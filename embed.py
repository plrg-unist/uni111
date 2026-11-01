#! /usr/bin/env python3

"""Translate supported Python into a Lean Program, assertions, and a proof stub."""

import argparse
import ast
import json
import os
from pathlib import Path
import re
import tokenize
import tomllib
from typing import NoReturn


ARITHMETIC = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul"}
COMPARISONS = {
    ast.LtE: "le", ast.GtE: "ge", ast.Lt: "lt",
    ast.Gt: "gt", ast.Eq: "eq", ast.NotEq: "ne",
}
RESERVED = {"int", "input", "print"}


def fail(node: ast.AST, message: str) -> NoReturn:
    raise ValueError(f"line {node.lineno}: {message}")


def identifier(
    node: ast.Name, *, target: bool = False, initialized: set[str] | None = None
) -> str:
    if node.id in RESERVED or (target and node.id == "__debug__"):
        fail(node, f"unsupported identifier: {node.id}")
    if initialized is not None and node.id not in initialized:
        fail(node, f"potentially uninitialized variable: {node.id}")
    return json.dumps(node.id, ensure_ascii=False)


def is_call(node: ast.AST, name: str, arity: int) -> bool:
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name) and node.func.id == name
        and len(node.args) == arity and not node.keywords
    )


def aexpr(node: ast.AST, initialized: set[str]) -> str:
    match node:
        case ast.Constant(value=value) if type(value) is int:
            try:
                literal = str(value)
            except ValueError:
                # Large hexadecimal literals can exceed Python's decimal conversion limit.
                literal = hex(value)
            return f"(AExpr.int ({literal}))"
        case ast.Name():
            return f"(AExpr.var {identifier(node, initialized=initialized)})"
        case ast.UnaryOp(op=ast.USub(), operand=operand):
            return f"(AExpr.neg {aexpr(operand, initialized)})"
        case ast.BinOp(left=left, op=op, right=right) if type(op) in ARITHMETIC:
            lhs = aexpr(left, initialized)
            rhs = aexpr(right, initialized)
            return f"(AExpr.{ARITHMETIC[type(op)]} {lhs} {rhs})"
        case _:
            fail(node, f"unsupported arithmetic expression: {type(node).__name__}")


def bexpr(node: ast.AST, initialized: set[str]) -> str:
    match node:
        case ast.Constant(value=value) if type(value) is bool:
            return f"(BExpr.bool {str(value).lower()})"
        case ast.Compare(left=left, ops=[op], comparators=[right]) if type(op) in COMPARISONS:
            lhs = aexpr(left, initialized)
            rhs = aexpr(right, initialized)
            return f"(BExpr.{COMPARISONS[type(op)]} {lhs} {rhs})"
        case ast.UnaryOp(op=ast.Not(), operand=operand):
            return f"(BExpr.not {bexpr(operand, initialized)})"
        case ast.BoolOp(op=op, values=values) if isinstance(op, (ast.And, ast.Or)):
            constructor = "and" if isinstance(op, ast.And) else "or"
            result = bexpr(values[-1], initialized)
            for value in reversed(values[:-1]):
                result = f"(BExpr.{constructor} {bexpr(value, initialized)} {result})"
            return result
        case _:
            fail(node, f"unsupported Boolean expression: {type(node).__name__}")


def command(node: ast.stmt, initialized: set[str]) -> tuple[str, set[str]]:
    match node:
        case ast.Pass():
            return "Command.pass", initialized
        case ast.Assign(targets=[ast.Name() as target], value=value):
            name = identifier(target, target=True)
            value = aexpr(value, initialized)
            return f"(Command.assign {name} {value})", initialized | {target.id}
        case ast.AugAssign(target=ast.Name() as target, op=op, value=value) if type(op) in ARITHMETIC:
            name = identifier(target, target=True, initialized=initialized)
            rhs = aexpr(value, initialized)
            value = f"(AExpr.{ARITHMETIC[type(op)]} (AExpr.var {name}) {rhs})"
            return f"(Command.assign {name} {value})", initialized
        case ast.If(test=test, body=body, orelse=orelse):
            cond = bexpr(test, initialized)
            yes, after_yes = block(body, initialized)
            no, after_no = block(orelse, initialized)
            return f"(Command.ite {cond} {yes} {no})", after_yes & after_no
        case ast.While(test=test, body=body, orelse=[]):
            cond = bexpr(test, initialized)
            body, _ = block(body, initialized)
            return f"(Command.whileDo {cond} {body})", initialized
        case _:
            fail(node, f"unsupported command: {type(node).__name__}")


def block(statements: list[ast.stmt], initialized: set[str]) -> tuple[str, set[str]]:
    commands = []
    for statement in statements:
        translated, initialized = command(statement, initialized)
        commands.append(translated)
    if not commands:
        return "Command.pass", initialized
    result = commands[-1]
    for translated in reversed(commands[:-1]):
        result = f"(Command.seq {translated} {result})"
    return result, initialized


def input_target(node: ast.stmt) -> ast.Name | None:
    if (
        isinstance(node, ast.Assign) and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and is_call(node.value, "int", 1)
        and is_call(node.value.args[0], "input", 0)
    ):
        return node.targets[0]
    return None


def assertion(statements: list[ast.Assert], initialized: set[str]) -> str:
    conditions = []
    for statement in statements:
        if statement.msg is not None:
            fail(statement, "assertion messages are not supported")
        condition = bexpr(statement.test, initialized)
        conditions.append(f"(interpBExpr {condition} store = true)")
    if not conditions:
        return "fun _ => True"
    return "fun store => " + " ∧ ".join(conditions)


def program(module: ast.Module) -> str:
    if not module.body:
        raise ValueError("expected a final print(identifier)")
    last = module.body[-1]
    if not (
        isinstance(last, ast.Expr) and is_call(last.value, "print", 1)
        and isinstance(last.value.args[0], ast.Name)
    ):
        fail(last, "expected a final print(identifier)")
    inputs = []
    seen = set()
    index = 0
    while index < len(module.body) - 1:
        target = input_target(module.body[index])
        if target is None:
            break
        if target.id in seen:
            fail(target, f"duplicate input identifier: {target.id}")
        inputs.append(identifier(target, target=True))
        seen.add(target.id)
        index += 1

    pre_start = index
    while index < len(module.body) - 1 and isinstance(module.body[index], ast.Assert):
        index += 1
    post_start = len(module.body) - 1
    while post_start > index and isinstance(module.body[post_start - 1], ast.Assert):
        post_start -= 1
    if index == post_start:
        fail(last, "main command must not be empty; use pass")

    precondition = assertion(module.body[pre_start:index], seen)
    body, initialized = block(module.body[index:post_start], seen)
    postcondition = assertion(module.body[post_start:-1], initialized)
    output = identifier(last.value.args[0], initialized=initialized)
    # Constructor applications need more Lean elaboration depth than the source AST.
    rec_depth = 8 * sum(1 for _ in ast.walk(module))
    options = f"set_option maxRecDepth {rec_depth} in\n" if rec_depth > 1024 else ""
    return (
        "import Python\n\n"
        "open Python\n\n"
        f"{options}def program : Python.Program :=\n"
        f"  {{ inputs := [{', '.join(inputs)}]\n"
        f"    command := {body}\n"
        f"    output := {output} }}\n"
        f"\n{options}def precondition : Assertion :=\n  {precondition}\n"
        f"\n{options}def postcondition : Assertion :=\n  {postcondition}\n"
        "\ntheorem program_correct : HoareTriple precondition program.command postcondition := by\n"
        "  sorry\n"
    )


def update_lakefile(text: str, lean_file: Path) -> str:
    """Register the generated module without replacing existing Lake settings."""
    config = tomllib.loads(text)
    name = lean_file.stem
    target = json.dumps(name, ensure_ascii=False)
    if name not in config.get("defaultTargets", []):
        if "defaultTargets" in config:
            text, count = re.subn(
                r"""(?m)^([ \t]*(?:defaultTargets|"defaultTargets"|'defaultTargets')\s*=\s*\[)""",
                lambda match: match[1] + target + ", ",
                text, count=1,
            )
            if not count or name not in tomllib.loads(text).get("defaultTargets", []):
                raise ValueError("could not update defaultTargets in lakefile.toml")
        else:
            text = f"defaultTargets = [{target}]\n" + text

    if not any(lib.get("name") == name for lib in config.get("lean_lib", [])):
        directory = Path(os.path.relpath(
            lean_file.parent.resolve(), config.get("srcDir", ".")
        )).as_posix()
        text = (
            text.rstrip() + f"\n\n[[lean_lib]]\nname = {target}\n"
            f"srcDir = {json.dumps(directory, ensure_ascii=False)}\n"
        )
    return text


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("python_file", type=Path)
    args = parser.parse_args()
    try:
        with tokenize.open(args.python_file) as source:
            module = ast.parse(source.read(), filename=str(args.python_file))
        lean = program(module)
        name = args.python_file.stem
        lean_file = args.python_file.with_name(name[:1].upper() + name[1:] + ".lean")
        lakefile = Path("lakefile.toml")
        original = lakefile.read_text(encoding="utf-8")
        updated = update_lakefile(original, lean_file)
        lean_file.write_text(lean, encoding="utf-8")
        if updated != original:
            lakefile.write_text(updated, encoding="utf-8")
    except (OSError, RecursionError, SyntaxError, ValueError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
