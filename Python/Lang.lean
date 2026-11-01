namespace Python

inductive AExpr where
  | int (value : Int)
  | var (name : String)
  | neg (expr : AExpr)
  | add (lhs rhs : AExpr)
  | sub (lhs rhs : AExpr)
  | mul (lhs rhs : AExpr)

inductive BExpr where
  | bool (value : Bool)
  | le (lhs rhs : AExpr)
  | ge (lhs rhs : AExpr)
  | lt (lhs rhs : AExpr)
  | gt (lhs rhs : AExpr)
  | eq (lhs rhs : AExpr)
  | ne (lhs rhs : AExpr)
  | and (lhs rhs : BExpr)
  | or (lhs rhs : BExpr)
  | not (expr : BExpr)

inductive Command where
  | pass
  | seq (first second : Command)
  | assign (name : String) (value : AExpr)
  | ite (cond : BExpr) (thenBranch elseBranch : Command)
  | whileDo (cond : BExpr) (body : Command)

structure Program where
  inputs : List String
  command : Command
  output : String

end Python
