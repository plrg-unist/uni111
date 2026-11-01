import Python.Lang

namespace Python

abbrev Store := String → Int

def Store.update (store : Store) (name : String) (value : Int) : Store :=
  fun key => if key = name then value else store key

def interpAExpr : AExpr → Store → Int
  | .int value, _ => value
  | .var name, store => store name
  | .neg expr, store => -interpAExpr expr store
  | .add lhs rhs, store => interpAExpr lhs store + interpAExpr rhs store
  | .sub lhs rhs, store => interpAExpr lhs store - interpAExpr rhs store
  | .mul lhs rhs, store => interpAExpr lhs store * interpAExpr rhs store

def interpBExpr : BExpr → Store → Bool
  | .bool value, _ => value
  | .le lhs rhs, store => decide (interpAExpr lhs store ≤ interpAExpr rhs store)
  | .ge lhs rhs, store => decide (interpAExpr lhs store ≥ interpAExpr rhs store)
  | .lt lhs rhs, store => decide (interpAExpr lhs store < interpAExpr rhs store)
  | .gt lhs rhs, store => decide (interpAExpr lhs store > interpAExpr rhs store)
  | .eq lhs rhs, store => decide (interpAExpr lhs store = interpAExpr rhs store)
  | .ne lhs rhs, store => decide (interpAExpr lhs store ≠ interpAExpr rhs store)
  | .and lhs rhs, store => interpBExpr lhs store && interpBExpr rhs store
  | .or lhs rhs, store => interpBExpr lhs store || interpBExpr rhs store
  | .not expr, store => !interpBExpr expr store

partial def interpCommand : Command → Store → Store
  | .pass, store => store
  | .seq first second, store => interpCommand second (interpCommand first store)
  | .assign name expr, store => store.update name (interpAExpr expr store)
  | .ite cond yes no, store =>
      if interpBExpr cond store then interpCommand yes store else interpCommand no store
  | .whileDo cond body, store =>
      if interpBExpr cond store then
        interpCommand (.whileDo cond body) (interpCommand body store)
      else store

private def bindInputs : List String → List Int → Store → Store
  | [], _, store => store
  | name :: names, [], store => bindInputs names [] (store.update name 0)
  | name :: names, value :: values, store =>
      bindInputs names values (store.update name value)

def interpProgram (program : Program) (inputs : List Int) : Int :=
  let store := bindInputs program.inputs inputs (fun _ => 0)
  interpCommand program.command store program.output

private def testStore : Store :=
  fun name => if name = "x" then 3 else if name = "y" then -2 else 0

/-- info: [-7, 3, 0, -3, 1, 5, -6] -/
#guard_msgs in
#eval [
  interpAExpr (.int (-7)) testStore,
  interpAExpr (.var "x") testStore,
  interpAExpr (.var "missing") testStore,
  interpAExpr (.neg (.var "x")) testStore,
  interpAExpr (.add (.var "x") (.var "y")) testStore,
  interpAExpr (.sub (.var "x") (.var "y")) testStore,
  interpAExpr (.mul (.var "x") (.var "y")) testStore]

/-- info: [true, false, true, true, false, true, true, false, true, false, true, false, true, false] -/
#guard_msgs in
#eval [
  interpBExpr (.le (.var "x") (.var "x")) testStore,
  interpBExpr (.le (.var "x") (.var "y")) testStore,
  interpBExpr (.le (.var "y") (.var "x")) testStore,
  interpBExpr (.ge (.var "y") (.var "y")) testStore,
  interpBExpr (.ge (.var "y") (.var "x")) testStore,
  interpBExpr (.ge (.var "x") (.var "y")) testStore,
  interpBExpr (.lt (.var "y") (.var "x")) testStore,
  interpBExpr (.lt (.var "x") (.var "x")) testStore,
  interpBExpr (.gt (.var "x") (.var "y")) testStore,
  interpBExpr (.gt (.var "x") (.var "x")) testStore,
  interpBExpr (.eq (.var "x") (.var "x")) testStore,
  interpBExpr (.eq (.var "x") (.var "y")) testStore,
  interpBExpr (.ne (.var "x") (.var "y")) testStore,
  interpBExpr (.ne (.var "x") (.var "x")) testStore]

/-- info: [true, false, true, false, false, false, true, true, true, false, true, false] -/
#guard_msgs in
#eval [
  interpBExpr (.bool true) testStore,
  interpBExpr (.bool false) testStore,
  interpBExpr (.and (.bool true) (.bool true)) testStore,
  interpBExpr (.and (.bool true) (.bool false)) testStore,
  interpBExpr (.and (.bool false) (.bool true)) testStore,
  interpBExpr (.and (.bool false) (.bool false)) testStore,
  interpBExpr (.or (.bool true) (.bool true)) testStore,
  interpBExpr (.or (.bool true) (.bool false)) testStore,
  interpBExpr (.or (.bool false) (.bool true)) testStore,
  interpBExpr (.or (.bool false) (.bool false)) testStore,
  interpBExpr (.not (.bool false)) testStore,
  interpBExpr (.not (.bool true)) testStore]

/-- info: [4, -2, -8, 0] -/
#guard_msgs in
#eval
  let command := Command.seq .pass
    (.seq (.assign "x" (.add (.var "x") (.int 1)))
      (.assign "z" (.mul (.var "x") (.var "y"))))
  let store := interpCommand command testStore
  [store "x", store "y", store "z", store "missing"]

/-- info: [2, 1] -/
#guard_msgs in
#eval
  let command := Command.ite (.lt (.var "x") (.int 0))
    (.assign "x" (.int 1)) (.assign "x" (.int 2))
  [(interpCommand command testStore) "x",
   (interpCommand command (testStore.update "x" (-3))) "x"]

private def sumProgram : Program := {
  inputs := ["n"]
  command := .seq (.assign "total" (.int 0))
    (.whileDo (.gt (.var "n") (.int 0))
      (.seq (.assign "total" (.add (.var "total") (.var "n")))
        (.assign "n" (.sub (.var "n") (.int 1)))))
  output := "total"
}

/-- info: [15, 0, 0] -/
#guard_msgs in
#eval
  let store := interpCommand sumProgram.command (Store.update (fun _ => 0) "n" 5)
  [store "total", store "n", store "missing"]

/-- info: [15, 0, 0, 15] -/
#guard_msgs in
#eval [interpProgram sumProgram [5], interpProgram sumProgram [],
  interpProgram sumProgram [-2], interpProgram sumProgram [5, 99]]

private def inputProgram : Program := {
  inputs := ["x", "y"]
  command := .assign "out" (.sub (.mul (.var "x") (.int 10)) (.var "y"))
  output := "out"
}

/-- info: [0, 70, 66, 66, 0] -/
#guard_msgs in
#eval [interpProgram inputProgram [], interpProgram inputProgram [7],
  interpProgram inputProgram [7, 4], interpProgram inputProgram [7, 4, 99],
  interpProgram { inputs := [], command := .pass, output := "missing" } [9]]

end Python
