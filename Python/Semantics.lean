import Python.Interp

namespace Python

inductive InterpAExpr (store : Store) : AExpr → Int → Prop where
  | int (value : Int) : InterpAExpr store (.int value) value
  | var (name : String) : InterpAExpr store (.var name) (store name)
  | neg {expr : AExpr} {value : Int}
      (h : InterpAExpr store expr value) :
      InterpAExpr store (.neg expr) (-value)
  | add {lhs rhs : AExpr} {left right : Int}
      (hl : InterpAExpr store lhs left) (hr : InterpAExpr store rhs right) :
      InterpAExpr store (.add lhs rhs) (left + right)
  | sub {lhs rhs : AExpr} {left right : Int}
      (hl : InterpAExpr store lhs left) (hr : InterpAExpr store rhs right) :
      InterpAExpr store (.sub lhs rhs) (left - right)
  | mul {lhs rhs : AExpr} {left right : Int}
      (hl : InterpAExpr store lhs left) (hr : InterpAExpr store rhs right) :
      InterpAExpr store (.mul lhs rhs) (left * right)

inductive InterpBExpr (store : Store) : BExpr → Bool → Prop where
  | bool (value : Bool) : InterpBExpr store (.bool value) value
  | le {lhs rhs : AExpr} {left right : Int}
      (hl : InterpAExpr store lhs left) (hr : InterpAExpr store rhs right) :
      InterpBExpr store (.le lhs rhs) (decide (left ≤ right))
  | ge {lhs rhs : AExpr} {left right : Int}
      (hl : InterpAExpr store lhs left) (hr : InterpAExpr store rhs right) :
      InterpBExpr store (.ge lhs rhs) (decide (left ≥ right))
  | lt {lhs rhs : AExpr} {left right : Int}
      (hl : InterpAExpr store lhs left) (hr : InterpAExpr store rhs right) :
      InterpBExpr store (.lt lhs rhs) (decide (left < right))
  | gt {lhs rhs : AExpr} {left right : Int}
      (hl : InterpAExpr store lhs left) (hr : InterpAExpr store rhs right) :
      InterpBExpr store (.gt lhs rhs) (decide (left > right))
  | eq {lhs rhs : AExpr} {left right : Int}
      (hl : InterpAExpr store lhs left) (hr : InterpAExpr store rhs right) :
      InterpBExpr store (.eq lhs rhs) (decide (left = right))
  | ne {lhs rhs : AExpr} {left right : Int}
      (hl : InterpAExpr store lhs left) (hr : InterpAExpr store rhs right) :
      InterpBExpr store (.ne lhs rhs) (decide (left ≠ right))
  | and {lhs rhs : BExpr} {left right : Bool}
      (hl : InterpBExpr store lhs left) (hr : InterpBExpr store rhs right) :
      InterpBExpr store (.and lhs rhs) (left && right)
  | or {lhs rhs : BExpr} {left right : Bool}
      (hl : InterpBExpr store lhs left) (hr : InterpBExpr store rhs right) :
      InterpBExpr store (.or lhs rhs) (left || right)
  | not {expr : BExpr} {value : Bool}
      (h : InterpBExpr store expr value) :
      InterpBExpr store (.not expr) (!value)

inductive InterpCommand : Store → Command → Store → Prop where
  | pass (store : Store) : InterpCommand store .pass store
  | seq {store middle final : Store} {first second : Command}
      (hfirst : InterpCommand store first middle)
      (hsecond : InterpCommand middle second final) :
      InterpCommand store (.seq first second) final
  | assign {store : Store} {name : String} {expr : AExpr} {value : Int}
      (h : InterpAExpr store expr value) :
      InterpCommand store (.assign name expr) (store.update name value)
  | ite_true {store final : Store} {cond : BExpr} {yes no : Command}
      (hcond : InterpBExpr store cond true) (hbody : InterpCommand store yes final) :
      InterpCommand store (.ite cond yes no) final
  | ite_false {store final : Store} {cond : BExpr} {yes no : Command}
      (hcond : InterpBExpr store cond false) (hbody : InterpCommand store no final) :
      InterpCommand store (.ite cond yes no) final
  | while_false {store : Store} {cond : BExpr} {body : Command}
      (hcond : InterpBExpr store cond false) :
      InterpCommand store (.whileDo cond body) store
  | while_true {store middle final : Store} {cond : BExpr} {body : Command}
      (hcond : InterpBExpr store cond true)
      (hbody : InterpCommand store body middle)
      (hrest : InterpCommand middle (.whileDo cond body) final) :
      InterpCommand store (.whileDo cond body) final

theorem interpAExpr_sound (expr : AExpr) (store : Store) :
    InterpAExpr store expr (interpAExpr expr store) := by
  induction expr with
  | int value => exact .int value
  | var name => exact .var name
  | neg expr ih => exact .neg ih
  | add lhs rhs ihl ihr => exact .add ihl ihr
  | sub lhs rhs ihl ihr => exact .sub ihl ihr
  | mul lhs rhs ihl ihr => exact .mul ihl ihr

theorem interpAExpr_complete {store : Store} {expr : AExpr} {value : Int}
    (h : InterpAExpr store expr value) : interpAExpr expr store = value := by
  induction h <;> simp_all [interpAExpr]

theorem interpAExpr_iff {store : Store} {expr : AExpr} {value : Int} :
    InterpAExpr store expr value ↔ interpAExpr expr store = value := by
  constructor
  · exact interpAExpr_complete
  · intro h
    simpa [h] using interpAExpr_sound expr store

theorem interpBExpr_sound (expr : BExpr) (store : Store) :
    InterpBExpr store expr (interpBExpr expr store) := by
  induction expr with
  | bool value => exact .bool value
  | le lhs rhs => exact .le (interpAExpr_sound lhs store) (interpAExpr_sound rhs store)
  | ge lhs rhs => exact .ge (interpAExpr_sound lhs store) (interpAExpr_sound rhs store)
  | lt lhs rhs => exact .lt (interpAExpr_sound lhs store) (interpAExpr_sound rhs store)
  | gt lhs rhs => exact .gt (interpAExpr_sound lhs store) (interpAExpr_sound rhs store)
  | eq lhs rhs => exact .eq (interpAExpr_sound lhs store) (interpAExpr_sound rhs store)
  | ne lhs rhs => exact .ne (interpAExpr_sound lhs store) (interpAExpr_sound rhs store)
  | and lhs rhs ihl ihr => exact .and ihl ihr
  | or lhs rhs ihl ihr => exact .or ihl ihr
  | not expr ih => exact .not ih

theorem interpBExpr_complete {store : Store} {expr : BExpr} {value : Bool}
    (h : InterpBExpr store expr value) : interpBExpr expr store = value := by
  induction h with
  | bool value => rfl
  | le hl hr => simp [interpBExpr, interpAExpr_complete hl, interpAExpr_complete hr]
  | ge hl hr => simp [interpBExpr, interpAExpr_complete hl, interpAExpr_complete hr]
  | lt hl hr => simp [interpBExpr, interpAExpr_complete hl, interpAExpr_complete hr]
  | gt hl hr => simp [interpBExpr, interpAExpr_complete hl, interpAExpr_complete hr]
  | eq hl hr => simp [interpBExpr, interpAExpr_complete hl, interpAExpr_complete hr]
  | ne hl hr => simp [interpBExpr, interpAExpr_complete hl, interpAExpr_complete hr]
  | and hl hr ihl ihr => simp [interpBExpr, ihl, ihr]
  | or hl hr ihl ihr => simp [interpBExpr, ihl, ihr]
  | not h ih => simp [interpBExpr, ih]

theorem interpBExpr_iff {store : Store} {expr : BExpr} {value : Bool} :
    InterpBExpr store expr value ↔ interpBExpr expr store = value := by
  constructor
  · exact interpBExpr_complete
  · intro h
    simpa [h] using interpBExpr_sound expr store

theorem increment_example (store : Store) :
    InterpCommand store (.assign "x" (.add (.var "x") (.int 1)))
      (store.update "x" (store "x" + 1)) :=
  .assign (.add (.var "x") (.int 1))

theorem assign_then_copy_example (store : Store) :
    InterpCommand store (.seq (.assign "x" (.int 2)) (.assign "y" (.var "x")))
      ((store.update "x" 2).update "y" 2) := by
  apply InterpCommand.seq (middle := store.update "x" 2)
  · exact .assign (.int 2)
  · apply InterpCommand.assign
    simpa [Store.update] using (InterpAExpr.var (store := store.update "x" 2) "x")

theorem conditional_true_example (store : Store) :
    InterpCommand store
      (.ite (.lt (.int 1) (.int 2)) (.assign "x" (.int 3)) (.assign "x" (.int 4)))
      (store.update "x" 3) :=
  .ite_true (.lt (.int 1) (.int 2)) (.assign (.int 3))

theorem conditional_false_example (store : Store) :
    InterpCommand store
      (.ite (.bool false) (.assign "x" (.int 3)) (.assign "x" (.int 4)))
      (store.update "x" 4) :=
  .ite_false (.bool false) (.assign (.int 4))

theorem while_clear_example :
    InterpCommand (fun _ => 1)
      (.whileDo (.gt (.var "x") (.int 0)) (.assign "x" (.int 0)))
      (Store.update (fun _ => 1) "x" 0) := by
  apply InterpCommand.while_true (middle := Store.update (fun _ => 1) "x" 0)
  · exact .gt (.var "x") (.int 0)
  · exact .assign (.int 0)
  · exact .while_false (.gt (.var "x") (.int 0))

end Python
