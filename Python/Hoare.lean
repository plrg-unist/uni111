import Python.Semantics

/-!
Partial-correctness rules following Software Foundations, Hoare Logic, Part I:
https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html
-/

namespace Python

abbrev Assertion := Store → Prop

/-- Every terminating execution from `pre` ends in a store satisfying `post`. -/
def HoareTriple (pre : Assertion) (command : Command) (post : Assertion) : Prop :=
  ∀ ⦃store final : Store⦄, pre store → InterpCommand store command final → post final

/-- Substitute an expression evaluated in the original store into an assertion. -/
def Assertion.subst (post : Assertion) (name : String) (expr : AExpr) : Assertion :=
  fun store => post (store.update name (interpAExpr expr store))

theorem hoare_pass (P : Assertion) : HoareTriple P .pass P := by
  intro store final hp hcommand
  cases hcommand
  exact hp

theorem hoare_assign (Q : Assertion) (name : String) (expr : AExpr) :
    HoareTriple (Q.subst name expr) (.assign name expr) Q := by
  intro store final hq hcommand
  cases hcommand with
  | assign hvalue =>
      simpa [Assertion.subst, interpAExpr_complete hvalue] using hq

theorem hoare_seq {P Q R : Assertion} {first second : Command}
    (hfirst : HoareTriple P first Q) (hsecond : HoareTriple Q second R) :
    HoareTriple P (.seq first second) R := by
  intro store final hp hcommand
  cases hcommand with
  | seq hfirstEval hsecondEval => exact hsecond (hfirst hp hfirstEval) hsecondEval

theorem hoare_ite {P Q : Assertion} {cond : BExpr} {yes no : Command}
    (hyes : HoareTriple (fun store => P store ∧ interpBExpr cond store = true) yes Q)
    (hno : HoareTriple (fun store => P store ∧ interpBExpr cond store = false) no Q) :
    HoareTriple P (.ite cond yes no) Q := by
  intro store final hp hcommand
  cases hcommand with
  | ite_true hcond hbody => exact hyes ⟨hp, interpBExpr_complete hcond⟩ hbody
  | ite_false hcond hbody => exact hno ⟨hp, interpBExpr_complete hcond⟩ hbody

theorem hoare_while {invariant : Assertion} {cond : BExpr} {body : Command}
    (hbody : HoareTriple
      (fun store => invariant store ∧ interpBExpr cond store = true) body invariant) :
    HoareTriple invariant (.whileDo cond body)
      (fun store => invariant store ∧ interpBExpr cond store = false) := by
  intro store final hinvariant hcommand
  generalize hloop : Command.whileDo cond body = command at hcommand
  revert hinvariant hloop
  induction hcommand with
  | pass | seq | assign | ite_true | ite_false =>
      intro _ hloop
      cases hloop
  | while_false hcond =>
      intro hinvariant hloop
      cases hloop
      exact ⟨hinvariant, interpBExpr_complete hcond⟩
  | while_true hcond hbodyEval hrest _ ihrest =>
      intro hinvariant hloop
      cases hloop
      exact ihrest (hbody ⟨hinvariant, interpBExpr_complete hcond⟩ hbodyEval) rfl

theorem hoare_consequence {P P' Q Q' : Assertion} {command : Command}
    (h : HoareTriple P' command Q')
    (hpre : ∀ store, P store → P' store) (hpost : ∀ store, Q' store → Q store) :
    HoareTriple P command Q := by
  intro store final hp hcommand
  exact hpost final (h (hpre store hp) hcommand)

theorem hoare_consequence_pre {P P' Q : Assertion} {command : Command}
    (h : HoareTriple P' command Q) (hpre : ∀ store, P store → P' store) :
    HoareTriple P command Q :=
  hoare_consequence h hpre (fun _ hq => hq)

theorem hoare_consequence_post {P Q Q' : Assertion} {command : Command}
    (h : HoareTriple P command Q') (hpost : ∀ store, Q' store → Q store) :
    HoareTriple P command Q :=
  hoare_consequence h (fun _ hp => hp) hpost

theorem hoare_post_true {P Q : Assertion} {command : Command}
    (hq : ∀ store, Q store) : HoareTriple P command Q := by
  intro store final _ _
  exact hq final

theorem hoare_pre_false {P Q : Assertion} {command : Command}
    (hp : ∀ store, ¬P store) : HoareTriple P command Q := by
  intro store final hpre _
  exact (hp store hpre).elim

end Python
