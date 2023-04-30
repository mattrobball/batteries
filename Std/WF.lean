/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/

/-!
# Computable Acc.rec and WellFounded.fix

This file exports no public definitions / theorems, but by importing it the compiler will
be able to compile `Acc.rec` and functions that use it. For example:

Before:
```
-- failed to compile definition, consider marking it as 'noncomputable'
-- because it depends on 'WellFounded.fix', and it does not have executable code
def log2p1 : Nat → Nat :=
  WellFounded.fix Nat.lt_wfRel.2 fun n IH =>
    let m := n / 2
    if h : m < n then
      IH m h + 1
    else
      0
```

After:
```
import Std.WF

def log2p1 : Nat → Nat := -- works!
  WellFounded.fix Nat.lt_wfRel.2 fun n IH =>
    let m := n / 2
    if h : m < n then
      IH m h + 1
    else
      0

#eval log2p1 4   -- 3
```
-/

namespace Acc

private local instance wfRel {r : α → α → Prop} : WellFoundedRelation { val // Acc r val } where
  rel := InvImage r (·.1)
  wf  := ⟨fun ac => InvImage.accessible _ ac.2⟩

/-- A computable version of `Acc.rec`. Workaround until Lean has native support for this. -/
@[elab_as_elim] private def recC {motive : (a : α) → Acc r a → Sort v}
    (intro : (x : α) → (h : ∀ (y : α), r y x → Acc r y) →
     ((y : α) → (hr : r y x) → motive y (h y hr)) → motive x (intro x h))
    {a : α} (t : Acc r a) : motive a t :=
  intro a (fun x h => t.inv h) (fun y hr => recC intro (t.inv hr))
termination_by _ a h => Subtype.mk a h

private theorem recC_intro {motive : (a : α) → Acc r a → Sort v}
    (intro : (x : α) → (h : ∀ (y : α), r y x → Acc r y) →
     ((y : α) → (hr : r y x) → motive y (h y hr)) → motive x (intro x h))
    {a : α} (h : ∀ (y : α), r y a → Acc r y) :
    recC intro (Acc.intro _ h) = intro a h (fun y hr => recC intro (h y hr)) :=
  rfl

@[csimp] private theorem rec_eq_recC : @Acc.rec = @Acc.recC := by
  funext α r motive intro a t
  induction t with
  | intro x h ih =>
    dsimp only [recC_intro intro h]
    congr; funext y hr; exact ih _ hr

/-- A computable version of `Acc.ndrec`. Workaround until Lean has native support for this. -/
private abbrev ndrecC {C : α → Sort v}
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → (a : r y x) → C y) → C x)
    {a : α} (n : Acc r a) : C a :=
  n.recC m

@[csimp] private theorem ndrec_eq_ndrecC : @Acc.ndrec = @Acc.ndrecC := by
  funext α r motive intro a t
  rw [Acc.ndrec, rec_eq_recC, Acc.ndrecC]

/-- A computable version of `Acc.ndrecOn`. Workaround until Lean has native support for this. -/
private abbrev ndrecOnC {C : α → Sort v} {a : α} (n : Acc r a)
    (m : (x : α) → ((y : α) → r y x → Acc r y) → ((y : α) → r y x → C y) → C x) : C a :=
  n.recC m

@[csimp] private theorem ndrecOn_eq_ndrecOnC : @Acc.ndrecOn = @Acc.ndrecOnC := by
  funext α r motive intro a t
  rw [Acc.ndrecOn, rec_eq_recC, Acc.ndrecOnC]

end Acc

namespace WellFounded

/-- A computable version of `WellFounded.fixF`.
Workaround until Lean has native support for this. -/
private def fixFC {α : Sort u} {r : α → α → Prop}
    {C : α → Sort v} (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) (a : Acc r x) : C x := by
  induction a using Acc.recC with
  | intro x₁ _ ih => exact F x₁ ih

@[csimp] private theorem fixF_eq_fixFC : @fixF = @fixFC := by
  funext α r C F x a
  rw [fixF, Acc.rec_eq_recC, fixFC]

/-- A computable version of `fix`. Workaround until Lean has native support for this. -/
private def fixC {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (hwf : WellFounded r)
    (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  fixFC F x (apply hwf x)

@[csimp] private theorem fix_eq_fixC : @fix = @fixC := by
  funext α C r hwf F x
  rw [fix, fixF_eq_fixFC, fixC]

end WellFounded

/--
Helper function to define a well founded relation on the subtype of elements
which are `r`-accessible. Useful for `termination_by` clauses.
-/
def WellFoundedRelation.ofAcc {r : β → β → Prop} (F : α → {x : β // Acc r x}) :
    WellFoundedRelation α :=
  invImage F ⟨InvImage r (·.1), ⟨fun ⟨_, h⟩ => InvImage.accessible _ h⟩⟩

/--
Introduces a predicate `p` into an accessibility relation,
provided that it holds of the initial point.
-/
def Acc.restriction (p : α → Prop) {r : α → α → Prop}
    {a : α} (ac : Acc r a) (h : p a) : Acc (fun x y => p y → p x ∧ r x y) a := by
  induction ac with
  | intro x _ ih => exact ⟨_, fun y hr => ih y (hr h).2 (hr h).1⟩
