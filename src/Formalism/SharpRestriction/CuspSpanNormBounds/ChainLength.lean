module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

section LocalTheory

open Formalism.MainNotions.S.Loc MeasureTheory ComplexConjugate

end LocalTheory

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ U : ∀ p : PlF D, AddSubgroup (D.s.atP p).Ep, (∀ p, IsOpen (U p : Set (D.s.atP p).Ep)) →
    {p | (U p : Set (D.s.atP p).Ep) ≠ ((D.s.atP p).O : Set (D.s.atP p).Ep)}.Finite →
    ∀ x : ∀ p, (D.s.atP p).Ep, {p | x p ∉ (D.s.atP p).O}.Finite →
      ∃ t : D.host.E, ∀ p, (D.s.atP p).ιE t - x p ∈ U p

def adm7 (D : Formalism.BasicNotions.D7) : Prop :=
  (∀ M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep, (∀ p, (M p).OK) →
    ∀ x : D.host.E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((D.s.atP p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((D.s.atP p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))))

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}

end Family

end Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum
