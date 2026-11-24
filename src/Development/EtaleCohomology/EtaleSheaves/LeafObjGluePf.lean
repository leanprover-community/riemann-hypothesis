module

public import Development.EtaleCohomology.EtaleSheaves.LeafObjFPPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjGluePf

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

def DescAt (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D), FP q ∧ IsPullback v f q (toR R)

theorem toR_eq {R R' : Subalgebra k Ω} (h : R ≤ R') : toR R' ≫ incl h = toR R := by
  simp only [toR, incl]
  rw [← Spec.map_comp]
  rfl

theorem fp_snd {X Y Z : Scheme.{0}} (q : X ⟶ Z) (g : Y ⟶ Z) (hq : FP q) : FP (pullback.snd q g) := by
  obtain ⟨h1, h2, h3⟩ := hq
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem descAt_mono {R R' : Subalgebra k Ω} (h : R ≤ R') {X : Scheme.{0}} {f : X ⟶ Sp Ω}
    (hd : DescAt R f) : DescAt R' f := by
  obtain ⟨D, q, v, hq, hp⟩ := hd
  refine ⟨pullback q (incl h), pullback.snd q (incl h),
    pullback.lift v (f ≫ toR R') (by rw [hp.w, Category.assoc, toR_eq]), fp_snd _ _ hq, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (v₁₃ := q) (h₂₂ := incl h) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback q (incl h))
  rw [pullback.lift_fst, toR_eq]
  exact hp

def GlueData (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) (U V : X.Opens) : Prop :=
  ∃ (DU DV DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qV : DV ⟶ Sp R) (qW : DW ⟶ Sp R)
    (vU : U.toScheme ⟶ DU) (vV : V.toScheme ⟶ DV) (vW : (U ⊓ V).toScheme ⟶ DW) (φU : DW ⟶ DU) (φV : DW ⟶ DV),
    FP qU ∧ FP qV ∧ FP qW ∧ IsOpenImmersion φU ∧ IsOpenImmersion φV ∧ φU ≫ qU = qW ∧ φV ≫ qV = qW ∧
    IsPullback vU (U.ι ≫ f) qU (toR R) ∧ IsPullback vV (V.ι ≫ f) qV (toR R) ∧
    IsPullback vW ((U ⊓ V).ι ≫ f) qW (toR R) ∧
    vW ≫ φU = X.homOfLE inf_le_left ≫ vU ∧ vW ≫ φV = X.homOfLE inf_le_right ≫ vV

def LeafInclDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens) (R : Subalgebra k Ω), R.FG →
    DescAt R (U.ι ≫ f) → DescAt R (V.ι ≫ f) → DescAt R ((U ⊓ V).ι ≫ f) →
    ∃ R' : Subalgebra k Ω, R ≤ R' ∧ R'.FG ∧ GlueData R' f U V

def LeafGlueTwo : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω) (U V : X.Opens) (R : Subalgebra k Ω), U ⊔ V = ⊤ → GlueData R f U V → DescAt R f

theorem LeafObjGlue_of (hI : LeafInclDescend) (hG : LeafGlueTwo) : LeafObjGlue := by
  intro k _ Ω _ _ X f hf U V hUV ⟨R1, h1, d1⟩ ⟨R2, h2, d2⟩ ⟨R3, h3, d3⟩
  obtain ⟨R', -, hR', g⟩ := hI k Ω f hf U V (R1 ⊔ R2 ⊔ R3) ((h1.sup h2).sup h3)
    (descAt_mono (le_sup_left.trans le_sup_left) d1) (descAt_mono (le_sup_right.trans le_sup_left) d2)
    (descAt_mono le_sup_right d3)
  exact ⟨R', hR', hG k Ω f U V R' hUV g⟩

end LateralTheory.E.LeafObjGluePf
end
