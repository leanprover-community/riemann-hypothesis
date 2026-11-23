module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.LBDescent

theorem exists_finite_subextension_cls (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (B X : Scheme.{0}) (pB : B ⟶ Sp K) [QuasiCompact pB]
    [QuasiSeparated pB] (p : X ⟶ Sp Ω) (φ : X ⟶ B)
    (hX : IsPullback φ p pB (spMap (algebraMap K Ω))) (L : LB X) (hL : L.IsLB) :
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp F) (φ₁ : X₁ ⟶ B),
        IsPullback φ₁ p₁ pB (spMap (algebraMap K F)) →
        ∀ j : X ⟶ X₁, j ≫ φ₁ = φ → j ≫ p₁ = p ≫ spMap (algebraMap F Ω) →
          ∃ x : CechPic.Pic X₁, CechPic.pull j x = CechPic.cls L hL := by
  obtain ⟨R, M, ρ, ⟨T, hT⟩, hM, h1, h2, hI⟩ := exists_fg_lb pB p φ hX L hL
  let F : IntermediateField K Ω := IntermediateField.adjoin K (T : Set Ω)
  have hle : R ≤ F.toSubalgebra := by
    rw [← hT]
    exact IntermediateField.algebra_adjoin_le_adjoin K _
  refine ⟨F, IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral), ?_⟩
  intro X₁ p₁ φ₁ hX₁ j hj1 hj2
  let ι : R →+* F := (Subalgebra.inclusion hle).toRingHom
  have e1 : spMap ι ≫ spMap (algebraMap K R) = spMap (algebraMap K F) := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have e2 : spMap (algebraMap F Ω) ≫ spMap ι = spMap R.val.toRingHom := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  let q : X₁ ⟶ Limits.pullback pB (spMap (algebraMap K R)) :=
    Limits.pullback.lift φ₁ (p₁ ≫ spMap ι) (by rw [Category.assoc, e1, hX₁.w])
  have hq : j ≫ q = ρ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, hj1, h1]
    · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, hj2, Category.assoc, e2, h2]
  refine ⟨CechPic.pull q (CechPic.cls M hM), ?_⟩
  rw [← CechPic.pull_comp, hq, ← CechPic.cls_pull hM ρ (pull_isLB hM ρ), eq_comm, CechPic.cls_eq_iff]
  exact hI

end GlobalTheory.LBDescent
