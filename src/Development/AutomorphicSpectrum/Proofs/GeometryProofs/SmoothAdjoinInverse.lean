module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem isLocalizationAway_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω}
    (hg : g ∈ A) (h0 : g ≠ 0) :
    letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
    IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := by
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A (invAdj A g) a : invAdj A g) : Ω) = a := fun _ => rfl
  refine IsLocalization.Away.mk (⟨g, hg⟩ : A) ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨g⁻¹, inv_mem_invAdj A g⟩ : invAdj A g) (Subtype.ext ?_)
    simp [hmap, h0]
  · intro s
    obtain ⟨k, hk⟩ := exists_mul_pow_mem hg h0 s.2
    refine ⟨k, ⟨_, hk⟩, Subtype.ext ?_⟩
    simp [hmap]
  · intro a b hab
    have hab' : a = b := Subtype.ext (by simpa [hmap] using congrArg Subtype.val hab)
    exact ⟨0, by rw [hab']⟩

theorem smooth_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 →
    Algebra.Smooth ℚ A → Algebra.Smooth ℚ (invAdj A g) := by
  intro Ω _ _ A g hg h0 hA
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ A (invAdj A g) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := isLocalizationAway_invAdj hg h0
  haveI : Algebra.Smooth A (invAdj A g) := Algebra.Smooth.of_isLocalization_Away (⟨g, hg⟩ : A)
  exact Algebra.Smooth.comp ℚ A (invAdj A g)

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
