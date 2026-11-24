module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGrFreeFiniteAndExactAt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exactAt_quot_of_shortExact {R : Type} [CommRing R]
    {S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)} (hS : S.ShortExact) (p : ℕ)
    (h₂ : S.X₂.ExactAt p) (h₁ : S.X₁.ExactAt (p + 1)) : S.X₃.ExactAt p := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h₁ h₂ ⊢
  exact (hS.homology_exact₃ p (p + 1) rfl).isZero_X₂ (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

theorem cubeComplex_grCube_exactAt_of_card_lt (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (q : ℕ) :
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, Fintype.card ι < p + q →
        (cubeComplex (grCube ι ℳ n)).ExactAt p := by
  induction q with
  | zero =>
    intro M _ _ _ _ ℳ _ _ _
    exact ⟨0, fun n _ p hp => (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_cubeComplex_homology _ hp)⟩
  | succ q ih =>
    intro M _ _ _ _ ℳ _ _ _
    obtain ⟨r, d, f, hf, hs⟩ := exists_graded_surjection (ι := ι) ℳ
    letI : Decomposition (grSub (grFree ι R d) (LinearMap.ker f)) :=
      grSubDecomposition _ hf.isHomogeneous_ker
    obtain ⟨a, ha⟩ := ih (LinearMap.ker f) (grSub (grFree ι R d) (LinearMap.ker f)) inferInstance
    obtain ⟨b, hb⟩ := (cubeComplex_grFree_finite_and_exactAt ι R r d).2
    refine ⟨max a b, fun n hn p hp => ?_⟩
    exact exactAt_quot_of_shortExact ((hf.shortExact_ker hs).cubeComplex_shortExact n) p
      (hb n (le_of_max_le_right hn) p) (ha n (le_of_max_le_left hn) (p + 1) (by omega))

theorem cubeComplex_grCube_exactAt_of_finite :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R]
      (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, (cubeComplex (grCube ι ℳ n)).ExactAt p := by
  intro ι _ _ R _ _ M _ _ _ _ ℳ _ _ hM
  obtain ⟨n₀, h⟩ := cubeComplex_grCube_exactAt_of_card_lt ι R (Fintype.card ι + 1) M ℳ hM
  exact ⟨n₀, fun n hn p => h n hn p (by omega)⟩

end GlobalTheory
