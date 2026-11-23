module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.QuotSMulTop
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsPowSmulEqAddSubOneSmul
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulMemSpanOfFiniteQuotStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_graded_presentation_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢], (∀ i : ι, Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G)) → ∃ (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)) (ψ : ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin) →ₗ[MvPolynomial ι R] G), (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) ∧ IsGradedMap (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 ψ ∧ ∀ i : ι, (∀ y, ψ y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) ∧ (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ) := by
  intro ι _ _ R _ G _ _ _ _ 𝒢 _ _ hG
  obtain ⟨a, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 fun i =>
    GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R G 𝒢 i (haveI := hG i; inferInstance)
  set φ := Fintype.linearCombination (MvPolynomial ι R) g with hφdef
  have hφ : IsGradedMap (grFree ι R d) 𝒢 φ := isGradedMap_linearCombination 𝒢 hg
  have hsat' : ∀ (i : ι) (z : G), ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ := by
    intro i z
    rw [hφdef, Fintype.range_linearCombination]
    exact hsat i z
  let _ : Decomposition (grSub (grFree ι R d) (LinearMap.ker φ)) :=
    grSubDecomposition _ hφ.isHomogeneous_ker
  obtain ⟨b, e, κ, hκ, hksat⟩ := exists_homogeneous_family_saturating ι R (LinearMap.ker φ)
    (grSub (grFree ι R d) (LinearMap.ker φ)) fun i =>
      GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R _ (grSub (grFree ι R d) (LinearMap.ker φ)) i
        (GlobalTheory.finite_quotSMulTop_ker_of_graded ι R _ (grFree ι R d) G 𝒢 φ i hφ inferInstance (hsat' i) (hG i))
  let Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R) := Matrix.of fun l j => (κ j).1 l
  have hrange : LinearMap.range Φ.mulVecLin =
      (Submodule.span (MvPolynomial ι R) (Set.range κ)).map (LinearMap.ker φ).subtype := by
    rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : LinearMap.range Φ.mulVecLin ≤ LinearMap.ker φ := by
    rw [hrange]
    exact Submodule.map_subtype_le _ _
  refine ⟨a, b, d, e, Φ, Submodule.liftQ _ φ hle, fun l j => ?_, hφ.liftQ _ hle,
    fun i => ⟨fun y hy => ?_, fun z => ?_⟩⟩
  · have := mem_grPi.1 (mem_grSub.1 (hκ j)) l
    rw [sub_eq_add_neg]
    exact this
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨k, hk⟩ := hksat i ⟨x, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hrange]
    exact ⟨_, hk, rfl⟩
  · rw [Submodule.range_liftQ]
    exact hsat' i z

end GlobalTheory
