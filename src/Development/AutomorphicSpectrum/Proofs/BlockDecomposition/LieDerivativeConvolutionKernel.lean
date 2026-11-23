module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.LieConv

theorem mMap_surjective (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Function.Surjective (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a) := fun X =>
  ⟨(fun i j => ((0, fun w => X i j w.1) : mixedEmbedding.mixedSpace E) :
    Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)), rfl⟩

theorem exists_kernel_basis (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ)
    (j : Fin (CuspidalSpectrum.archDim E a)) :
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a,
      (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (CuspidalSpectrum.archBasis E a j)) φ).1 g =
        ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  obtain ⟨D, hD, hDc, h⟩ := GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ) hφ ν 1
    (fun _ => j)
  refine ⟨D, hD, hDc, fun g => ?_⟩
  rw [← h g, CuspidalSpectrum.uAction_uJ_succ]
  have e := GlobalTheory.CompanionTheory.HCRep.smL_liB (E := E) (a := a) (CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis E a j)) φ
  have e2 := congrArg (fun ψ : AutomorphicForm.archSmooth E a => ψ.1 g) e
  have e0 : ∀ ψ : AutomorphicForm.archSmooth E a,
      AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) 0 (Fin.tail fun _ => j)) ψ = ψ := fun ψ => by
    rw [CuspidalSpectrum.uJ, map_one]
    rfl
  rw [e0]
  exact e2

theorem hasCompactSupport_sum {G ι : Type*} [TopologicalSpace G] (s : Finset ι) (c : ι → ℂ) (D : ι → G → ℂ)
    (h : ∀ j, HasCompactSupport (D j)) : HasCompactSupport fun y => ∑ j ∈ s, c j * D j y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((h j).mul_left (f := fun _ => c j)).add ih

theorem lie_eq_conv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a), IsAutForm φ → ∀ X : Lie E a, ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a, (lie E a X φ).1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  intro E _ _ _ a _ _ ν _ φ hφ X
  obtain ⟨Y, rfl⟩ := mMap_surjective E a X
  choose D hD hDc hconv using exists_kernel_basis E a ν φ hφ
  set b := CuspidalSpectrum.archBasis E a with hb
  set c : Fin (CuspidalSpectrum.archDim E a) → ℂ := fun j => ((b.repr Y j : ℝ) : ℂ) with hc
  refine ⟨fun y => ∑ j, c j * D j y, continuous_finsetSum _ fun j _ => continuous_const.mul (hD j),
    hasCompactSupport_sum _ c D hDc, fun g => ?_⟩
  have hf : Continuous fun y => φ.1 (g * AutomorphicForm.infEmb E a y) :=
    IsExpLieAlgebra.continuous_of_isSmoothFun (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ g)
  have hint : ∀ j, Integrable (fun y => φ.1 (g * AutomorphicForm.infEmb E a y) * D j y) ν := fun j =>
    (hf.mul (hD j)).integrable_of_hasCompactSupport ((hDc j).mul_left)
  have hY : (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a Y) φ).1 g =
      ∑ j, c j * (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (b j)) φ).1 g := by
    conv_lhs => rw [← b.sum_repr Y]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
    Complex.real_smul, hc]
  rw [hY]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hconv j g, ← integral_const_mul]
    congr 1
    funext y
    ring
  · exact ((hint j).const_mul (c j)).congr (Filter.Eventually.of_forall fun y => by ring)

end GlobalTheory.CompanionTheory.LieConv
