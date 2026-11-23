module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAndMean
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.PlaceWeights


open Classical in
theorem sum_ind_algHom (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (v : InfinitePlace K) :
    (∑ f : K →ₐ[ℚ] ℂ, (if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)) = 2 := by
  have h1 : (∑ f : K →ₐ[ℚ] ℂ, (if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0))
      = ∑ f : K →+* ℂ, (if InfinitePlace.mk f = v then (1 : ℝ) else 0) :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)) _ _ (fun _ => rfl)).symm
  rw [h1, Finset.sum_boole, InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq]
  norm_num

theorem finrank_eq_two_mul (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * Fintype.card (InfinitePlace K) := by
  rw [← InfinitePlace.sum_mult_eq]
  simp [IsTotallyComplex.mult_eq, mul_comm]


open Classical in
theorem sum_ind_placeUnder (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ₀ : K →+* ℂ)
    (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (h : ∀ k, σ₀ k ∈ M) (v : InfinitePlace K) :
    (∑ ρ : M →ₐ[ℚ] ℂ, (if placeUnder σ₀ h ρ = v then (1 : ℝ) else 0)) / (Module.finrank ℚ M : ℝ)
      = 1 / (Fintype.card (InfinitePlace K) : ℝ) := by
  let _ : Algebra K M := (σ₀.codRestrict M h).toAlgebra
  have : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  have key := (GlobalTheory.EmbeddingMean.tower (K := ℚ) (A := K) (B := M) (C := ℂ)).2
    (fun f => if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)
  rw [sum_ind_algHom, finrank_eq_two_mul K] at key
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · push_cast
    field_simp

theorem exists_weights : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (h : ∀ k, σ₀ k ∈ M), ∃ wt : InfinitePlace K → (M →ₐ[ℚ] ℂ) → ℝ, (∀ v ρ, 0 ≤ wt v ρ) ∧ (∀ v, ∑ ρ, wt v ρ = 1) ∧ (∀ v ρ, wt v ρ ≠ 0 → placeUnder σ₀ h ρ = v) ∧ ∀ ρ, (∑ v, wt v ρ) / (Fintype.card (InfinitePlace K) : ℝ) = 1 / (Module.finrank ℚ M : ℝ) := by
  classical
  intro K _ _ _ σ₀ M _ h
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  refine ⟨fun v ρ => (if placeUnder σ₀ h ρ = v then (1 : ℝ) else 0) *
    ((Fintype.card (InfinitePlace K) : ℝ) / (Module.finrank ℚ M : ℝ)), ?_, ?_, ?_, ?_⟩
  · intro v ρ
    refine mul_nonneg ?_ (by positivity)
    split_ifs <;> norm_num
  · intro v
    have key := sum_ind_placeUnder K σ₀ M h v
    rw [← Finset.sum_mul]
    rw [div_eq_div_iff hM hc] at key
    rw [← mul_div_assoc, div_eq_one_iff_eq hM]
    convert key using 1
    ring
  · intro v ρ hw
    by_contra hne
    exact hw (by simp [hne])
  · intro ρ
    rw [← Finset.sum_mul, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    field_simp

end GlobalTheory.PlaceWeights
