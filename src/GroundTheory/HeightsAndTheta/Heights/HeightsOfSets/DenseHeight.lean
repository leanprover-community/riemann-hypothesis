module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Points
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem finitePlace_le_one_of_isIntegral {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    {x : K} (hx : IsIntegral ℤ x) : v x ≤ 1 := by
  let y : 𝓞 K := ⟨x, hx⟩
  have h := FinitePlace.norm_le_one K v.maximalIdeal y
  rw [FinitePlace.norm_embedding_eq] at h
  exact h

theorem finsum_log_finitePlace_natCast {K : Type*} [Field K] [NumberField K] {δ : ℕ} (hδ : 0 < δ) :
    ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = -(Module.finrank ℚ K * Real.log δ) := by
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'
  have hfin : (Function.mulSupport fun w : FinitePlace K ↦ w (δ : K)).Finite :=
    FinitePlace.hasFiniteMulSupport hne
  have hprod := FinitePlace.prod_eq_inv_abs_norm hne
  rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _
    (fun x hx ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hx))] at hprod
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [← Real.log_prod (fun v _ ↦ (map_ne_zero _).mpr hne), hprod]
    have : Algebra.norm ℚ ((δ : ℕ) : K) = (δ : ℚ) ^ (Module.finrank ℚ K) := by
      have := Algebra.norm_algebraMap (S := K) (δ : ℚ)
      simpa using this
    rw [this]
    push_cast
    rw [abs_pow, Nat.abs_cast, Real.log_inv, Real.log_pow]
  · intro v hv
    have h1' : v (δ : K) ≠ 1 := fun h ↦ hv (by show Real.log (v (δ : K)) = 0; rw [h, Real.log_one])
    exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr h1')

theorem vectorL2Norm_le_sqrt_card_mul {m : ℕ} (w : Fin m → ℂ) {R : ℝ} (hR : 0 ≤ R) (hw : ∀ i, ‖w i‖ ≤ R) :
    l2Norm w ≤ Real.sqrt m * R := by
  rw [l2Norm, ← Real.sqrt_sq hR, ← Real.sqrt_mul (Nat.cast_nonneg m)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin m, R ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
    _ = m * R ^ 2 := by simp

theorem height_standard_le (z : Cone n (AlgebraicClosure ℚ)) (hz : BlockNonzero z) {δ : ℕ}
    (hδ : 0 < δ) {R : ℝ} (hR : 0 < R)
    (hint : ∀ k i, IsIntegral ℤ ((δ : AlgebraicClosure ℚ) * z k i))
    (harch : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) k i, ‖σ (z k i)‖ ≤ R) :
    height (HermLine.standard (n := n)) z ≤
      ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
  set K := coordField z
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd_def
  have hd : 0 < d := by rw [hd_def]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'

  have hloc : ∀ (v : FinitePlace K) (k : ι),
      Real.log (⨆ i, v (coordVec z k i)) ≤ -Real.log (v (δ : K)) := by
    intro v k
    have hδv : 0 < v (δ : K) := FinitePlace.pos_iff.mpr hne
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
    have hi0' : coordVec z k i0 ≠ 0 := fun h ↦ hi0 (congrArg Subtype.val h)
    have hpos : 0 < ⨆ i, v (coordVec z k i) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.mpr hi0')
        (le_ciSup (f := fun i ↦ v (coordVec z k i)) (Set.finite_range _).bddAbove i0)
    rw [← Real.log_inv]
    refine Real.log_le_log hpos (ciSup_le fun i ↦ ?_)
    have hI : IsIntegral ℤ ((δ : K) * coordVec z k i) := by
      have h1 := hint k i
      have h2 : (K.val : K →+* AlgebraicClosure ℚ) ((δ : K) * coordVec z k i) =
          (δ : AlgebraicClosure ℚ) * z k i := by
        simp [coordVec]
      rw [← h2] at h1
      exact (isIntegral_algHom_iff ((K.val : K →+* AlgebraicClosure ℚ).toIntAlgHom)
        K.val.injective).mp h1
    have h3 := finitePlace_le_one_of_isIntegral v hI
    rw [map_mul] at h3
    calc v (coordVec z k i) = (v (δ : K))⁻¹ * (v (δ : K) * v (coordVec z k i)) := by
          field_simp
      _ ≤ (v (δ : K))⁻¹ * 1 := mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hδv).le
      _ = (v (δ : K))⁻¹ := mul_one _
  have hsupp1 := finite_support_height (HermLine.standard (n := n)) z hz
  have hsupp2 : (Function.support fun v : FinitePlace K ↦ Real.log (v (δ : K))).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hne).subset fun v hv h ↦ hv ?_
    have h' : v (δ : K) = 1 := h
    show Real.log (v (δ : K)) = 0
    rw [h', Real.log_one]
  set T := (hsupp1.union hsupp2).toFinset
  have hfin : (∑ᶠ v : FinitePlace K, ∑ k, ((HermLine.standard (n := n)).deg k : ℝ) *
      Real.log (⨆ i, v (coordVec z k i))) ≤ Fintype.card ι * (d * Real.log δ) := by
    rw [finsum_eq_sum_of_support_subset (s := T) _
      (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inl hv)))]
    have h2 : ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = ∑ v ∈ T, Real.log (v (δ : K)) :=
      finsum_eq_sum_of_support_subset (s := T) _
        (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inr hv)))
    have h3 := finsum_log_finitePlace_natCast (K := K) hδ
    rw [h2] at h3
    calc ∑ v ∈ T, ∑ k, ((HermLine.standard (n := n)).deg k : ℝ) * Real.log (⨆ i, v (coordVec z k i))
        ≤ ∑ v ∈ T, ∑ _k : ι, -Real.log (v (δ : K)) := by
          refine Finset.sum_le_sum fun v _ ↦ Finset.sum_le_sum fun k _ ↦ ?_
          simp only [HermLine.standard, Int.cast_one, one_mul]
          exact hloc v k
      _ = Fintype.card ι * -(∑ v ∈ T, Real.log (v (δ : K))) := by
          simp [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = Fintype.card ι * (d * Real.log δ) := by rw [h3, neg_neg]

  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
  have : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  have harchK : ∀ σ : K →+* ℂ, Real.log ((HermLine.standard (n := n)).metric
      fun k i ↦ σ (coordVec z k i)) ≤ ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    intro σ
    let σ' : AlgebraicClosure ℚ →+* ℂ := ComplexEmbedding.lift (AlgebraicClosure ℚ) σ
    have hσ : ∀ k i, σ (coordVec z k i) = σ' (z k i) := by
      intro k i
      have := ComplexEmbedding.lift_algebraMap_apply (AlgebraicClosure ℚ) σ (coordVec z k i)
      rw [← this]
      rfl
    have hpos : ∀ k, 0 < l2Norm (fun i ↦ σ (coordVec z k i)) := by
      intro k
      obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
      refine vectorL2Norm_pos (Function.ne_iff.mpr ⟨i0, ?_⟩)
      intro h
      apply hi0
      have h2 := (map_eq_zero σ).mp h
      have := congrArg Subtype.val h2
      simpa [coordVec] using this
    change Real.log (∏ k, l2Norm (fun i ↦ σ (coordVec z k i))) ≤ _
    rw [Real.log_prod (fun k _ ↦ (hpos k).ne')]
    refine Finset.sum_le_sum fun k _ ↦ Real.log_le_log (hpos k) ?_
    have := vectorL2Norm_le_sqrt_card_mul (fun i ↦ σ (coordVec z k i)) hR.le (fun i ↦ by rw [hσ]; exact harch σ' k i)
    simpa using this
  have harchSum : ∑ σ : K →+* ℂ, Real.log ((HermLine.standard (n := n)).metric
      fun k i ↦ σ (coordVec z k i)) ≤ d * ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    refine (Finset.sum_le_sum fun σ _ ↦ harchK σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]

  set S := ∑ k, Real.log (Real.sqrt (n k + 1) * R) with hS
  unfold height
  rw [← hd_def]
  calc d⁻¹ * (_ + _) ≤ d⁻¹ * (Fintype.card ι * (d * Real.log δ) +
        d * ∑ k, Real.log (Real.sqrt (n k + 1) * R)) :=
        mul_le_mul_of_nonneg_left (add_le_add hfin harchSum) (inv_pos.mpr hd).le
    _ = ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hS]
        field_simp

end

end GroundTheory.Heights₂.Heights
