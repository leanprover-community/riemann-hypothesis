module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.AdaptedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_pow_le {ϖ : kˣ} (h : IsUnif ϖ) (s : kˣ) :
    ∀ᶠ e : ℕ in Filter.atTop, valuation k ((ϖ ^ e : kˣ) : k) ≤ valuation k (s : k) := by
  have h1 : valuation k (ϖ : k) < 1 := (h _).2 le_rfl
  have hs : valuation k (s : k) ≠ 0 := by simp
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hs)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le he).trans hm.le

theorem eventually_subset_cball {ϖ : kˣ} (h : IsUnif ϖ) {K : Set k} (hK : IsCompact K) :
    ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹ := by
  have key : ∀ s : kˣ, ∀ᶠ e : ℕ in Filter.atTop, cball s ⊆ cball (ϖ ^ e)⁻¹ := by
    intro s
    filter_upwards [eventually_pow_le h s⁻¹] with e he x hx
    have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
    have he0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := by
      rw [pos_iff_ne_zero]; simp
    simp only [cball, Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx he ⊢
    exact hx.trans ((le_inv_comm₀ he0 hs).1 he)
  refine hK.induction_on (p := fun K => ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹)
    (by simp) ?_ ?_ ?_
  · intro s t hst ht
    exact ht.mono fun e he => hst.trans he
  · intro s t hs ht
    filter_upwards [hs, ht] with e h1 h2 using Set.union_subset h1 h2
  · intro x _
    by_cases hx : x = 0
    · subst hx
      exact ⟨cball 1, mem_nhdsWithin_of_mem_nhds (cball_mem_nhds 1), key 1⟩
    · exact ⟨cball (Units.mk0 x hx), mem_nhdsWithin_of_mem_nhds
        ((isOpen_cball _).mem_nhds (by simp [cball])), key _⟩

variable {n n' : Type}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem withCol_add (x₀ : Matrix n n' k) (y z : n → k) :
    withCol x₀ (y + z) = withCol x₀ y + withCol (0 : Matrix n n' k) z := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [withCol]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_withCol_zero :
    Continuous fun z : n → k => withCol (0 : Matrix n n' k) z := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simp only [withCol, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop

theorem eventually_box_subset [Fintype n] {ϖ : kˣ} (h : IsUnif ϖ) {U : Set (n → k)}
    (hU : U ∈ 𝓝 (0 : n → k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ z ∈ box n (ϖ ^ e), z ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose s hs using fun i => exists_cball_subset (ht i)
  filter_upwards [Filter.eventually_all.2 fun i => eventually_pow_le h (s i)] with e he z hz
  exact hsub fun i _ => hs i (le_trans (hz i) (he i))

theorem eventually_adapted [Fintype n] [Fintype n'] {ϖ : kˣ} (h : IsUnif ϖ)
    {Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ (x₀ : Matrix n n' k) (y : n → k),
      (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧
        ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  obtain ⟨Λ, hΛ, hinv⟩ := sb_matrix_exists_isOpen_addSubgroup k _ _ Ψ hΨ
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ r : n, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k => x (Sum.inl r) (Sum.inr 0)) ''
        tsupport Ψ ⊆ cball (ϖ ^ e)⁻¹ := fun r =>
    eventually_subset_cball h (hc.image (by fun_prop))
  have h0 : withCol (0 : Matrix n n' k) (0 : n → k) = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [withCol]
  have h2 : (fun z : n → k => withCol (0 : Matrix n n' k) z) ⁻¹' (Λ : Set _) ∈ 𝓝 (0 : n → k) :=
    (hΛ.preimage continuous_withCol_zero).mem_nhds (by
      simp only [Set.mem_preimage, h0]; exact Λ.zero_mem)
  filter_upwards [Filter.eventually_all.2 h1, eventually_box_subset h h2] with e he1 he2 x₀ y
  refine ⟨fun hne r => ?_, fun z hz => ?_⟩
  · exact he1 r ⟨withCol x₀ y, subset_tsupport _ hne, rfl⟩
  · rw [withCol_add]
    exact hinv _ _ (he2 z hz)

theorem exists_adapted_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  intro k _ _ _ _ n _ _ n' _ _ S hS hSB ϖ h
  exact ((Filter.eventually_ge_atTop 1).and ((Filter.eventually_all_finite hS).2
    fun Ψ hΨ => eventually_adapted h (hSB Ψ hΨ))).exists

end GlobalTheory.AdaptedExp
