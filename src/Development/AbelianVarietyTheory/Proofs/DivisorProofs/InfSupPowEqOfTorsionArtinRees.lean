module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Colon

@[expose] public section

namespace GlobalTheory

theorem inf_sup_pow_eq_of_torsion : ∀ (B : Type) [CommRing B] [IsNoetherianRing B]
    (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  intro B _ _ K τ τ' hle htor
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian τ' : τ'.FG)
  have hrad : K ≤ (τ.colon (s : Set B)).radical := by
    intro f hf
    have hm : ∀ b ∈ s, ∃ m : ℕ, f ^ m * b ∈ τ := fun b hb =>
      htor b (hs ▸ Submodule.subset_span hb) f hf
    choose! m hm using hm
    refine ⟨∑ b ∈ s, m b, ?_⟩
    rw [Submodule.mem_colon]
    intro b hb
    have hb' : b ∈ s := hb
    have hle' : m b ≤ ∑ b ∈ s, m b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb'
    rw [smul_eq_mul, ← Nat.sub_add_cancel hle', pow_add, mul_assoc]
    exact τ.mul_mem_left _ (hm b hb')
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian K)
  have hKm : K ^ m * τ' ≤ τ := by
    rw [Ideal.mul_le]
    intro r hr t ht
    have hr' := Submodule.mem_colon.mp (hm hr)
    rw [← hs] at ht
    induction ht using Submodule.span_induction with
    | mem x hx => simpa [smul_eq_mul] using hr' x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact τ.add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact τ.mul_mem_left a hx
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul K (M := B) (τ' : Submodule B B)
  refine ⟨c + m, fun k hk => ?_⟩
  have hAR : K ^ k ⊓ τ' ≤ τ := by
    have h := hc k (by omega)
    simp only [smul_eq_mul, Ideal.mul_top] at h
    rw [h]
    calc K ^ (k - c) * (K ^ c ⊓ τ') ≤ K ^ (k - c) * τ' := Ideal.mul_mono_right inf_le_right
      _ ≤ K ^ m * τ' := Ideal.mul_mono_left (Ideal.pow_le_pow_right (by omega))
      _ ≤ τ := hKm
  apply le_antisymm
  · rw [inf_comm, sup_inf_assoc_of_le _ hle]
    exact sup_le le_rfl hAR
  · exact le_inf hle le_sup_left

end GlobalTheory
