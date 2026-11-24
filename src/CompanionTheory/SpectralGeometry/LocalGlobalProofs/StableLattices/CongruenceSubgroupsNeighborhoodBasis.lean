module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Topology

namespace GlobalTheory.CompanionTheory.CartGL

theorem exists_pi_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Fin n → Fin n → L)} {x : Fin n → Fin n → L} (hA : A ∈ 𝓝 x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin n → Fin n → L, (∀ i j, ‖y i j - x i j‖ ≤ ε) → y ∈ A := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hA
  refine ⟨ε / 2, half_pos hε, fun y hy => hball ?_⟩
  have hd : dist y x ≤ ε / 2 := by
    rw [dist_pi_le_iff (half_pos hε).le]
    intro i
    rw [dist_pi_le_iff (half_pos hε).le]
    intro j
    rw [dist_eq_norm]
    exact hy i j
  rw [Metric.mem_ball]
  linarith

theorem exists_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Matrix (Fin n) (Fin n) L)} (hA : A ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Matrix (Fin n) (Fin n) L,
      (∀ i j, ‖(M - 1) i j‖ ≤ ε) → M ∈ A := by
  obtain ⟨ε, hε, h⟩ := exists_pi_entry_box (x := (1 : Matrix (Fin n) (Fin n) L)) hA
  refine ⟨ε, hε, fun M hM => h M fun i j => ?_⟩
  have := hM i j
  rwa [Matrix.sub_apply] at this

theorem congK_cofinal (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (U : Set (GL (Fin n) L)) (hU : IsOpen U) (h1U : (1 : GL (Fin n) L) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r ≤ ε →
      (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) ⊆ U := by
  have hU1 : U ∈ 𝓝 (1 : GL (Fin n) L) := hU.mem_nhds h1U
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap, map_one] at hU1
  obtain ⟨V, hV, hVU⟩ := hU1
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    (mem_nhds_prod_iff (x := (1 : Matrix (Fin n) (Fin n) L)) (y := MulOpposite.op 1)).1 hV
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_entry_box hA
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_entry_box hB'
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r h0 h1 hr k hk => hVU (hAB ⟨?_, ?_⟩)⟩
  · exact h₁ _ fun i j => ((hk i j).1.trans hr).trans (min_le_left _ _)
  · exact h₂ _ fun i j => ((hk i j).2.trans hr).trans (min_le_right _ _)

end GlobalTheory.CompanionTheory.CartGL
