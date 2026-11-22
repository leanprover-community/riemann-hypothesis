module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtBasePointStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPointsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateRatioValueAtPointStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem coord_ne (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k} (hq : (X q : MRing ι) ∉ mCoordIdeal z) :
    x q ≠ 0 := fun h => hq (by
  have hm : (X q : MRing ι) ∈ mCoordIdeal x := by
    show mConeMap x (X q) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h0 : z q = 0 := by simpa using hz.2 _ hm
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

theorem isValueAt_sum {α : Type} (S : Finset α) (f : α → Ω) (v : α → ℂ)
    (h : ∀ i ∈ S, IsValueAt x (f i) z (v i)) : IsValueAt x (∑ i ∈ S, f i) z (∑ i ∈ S, v i) := by
  induction S using Finset.induction_on with
  | empty => simpa using ValRing.isValueAt_zero_self x z
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ValRing.isValueAt_add (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Values

theorem stepCols_ne {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · have hlt : N - j < N := by omega
    have hm : (⟨N - j, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
      omega
    rw [e] at hm
    simp at hm
  · have hm : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
      omega
    rw [e] at hm
    simp at hm

theorem read_minor {κ : Type} [Fintype κ] {N : ℕ} (P : Finset (Fin N) → Prop)
    (A : Finset (Fin N) → κ → ℂ) (B : κ → Finset (Fin N) → ℂ)
    (hAB : ∀ I I', P I → P I' → ∑ m, A I m * B m I' = if I = I' then 1 else 0)
    (μ : Finset (Fin N) → ℂ) (hμ : ∀ I, ¬ P I → μ I = 0) (w : κ → ℂ) (a : ℂ)
    (hw : ∀ m, w m = a * ∑ I, B m I * μ I) (I' : Finset (Fin N)) (hI' : P I') :
    ∑ m, A I' m * w m = a * μ I' := by
  have e : ∑ m, A I' m * w m = a * ∑ I, (∑ m, A I' m * B m I) * μ I := by
    simp only [hw, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e, Finset.sum_eq_single I']
  · rw [hAB I' I' hI' hI', if_pos rfl, one_mul]
  · intro I _ hne
    by_cases hI : P I
    · rw [hAB I' I hI' hI, if_neg hne.symm, zero_mul]
    · rw [hμ I hI, mul_zero]
  · simp

theorem move_minor {κ : Type} [Fintype κ] {N : ℕ} (P : Finset (Fin N) → Prop)
    (S : Finset (Finset (Fin N))) (hS : ∀ I, I ∈ S ↔ P I) (A : Finset (Fin N) → κ → ℂ)
    (D : Finset (Fin N) → ℂ) (Tm : Finset (Fin N) → Finset (Fin N) → ℂ)
    (μ : Finset (Fin N) → ℂ) (hμ : ∀ I, ¬ P I → μ I = 0) (w : κ → ℂ) (a : ℂ)
    (hA : ∀ I', P I' → ∑ m, A I' m * w m = a * μ I') :
    ∑ m, (∑ I, ∑ I' ∈ S, D I * Tm I I' * A I' m) * w m = a * ∑ I, D I * ∑ I', Tm I I' * μ I' := by
  have e : ∑ m, (∑ I, ∑ I' ∈ S, D I * Tm I I' * A I' m) * w m =
      ∑ I, ∑ I' ∈ S, D I * Tm I I' * ∑ m, A I' m * w m := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ S) fun I' _ h => by
    rw [hμ I' fun hp => h ((hS I').2 hp), mul_zero], Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun I' h => by rw [hA I' ((hS I').1 h)]; ring

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep
