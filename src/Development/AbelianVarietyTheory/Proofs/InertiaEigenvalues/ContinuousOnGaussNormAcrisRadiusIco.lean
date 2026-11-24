module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomialStatement
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

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
open Filter Topology

noncomputable section

namespace GlobalTheory.PMon.Gauss

theorem gC_zero_of_lt_one (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  unfold gC
  split_ifs with h
  · have hN := Classical.choose_spec h
    set N := Classical.choose h
    have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
    have hl : N (l : Formalism.Per.Acris l) = ρ := by
      have := hN.2.2.2.2 (l : Formalism.Per.Ainf l)
      rw [map_natCast] at this
      rw [this]
      exact GlobalTheory.GaussSlope.gauss_l l h0
    rw [mul_zero, hl] at hm
    have : (1 - ρ) * N 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · rfl

theorem continuousOn_gC (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) :
    ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) := by
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  by_cases hx : x = 0
  · subst hx
    refine (continuousOn_const (c := (0 : ℝ))).congr fun ρ hρ => ?_
    exact gC_zero_of_lt_one l (hl0.le.trans hρ.1) hρ.2
  intro ρ₀ hρ₀
  have hpos : 0 < ρ₀ := hl0.trans_le hρ₀.1
  obtain ⟨⟨c, k, ρ₂, -, h02, -, hR⟩, hL⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l x hx ρ₀ hρ₀.1 hρ₀.2
  have hS : Set.Ico (l : ℝ)⁻¹ 1 = (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Iic ρ₀) ∪ (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Ici ρ₀) := by
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro hy
      rcases le_total y ρ₀ with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h) <;> exact h.1
  rw [ContinuousWithinAt, hS, ← ContinuousWithinAt, continuousWithinAt_union]
  constructor
  · rcases eq_or_lt_of_le hρ₀.1 with heq | hlt
    · refine (continuousWithinAt_singleton (f := fun ρ => gC l ρ x) (x := ρ₀)).mono ?_
      rintro y ⟨hy1, hy2⟩
      exact le_antisymm hy2 (heq ▸ hy1.1)
    · obtain ⟨c', k', ρ₁, -, -, h10, hL'⟩ := hL hlt
      have hg : ContinuousWithinAt (fun ρ : ℝ => c' * ρ ^ k') (Set.Iic ρ₀) ρ₀ :=
        (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k' (Or.inl hpos.ne'))).continuousWithinAt
      have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₁ ρ₀) ρ₀ :=
        (hg.mono Set.Icc_subset_Iic_self).congr (fun y hy => hL' y hy) (hL' ρ₀ ⟨h10.le, le_rfl⟩)
      exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE h10)).mono Set.inter_subset_right
  · have hg : ContinuousWithinAt (fun ρ : ℝ => c * ρ ^ k) (Set.Ici ρ₀) ρ₀ :=
      (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k (Or.inl hpos.ne'))).continuousWithinAt
    have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₀ ρ₂) ρ₀ :=
      (hg.mono Set.Icc_subset_Ici_self).congr (fun y hy => hR y hy) (hR ρ₀ ⟨le_rfl, h02.le⟩)
    exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE h02)).mono Set.inter_subset_right

theorem continuousOn_gC_target :
    ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) :=
  fun l _ x => continuousOn_gC l x

end GlobalTheory.PMon.Gauss

end
