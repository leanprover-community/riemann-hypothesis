module

import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.SummablePrimesRpow
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Filter Topology Asymptotics

namespace Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds

section Sum
variable (K : Type) [Field K] [NumberField K]

lemma card_fib (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} =
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k).toFinset.card := by
  rw [← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k),
    ← Nat.card_coe_set_eq]
  rfl

lemma sum_le_count (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) ≤
      (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ n} : ℝ) := by
  classical
  have hle := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n
  set T := hle.toFinset with hTdef
  have hT : Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ n} = T.card := by
    have hs : {I : Ideal (𝓞 K) | (Ideal.absNorm I : ℝ) ≤ n} = {I | Ideal.absNorm I ≤ n} := by
      ext I; simp
    rw [← Set.ncard_eq_toFinset_card _ hle, ← hs, ← Nat.card_coe_set_eq]
    rfl
  have hfib : ∀ k ∈ Finset.Icc 1 n,
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} = (T.filter (fun I => Ideal.absNorm I = k)).card := by
    intro k hk
    rw [card_fib]
    congr 1
    ext I
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter, hTdef]
    constructor
    · intro h; exact ⟨by rw [h]; exact (Finset.mem_Icc.1 hk).2, h⟩
    · intro h; exact h.2
  have hsum : T.card = ∑ k ∈ Finset.range (n + 1), (T.filter (fun I => Ideal.absNorm I = k)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro I hI
    simp only [hTdef, Finset.coe_range, Set.mem_Iio, Set.Finite.coe_toFinset, Set.mem_ofPred_eq] at hI ⊢
    omega
  rw [hT, hsum, Finset.sum_congr rfl (fun k hk => by rw [hfib k hk])]
  push_cast
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
  · intros; positivity

lemma count_isBigO :
    (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ n} : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  have h := NumberField.Ideal.tendsto_norm_le_div_atTop K
  have h1 := h.isBigO_one ℝ
  have h2 : (fun s : ℝ => (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ s} : ℝ)) =O[atTop]
      (fun s : ℝ => s) := by
    have := h1.mul (isBigO_refl (fun s : ℝ => s) atTop)
    refine this.congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs
      field_simp
    · filter_upwards with s; simp
  have h3 := h2.comp_tendsto tendsto_natCast_atTop_atTop
  simpa [Function.comp_def, Real.rpow_one] using h3

lemma lseries_summable {σ : ℝ} (hσ : 1 < σ) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) (σ : ℂ) := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1)
  · refine (isBigO_of_le _ (fun n => ?_)).trans (count_isBigO K)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)),
      Real.norm_of_nonneg (by positivity)]
    exact sum_le_count K n
  · intro n; positivity
  · norm_num
  · simpa using hσ

theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun w : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-σ)) := by
  apply PositivityTheory.Lord.summable_primes_rpow <;> assumption

end Sum

end Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds

namespace Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds
section Euler
variable {ι : Type} (q : ι → ℕ) (ε : ι → ℕ → ℂ) (n : ℕ)

variable {q ε}

variable (hsum : ∀ σ : ℝ, 1 < σ → Summable (fun i => (q i : ℝ) ^ (-σ)))
include hsum

end Euler
end Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds

namespace Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds
open Formalism.MainNotions.SchurIrreducible MeasureTheory

section Tail
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]



end Tail

section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)

end Main
end Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds

namespace Formalism.MainNotions.DIV.Proofs
open Formalism.BasicNotions Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.MainNotions.DIV.Proofs
