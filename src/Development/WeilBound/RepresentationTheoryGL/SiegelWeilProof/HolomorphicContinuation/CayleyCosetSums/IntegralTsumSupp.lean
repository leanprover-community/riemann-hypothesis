module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem ιK_apply (k : KR n) : ιK n k = mR (k : GR n) := rfl

theorem continuous_fzG (hS : SecFz) (w : ℂ) : Continuous fun Y : GR n => fz m e w (mR Y) := by
  have h1 : (fun Y : GR n => fz m e w (mR Y)) = fun Y => F0 m 0 e Y * ((hLoc Y : ℝ) : ℂ) ^ w :=
    funext fun Y => hS n m e w Y
  rw [h1]
  refine (Vac.continuous_weight_factor detU1 m 0 e).mul ?_
  refine Continuous.cpow (Complex.continuous_ofReal.comp (Vac.continuous_hLoc detU1)) continuous_const fun Y => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (Vac.hLoc_pos detU1 Y)

theorem integral_tsum_supp {X : Type} [MeasurableSpace X] {ν : Measure X} {ι' : Type} (F : ι' → X → ℂ) (u : ι' → ℝ)
    (hu : Summable u) (hu0 : ∀ q, 0 ≤ u q) (bd : X → ℝ) (hbd : Integrable bd ν)
    (hF : ∀ q x, ‖F q x‖ ≤ u q * bd x) (hFm : ∀ q, AEStronglyMeasurable (F q) ν) :
    Summable (fun q => ∫ x, F q x ∂ν) ∧ ∫ x, ∑' q, F q x ∂ν = ∑' q, ∫ x, F q x ∂ν := by
  have hFi : ∀ q, Integrable (F q) ν := fun q =>
    Integrable.mono' (hbd.const_mul (u q)) (hFm q) (ae_of_all _ (hF q))
  have hIn : ∀ q, ‖∫ x, F q x ∂ν‖ ≤ u q * ∫ x, bd x ∂ν := by
    intro q
    calc ‖∫ x, F q x ∂ν‖ ≤ ∫ x, u q * bd x ∂ν := norm_integral_le_of_norm_le (hbd.const_mul (u q)) (ae_of_all _ (hF q))
      _ = u q * ∫ x, bd x ∂ν := integral_const_mul _ _
  refine ⟨Summable.of_norm_bounded (hu.mul_right _) hIn, ?_⟩
  have hF0 : ∀ q, q ∉ Function.support u → ∀ x, F q x = 0 := by
    intro q hq x
    have h0 : u q = 0 := Function.notMem_support.mp hq
    have := hF q x
    rw [h0, zero_mul] at this
    exact norm_le_zero_iff.mp this
  have : Countable (Function.support u) := hu.countable_support.to_subtype
  have hL : ∀ x, ∑' q, F q x = ∑' s : Function.support u, F s x := by
    intro x
    refine (tsum_subtype_eq_of_support_subset (f := fun q => F q x) ?_).symm
    intro q hq
    by_contra h
    exact hq (hF0 q h x)
  have hN : ∀ q, ∫ x, ‖F q x‖ ∂ν ≤ u q * ∫ x, bd x ∂ν := by
    intro q
    calc ∫ x, ‖F q x‖ ∂ν ≤ ∫ x, u q * bd x ∂ν :=
          integral_mono (hFi q).norm (hbd.const_mul (u q)) (hF q)
      _ = u q * ∫ x, bd x ∂ν := integral_const_mul _ _
  have hsumn : Summable fun s : Function.support u => ∫ x, ‖F s x‖ ∂ν :=
    Summable.of_nonneg_of_le (fun s => integral_nonneg fun _ => norm_nonneg _) (fun s => hN s)
      ((hu.subtype _).mul_right _)
  simp_rw [hL]
  rw [← integral_tsum_of_summable_integral_norm (F := fun (s : Function.support u) x => F s x) (fun s => hFi s) hsumn]
  refine tsum_subtype_eq_of_support_subset (f := fun q => ∫ x, F q x ∂ν) ?_
  intro q hq
  by_contra h
  exact hq (by simp only [hF0 q h, integral_zero])

end PositivityTheory.Rg.Sw.HSt.FarP
