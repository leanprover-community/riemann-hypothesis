module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitHeightSummableExpNegAbs
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory

open Filter Topology

theorem hasSum_pi_prod_of_summable_norm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by
  intro ι _ _ J f hf
  classical
  have hnorm : Summable fun j : ∀ i, J i => ‖∏ i, f i (j i)‖ := by
    have := splitHeight_summable_pi_prod (α := J) (f := fun i x => ‖f i x‖)
      (fun i x => norm_nonneg (f i x)) hf
    refine this.congr fun j => ?_
    exact (norm_prod _ _).symm
  have hs : Summable fun j : ∀ i, J i => ∏ i, f i (j i) := hnorm.of_norm
  have hcof : Tendsto (fun S : ∀ i, Finset (J i) => Fintype.piFinset S) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun t => ⟨fun i => t.image (· i), fun S hS => ?_⟩
    intro x hx
    exact Fintype.mem_piFinset.2 fun i => hS i (Finset.mem_image_of_mem _ hx)
  have h1 : Tendsto (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i))
      atTop (𝓝 (∑' j : ∀ i, J i, ∏ i, f i (j i))) := hs.hasSum.comp hcof
  have hproj : ∀ i, Tendsto (fun S : ∀ i, Finset (J i) => S i) atTop atTop := by
    intro i
    refine Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨Function.update (fun j => (∅ : Finset (J j))) i b, fun S hS => ?_⟩
    have := hS i
    simpa using this
  have h2 : Tendsto (fun S : ∀ i, Finset (J i) => ∏ i, ∑ x ∈ S i, f i x)
      atTop (𝓝 (∏ i, ∑' j, f i j)) :=
    tendsto_finsetProd _ fun i _ => ((hf i).of_norm.hasSum).comp (hproj i)
  have h3 : (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i)) =
      fun S => ∏ i, ∑ x ∈ S i, f i x := by
    funext S; exact (Finset.prod_univ_sum S fun i x => f i x).symm
  rw [h3] at h1
  have := tendsto_nhds_unique h1 h2
  rw [← this]; exact hs.hasSum

end GlobalTheory
