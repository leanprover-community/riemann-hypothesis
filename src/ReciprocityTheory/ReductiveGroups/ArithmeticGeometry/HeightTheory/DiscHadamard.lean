module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscPointwise
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.EvTEqBlockPointOfMh
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_hadamard (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (a b : KTp K d.D d.N)
    (hab : d.IsPres hd h a b) (sg : K →+* ℂ) :
    d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg ≤
      d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) := by
  haveI : MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) :=
    ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (Nat.succ_pos _)
  have he := hd.a4.choose_spec.1
  have hF : ∀ c, MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        -Real.log (d.nrm c d.wF (hd.a4.choose c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
    intro c
    have := ((d.int_Nsg hd h hI2be c sg).1 d.wF (hd.a4.choose c) (by simp) (he c).1 (he c).2).neg
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.neg_apply]
    rw [← finsum_neg_distrib]
    congr 1; ext P
    rw [← finsum_neg_distrib]
    rfl
  have hR : MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      (d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          -Real.log (d.nrm c d.wF (hd.a4.choose c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) :=
    (MeasureTheory.integrable_const _).add
      ((MeasureTheory.integrable_finsetSum _ fun c _ => hF c).const_mul 2)
  have hmono := MeasureTheory.integral_mono_ae (d.integrable_log_norm_sub_log_norm hd h a b hab sg) hR
    (d.disc_pointwise hd h a b hab sg)
  have hc : ∫ _z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1),
      ((d.del : ℝ) * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))))
        ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) =
      (d.del : ℝ) * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) := by simp
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _)
      ((MeasureTheory.integrable_finsetSum _ fun c _ => hF c).const_mul 2),
    hc, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ fun c _ => hF c] at hmono
  have hN : d.Nsg d.wF hd.a4.choose sg = ∑ c, ∫ z, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
      -Real.log (d.nrm c d.wF (hd.a4.choose c) P) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := rfl
  have hm : d.mSgP sg a b = ∫ z, (Real.log ‖d.evT sg 0 (d.tOf z) a‖ -
      Real.log ‖d.evT sg 0 (d.tOf z) b‖) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := rfl
  rw [hN, hm]
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
