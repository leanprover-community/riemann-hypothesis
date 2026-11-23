module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RegOkPi
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

theorem UpperTheory.ConvolutionTheory.L1.matchFin :
    UpperTheory.ConvolutionTheory.L1.MatchFin := by
  intro F E _ _ _ _ _ σ m v D n _ _ _ _ μE μF hE hF
  have hreg : UpperTheory.ConvolutionTheory.L1.RegOk (v.adicCompletion F) n := UpperTheory.ConvolutionTheory.L1.regOkPi.1 _ n
  obtain ⟨c, hc, hμ, hφ⟩ := UpperTheory.ConvolutionTheory.L1.matchSplit (v.adicCompletion F) (CompletionsOver E v)
    (incFin E v) (galFin σ v) m D n μE μF hE hF hreg
  refine ⟨c, hc, hμ, fun φ h1 h2 => (hφ φ h1 h2).2.2, fun φ h => ?_⟩
  obtain ⟨hcomp, hglue, -, hgc, hcc, -⟩ :=
    UpperTheory.ConvolutionTheory.L1.glueBasic (v.adicCompletion F) (CompletionsOver E v) (incFin E v) (galFin σ v) m D n
  let e : (Fin (m + 1) → GL (Fin n) (v.adicCompletion F)) ≃ₜ GL (Fin n) (CompletionsOver E v) :=
    { toFun := D.glue n
      invFun := fun x i => D.comp n i x
      left_inv := fun g => funext fun i => hcomp g i
      right_inv := hglue
      continuous_toFun := hgc
      continuous_invFun := continuous_pi hcc }
  have hΨc : Continuous fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) :=
    continuous_finsetProd _ fun i _ => (h i).1.comp (continuous_apply i)
  have hΨs : HasCompactSupport fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) := by
    refine HasCompactSupport.intro' (K := Set.pi Set.univ fun i => tsupport (φ i))
      (isCompact_univ_pi fun i => (h i).2) (isClosed_set_pi fun i _ => isClosed_tsupport _) ?_
    intro g hg
    obtain ⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ g i ∉ tsupport (φ i) := by
      simpa [Set.mem_pi] using hg
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
  have htens : D.tens n φ = (fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i)) ∘ e.symm :=
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [htens]
    exact hΨc.comp e.symm.continuous
  · rw [htens]
    exact hΨs.comp_isClosedEmbedding e.symm.isClosedEmbedding
  · have hpush := UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) (v.adicCompletion F)) μF m φ
      (fun i => (h i).1) (fun i => (h i).2)
    rw [← hpush]
    unfold UpperTheory.ConvolutionTheory.L1.Split.transfer
    congr 1
    funext g
    rw [htens]
    change (∏ i, φ i ((e.symm (e g)) i)) = _
    rw [e.symm_apply_apply]
