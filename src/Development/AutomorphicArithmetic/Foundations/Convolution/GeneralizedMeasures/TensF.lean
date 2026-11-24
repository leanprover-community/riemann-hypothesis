module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AvgTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.FinTens
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

theorem UpperTheory.ConvolutionTheory.GM.avgF :
    AvgF := by
  intro F _ _ n hn S β f hS hoff
  obtain ⟨r, w, hw, hr⟩ : ∃ (r : ℕ) (w : Fin r → Pl F), Function.Injective w ∧ Set.range w = (S : Set (Pl F)) :=
    ⟨S.card, fun i => (S.equivFin.symm i : Pl F),
      Subtype.val_injective.comp S.equivFin.symm.injective, by
        ext v
        constructor
        · rintro ⟨i, rfl⟩
          exact (S.equivFin.symm i).2
        · intro hv
          exact ⟨S.equivFin ⟨v, hv⟩, by simp⟩⟩
  have ht : ∀ i, C.Test (f (w i)) := fun i => hS _ (by
    have : w i ∈ (S : Set (Pl F)) := hr ▸ Set.mem_range_self i
    exact this)
  have ho : ∀ v, v ∉ Set.range w → f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set (C.Gw n v)).indicator 1 := by
    intro v hv
    exact hoff v (fun h => hv (hr ▸ h))
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨e, he, ⟨U, hUo, hU⟩, -⟩ := UpperTheory.ConvolutionTheory.Tf.finTens F n (Measure.haar) (Measure.haar) r w hw f ht ho
  refine ⟨e, ?_, fun x => he x, fun x => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hc : Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
      have : Continuous (fun y : AdelicGLn.FiniteAdelicGL F n => x⁻¹ * y) := continuous_const.mul continuous_id
      simpa using this.tendsto x
    filter_upwards [hc (hUo.mem_nhds U.one_mem)] with y hy
    have := (hU _ hy x).2
    simpa using this
  · obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.Tf.avgTens F n hn β e (fun g => β (infPart F n g) * e (finPart F n g)) (fun _ => rfl)
    have hΦ : tensF (onInf β) f = fun g => β (infPart F n g) * e (finPart F n g) := by
      funext g
      simp only [tensF, onInf]
      rw [h2 g, he (finPart F n g)]
      congr 1
    rw [hΦ, h1 x]
