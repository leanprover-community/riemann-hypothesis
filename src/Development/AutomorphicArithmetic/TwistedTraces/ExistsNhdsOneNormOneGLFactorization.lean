module

public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_nhds_one_normOneGL_factorization :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (N : Set (archGroup K n)) (U : Subgroup (AdelicGLn.integralFiniteGL K n)), N ∈ 𝓝 (1 : archGroup K n) → IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → ∃ N' ∈ 𝓝 (1 : normOneGL (K := K) (n := n)), ∀ g ∈ N', ∃ a ∈ N, ∃ u ∈ U, g = archP K n a * retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n)) := by
  intro K _ _ n N U hN hU
  have hU' : IsOpen (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))) :=
    (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have hp : Continuous fun g : normOneGL (K := K) (n := n) => AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n) :=
    (AdelicGLn.prodEquiv K n).continuous.comp continuous_subtype_val
  have ha : Continuous fun g : normOneGL (K := K) (n := n) =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1 :=
    (archEquiv K n).continuous.comp hp.fst
  have hf : Continuous fun g : normOneGL (K := K) (n := n) =>
      (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := hp.snd
  refine ⟨(fun g : normOneGL (K := K) (n := n) =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1) ⁻¹' N ∩
    (fun g : normOneGL (K := K) (n := n) => (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2) ⁻¹'
      (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))), Filter.inter_mem ?_ ?_, ?_⟩
  · refine ha.continuousAt.preimage_mem_nhds ?_
    simpa only [OneMemClass.coe_one, map_one, Prod.fst_one] using hN
  · refine (hU'.preimage hf).mem_nhds ⟨1, U.one_mem, ?_⟩
    simp only [OneMemClass.coe_one, map_one, Prod.snd_one]
  · rintro g ⟨hg, u, hu, e⟩
    refine ⟨_, hg, u, hu, ?_⟩
    have e' : (u : AdelicGLn.FiniteAdelicGL K n) = (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := e
    rw [e']
    calc g = retractOne (g : AdelicGLn.AdelicGL K n) := (retractOne_coe g).symm
      _ = retractOne (infEmb K n (archEquiv K n (AdelicGLn.prodEquiv K n g).1) *
            finEmb K n (AdelicGLn.prodEquiv K n g).2) := by rw [infEmb_mul_finEmb]
      _ = _ := by rw [retractOne_mul, retract_infEmb]
