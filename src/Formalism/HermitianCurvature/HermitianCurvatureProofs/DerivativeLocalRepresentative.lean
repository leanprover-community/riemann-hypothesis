module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupEquationsPostHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieDecompositionLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem derivative_local_representative : RdVRep := by
  intro k r E _ _ X U F f hX hU hc he h hh hhG
  have hc' : ContDiffOn ℝ (((1 : ℕ∞) : WithTop ℕ∞)) F U := by exact_mod_cast hc
  refine ⟨LieDecompositionLocal.rdV_eq_fderiv (m := 1) le_rfl hU hh hhG hc' he hX, ?_⟩
  have hd : DifferentiableAt ℝ F h :=
    (hc.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hh)
  have hloc : Q.LdV X f h = Q.LdV X F h := by
    show deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * h)) 0 =
      deriv (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * h)) 0
    apply Filter.EventuallyEq.deriv_eq
    have hcont : Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * h) := by
      have h1 := (gpMulR h).continuous.comp (B5.curve_contDiff (1 : B.Mat k r) X).continuous
      refine h1.congr fun t => ?_
      simp [gpMulR_apply]
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * h ∈ U := by
      apply hcont.continuousAt.preimage_mem_nhds
      have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * h = h := by simp
      rw [h0]
      exact hU.mem_nhds hh
    filter_upwards [hev] with t ht
    exact he _ ht (WeylGroupFacts.uh_mul (B5.exp_mem hX t) hhG)
  rw [hloc]
  exact gp_ldV X h F hd

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
