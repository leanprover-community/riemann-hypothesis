module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StdSteps

theorem even_N (R : Ranks) (j : ℕ) : Even (R.N j) :=
  R.k_even.add (R.t_odd.add_one.mul_left j)

theorem N_lt_succ (R : Ranks) (j : ℕ) : R.N j < R.N (j + 1) := by
  unfold Ranks.N
  rw [Nat.add_mul]
  omega

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (D : D7) (h : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  rw [Host.xi0, h, Ideal.absNorm_top, map_div₀, map_neg, map_one, map_mul, h1, Nat.cast_one, map_one, one_mul, Complex.ofReal_inv]
  field_simp
  rw [Complex.I_sq]

theorem scale_eq (D : D7) {δ : ℂ} (hδ : δ ≠ 0) :
    (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D ⊤ δ))⁻¹ * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹ := by
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ‖δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
  rw [GlobalTheory.MomDict.area_lamOf D ⊤ δ top_ne_bot, Ideal.absNorm_top, Complex.normSq_eq_norm_sq]
  field_simp
  simp

end GlobalTheory.AdForm.StdSteps
