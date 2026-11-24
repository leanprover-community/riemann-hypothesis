module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemExtSubSpanDepth
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspConv

theorem isCuspFun_convR_lift : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ,
    F ∈ GlobalTheory.Cusp.L2cusp V μ → IsCuspFun V (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) := by
  intro D V μ _ _ f hf F hF
  obtain ⟨hc, hs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have h := (GlobalTheory.CuspAE.mem_L2cusp_iff_isCuspAE D V μ F).1 hF
  have hl := (GlobalTheory.AutomorphicL2Unitary.leftInv_lift (Γ := GQ V) F).convR (μ := μ) f
  refine GlobalTheory.Cusp.isCuspFun_of_forall_flag hl fun 𝔉 h𝔉 => funext fun x => ?_
  refine (GlobalTheory.CuspAE.constTermOn_convR (GlobalTheory.Cusp.cocompact_flag D V 𝔉) (GlobalTheory.AutomorphicL2Unitary.leftInv_lift _)
    ((Lp.stronglyMeasurable F).comp_measurable GlobalTheory.AutomorphicL2Unitary.measurable_mk) (GlobalTheory.CuspAE.locallyIntegrable_lift F)
    hc hs x).trans ?_
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (h 𝔉 h𝔉)] with y hy
  exact mul_eq_zero_of_right _ hy

end GlobalTheory.CuspConv
