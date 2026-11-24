module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepCommutesSliceSuperpositionTarget
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weilRep_commutes_slice_superposition_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resT S).symm (u, k w))) u₀ ∂μ := by
  first | exact @GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target | exact GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target | (intros; apply GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target <;> assumption)
