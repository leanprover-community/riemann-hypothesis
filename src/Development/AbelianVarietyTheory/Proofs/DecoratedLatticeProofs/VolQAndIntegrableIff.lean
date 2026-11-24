module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuotFundDom

theorem volQ_and_integrable_iff : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν = (ν X).toReal ∧ ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → (Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F) (GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) ↔ IntegrableOn F X ν) := by
  intro D V ν X hν hX
  refine ⟨?_, fun F hF _ => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, Measure.real, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hX]
  · have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F := hF
    rw [← memLp_one_iff_integrable, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hX, hL.lift_descend,
      memLp_one_iff_integrable]
    rfl

end GlobalTheory.QuotFundDom
