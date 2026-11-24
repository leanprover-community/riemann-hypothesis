module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericSeriesSquarefreeLabels
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_genericSeries_squarefreeLabels : GlobalTheory.GLq.Green → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (n : ℕ), 5 ≤ g → 0 < n → ∃ τ : (ZMod g)[X] → GlobalTheory.BadShare.GG g n → ℂ, GlobalTheory.BadShare.IsSeries τ ∧ ∀ f ∈ GlobalTheory.BadShare.sqSet g n, ∀ x, (GlobalTheory.GLq.eSerC L n f).coeff x = GlobalTheory.BadShare.zc (τ f) x := by
  first | exact @GlobalTheory.GLq.SqSeries.exists_series | exact GlobalTheory.GLq.SqSeries.exists_series | (intros; apply GlobalTheory.GLq.SqSeries.exists_series <;> assumption)
