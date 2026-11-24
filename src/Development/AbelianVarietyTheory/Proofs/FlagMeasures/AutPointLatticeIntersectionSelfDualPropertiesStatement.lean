module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
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

@[expose] public section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.autPointLatticeIntersection_selfDual_properties : ∀ (I : AutInst) (x : I.GA), (∀ y, y ∈ lamX I x ↔ I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf) ∧ (lamX I x).FG ∧ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) = ⊤ ∧ (∀ y, y ∈ lamX I x ↔ ∀ z ∈ lamX I x, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ ∀ k : I.GA, k.2 ∈ I.Kset → lamX I (x * k) = lamX I x := by
  first | exact @GlobalTheory.PointLattice.lamX_selfDual | exact GlobalTheory.PointLattice.lamX_selfDual | (intros; apply GlobalTheory.PointLattice.lamX_selfDual <;> assumption)
