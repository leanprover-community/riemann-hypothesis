module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesModelHolomorphicPositiveSignsFirst
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

theorem _root_.GlobalTheory.T.discreteSeriesModel_holomorphic_positiveSignsFirst : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ), (∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ) → ∀ (i : Fin D.R.m) (M : DSModel (Wc D i) (Formalism.IndefR.Links.parAt (Wc D i) σ)), GlobalTheory.HolDict.HolShape M ∧ (∃ wt, GlobalTheory.HolDict.WtIs M wt) ∧ ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < pW D i ρ) := by
  first | exact @GlobalTheory.HolLabel.holShape_signs_first | exact GlobalTheory.HolLabel.holShape_signs_first | (intros; apply GlobalTheory.HolLabel.holShape_signs_first <;> assumption)
