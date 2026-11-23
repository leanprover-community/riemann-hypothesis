module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFrameToRealLieAlgebraSpec
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjFrameToRealLieAlgebra_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ Z ∈ GlobalTheory.HolRead.unitLie C.X, (∀ ρ, (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z ρ).1 = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) ∧ GlobalTheory.AdSpan.ConjHol.toLieC C R B (I • Z) = 0 := by
  first | exact @GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec | exact GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec | (intros; apply GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec <;> assumption)
