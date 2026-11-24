module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.topDegreeFormCoeff_linearSubst_eq_absDet_sq_mul : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ), topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) P) = J.det * starRingEnd ℂ J.det * topCoeff P := by
  first | exact @GlobalTheory.GoodMetric.topCoeff_subst_conj | exact GlobalTheory.GoodMetric.topCoeff_subst_conj | (intros; apply GlobalTheory.GoodMetric.topCoeff_subst_conj <;> assumption)
