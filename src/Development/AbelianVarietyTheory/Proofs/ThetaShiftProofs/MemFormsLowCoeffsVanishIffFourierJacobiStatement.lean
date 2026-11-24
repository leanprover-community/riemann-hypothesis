module

public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobi
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem _root_.GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), InR D j → j < D.R.m → ∀ F : (recB h).Cusp j ka, (∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA ka) ka.n k)) ∧ (F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka ↔ ∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) := by
  first | exact @GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish | exact GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish | (intros; apply GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish <;> assumption)
