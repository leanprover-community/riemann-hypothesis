module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FilPEqSpanBetaDPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.filP_eq_span_betaD_pow_of_kerP_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  first | exact @GlobalTheory.Pst.StLat.filtration_eq_span_pow | exact GlobalTheory.Pst.StLat.filtration_eq_span_pow | (intros; apply GlobalTheory.Pst.StLat.filtration_eq_span_pow <;> assumption)
