module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLocalEigenGaloisPolynomialSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem _root_.GlobalTheory.T.pointLocalEigen_galoisPolynomial_split : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → Formalism.L2.HeckeRational D M → Formalism.L2.AVTied D M → Formalism.L2.NormalizedLocalCompatibility D M → ∀ i : D.nd.Loc, (∀ (P : D.naut.AV i) (w : PlE D.host), SplitOut D.nd i w → ∃ lam : ℕ → ℂ, galPol D.naut (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) = X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV, C ((-1) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (D.R.nV - k) ∧ ∀ (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host w s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P, Formalism.L2.NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = lam k • (M.loc i).real y) → GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  first | exact @GlobalTheory.PtLocalEig.main | exact GlobalTheory.PtLocalEig.main | (intros; apply GlobalTheory.PtLocalEig.main <;> assumption)
