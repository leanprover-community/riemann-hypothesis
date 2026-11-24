module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDividedPowerJetIntegralityOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueConjugationOfEllipticCMTheoremsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIsAlgebraicOfEllipticCMTheoremsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaStatementsOfJetIntegralityAlgebraStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

theorem GlobalTheory.JoinFun.joinOut_of_five : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.Mem.LiteralAutomorphy.JoinOut :=
  fun hEM hHJ hSK hPZ hHT => GlobalTheory.T.toricPeriodZetaStatements_of_jetIntegrality_algebraicity hEM hHJ hSK hPZ hHT (GlobalTheory.T.cmLatticeDividedPowerJetIntegrality_of_ellipticCM hSK hPZ hHJ hEM)
    (GlobalTheory.T.latticeValueIsAlgebraic_of_ellipticCM_theorems hSK hPZ hHJ hEM) (GlobalTheory.T.latticeValueConjugation_of_ellipticCM_theorems hSK hPZ hHJ hEM)
