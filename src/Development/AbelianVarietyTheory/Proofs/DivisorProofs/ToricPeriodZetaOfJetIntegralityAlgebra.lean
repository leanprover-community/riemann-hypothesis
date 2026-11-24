module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHeckeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityUnramifiedOfJetIntegralitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorialInvLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfLatticeValueStatementsStatement
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

theorem GlobalTheory.JoinFun.joinOut_of_jetInt : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatJet.JetInt → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  intro hEM hHCF hSKDR hPZ hHT hJetInt hLatAlg hLatConj
  have hS44 := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke (GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ)
  exact GlobalTheory.T.toricPeriodZeta_of_latticeValue_statements hEM hHCF hSKDR hHT (GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion hS44 (GlobalTheory.JetExp.expansion_of_jetInt hJetInt))
    (GlobalTheory.T.latticeValueIntegrality_unramified_of_jetIntegrality hS44 hJetInt) hLatAlg hLatConj
