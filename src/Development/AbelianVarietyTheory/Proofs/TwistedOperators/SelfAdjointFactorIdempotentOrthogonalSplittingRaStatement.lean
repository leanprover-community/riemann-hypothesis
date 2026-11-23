module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LinearIndependentE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRa
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

theorem _root_.GlobalTheory.T.selfAdjointFactorIdempotent_orthogonal_splitting_rank : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)] (e : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) (i : Fin k), GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i).rank = Module.finrank D.host.E (TensorProduct D.host.F D.host.E (Kf i)) := by
  first | exact @GlobalTheory.FactorSplit.factorIdem_orthSplit_rank | exact GlobalTheory.FactorSplit.factorIdem_orthSplit_rank | (intros; apply GlobalTheory.FactorSplit.factorIdem_orthSplit_rank <;> assumption)
