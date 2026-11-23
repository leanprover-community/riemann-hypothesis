module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharacters
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.admissible_irreducible_torus_characters : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → ∀ (D : D7) (V : HSp D) (U : AuxiliaryPlaceHermitianSpace V) (μ : Measure (Gv V U.u)), μ.IsHaarMeasure → ∀ (n : ℕ) (N : Fin n → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (π : ∀ i, Representation ℂ (Gv V U.u) (N i)), (∀ i, (π i).IsIrreducible) → (∀ i, IsAdmissible (π i)) → ∀ d : Fin n → ℂ, (∀ t ∈ strictTorus V.rank U.ϖ, ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) (U.frame.cosetFn t) (b i)) → ∑ i, d i * b i = 0) → ∀ f ∈ CcLoc D.sp.cm.sig V.gram U.u, (∀ k ∈ U.frame.iwahori, ∀ g, f (k * g) = f g) → ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) f (b i)) → ∑ i, d i * b i = 0 := by
  first | exact @GlobalTheory.IwahoriRel.relation_of_iwahoriTrace | exact GlobalTheory.IwahoriRel.relation_of_iwahoriTrace | (intros; apply GlobalTheory.IwahoriRel.relation_of_iwahoriTrace <;> assumption)
