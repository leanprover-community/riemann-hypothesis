module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LinearIndependentE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemStandardLeviWittFrame
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
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
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct


theorem _root_.GlobalTheory.T.conj_mem_standardLevi_wittFrame : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) (γ g : GF V) {a : ℕ} (ha : a ≤ wittIndex V) (j : Fin (wittIndex V)), j.val + 1 = a → ∀ (x x' : Fin a → V.V), (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i)) → (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i)) → (∀ v ∈ Submodule.span D.host.E (Set.range x), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x)) → (∀ v ∈ Submodule.span D.host.E (Set.range x'), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x')) → rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) {stdVec j} := by
  first | exact @GlobalTheory.Cusp.ConjLevi.conj_mem_levi_stdVec | exact GlobalTheory.Cusp.ConjLevi.conj_mem_levi_stdVec | (intros; apply GlobalTheory.Cusp.ConjLevi.conj_mem_levi_stdVec <;> assumption)
