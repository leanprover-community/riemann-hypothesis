module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FixedOfForallLocalSubgroupFixedFiniteAdelic
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

theorem _root_.GlobalTheory.T.fixed_of_forall_localSubgroup_fixed_finiteAdelic : ∀ (D : D7) (V : HSp D) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, K' v ≤ Kv V v) → ∀ x : W, (∀ v, ∀ k ∈ K' v, σ (locFin V v k) x = x) → ∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x := by
  first | exact @GlobalTheory.TrIdem.fixed_of_forall_finLoc_mem | exact GlobalTheory.TrIdem.fixed_of_forall_finLoc_mem | (intros; apply GlobalTheory.TrIdem.fixed_of_forall_finLoc_mem <;> assumption)
