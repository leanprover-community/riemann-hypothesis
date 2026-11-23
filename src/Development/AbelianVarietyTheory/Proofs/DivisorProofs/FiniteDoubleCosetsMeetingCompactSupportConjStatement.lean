module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Support
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetsMeetingCompactSupportConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finite_doubleCosets_meeting_compact_support_conj : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G) (y : G) (f : G → ℂ), IsCompact (K : Set G) → HasCompactSupport f → (∀ C : Set G, IsCompact C → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite) → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * y * (Quotient.out q * k)) ≠ 0}.Finite := by
  first | exact @GlobalTheory.doubleCoset_finite_of_compactSupport | exact GlobalTheory.doubleCoset_finite_of_compactSupport | (intros; apply GlobalTheory.doubleCoset_finite_of_compactSupport <;> assumption)
