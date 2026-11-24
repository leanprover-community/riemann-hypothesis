module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStabIffIsKStableOnFiniteVectors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.kStab_iff_isKStableOn_finite_vectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ U : Submodule ℂ D, FiniteDimensional ℂ U → (KStab ε E U ↔ IsKStableOn ε σ (U.map D.subtype)) := by
  first | exact @GlobalTheory.KFinStab.kStab_iff_kStableOn | exact GlobalTheory.KFinStab.kStab_iff_kStableOn | (intros; apply GlobalTheory.KFinStab.kStab_iff_kStableOn <;> assumption)
