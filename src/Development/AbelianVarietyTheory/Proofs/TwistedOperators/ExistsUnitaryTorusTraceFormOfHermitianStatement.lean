module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryTorusTraceFormOfHermitian
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix


theorem _root_.GlobalTheory.T.exists_unitaryTorus_traceForm_of_hermitian : ∀ (F E : Type) [Field F] [Field E] [CharZero E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (P : PPol σ n) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (A : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) A * J * A = J → ∀ φ : Fld P ≃ₗ[E] (Fin n → E), (∀ y, A *ᵥ φ y = φ (alpha P * y)) → ∃ x : Fld P, x ≠ 0 ∧ star' P x = x ∧ ∀ y y', Formalism.UG.hform (σ : E →+* E) J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y') := by
  first | exact @GlobalTheory.TrEll.HermTrace.exists_trace_form | exact GlobalTheory.TrEll.HermTrace.exists_trace_form | (intros; apply GlobalTheory.TrEll.HermTrace.exists_trace_form <;> assumption)
