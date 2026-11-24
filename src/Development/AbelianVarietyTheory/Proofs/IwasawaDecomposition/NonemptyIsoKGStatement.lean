module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoKG
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.nonempty_isoKG_of_trace_positive : ∀ (K E : Type) [Field K] [CharZero K] [Field E] [Algebra K E] [FiniteDimensional K E] (cj : E →+* E) (σ : K →+* K) (ι : Type) [Fintype ι], Fintype.card ι = Module.finrank K E → (∀ x, cj (algebraMap K E x) = algebraMap K E (σ x)) → (∀ y, cj (cj y) = y) → (∀ y, Algebra.trace K E (cj y) = σ (Algebra.trace K E y)) → (∀ y, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace K E (y * cj y) = (a : K)) → Nonempty (IsoKG K E cj ι) := by
  first | exact @GlobalTheory.FourCopiesIso.nonempty_isoKG | exact GlobalTheory.FourCopiesIso.nonempty_isoKG | (intros; apply GlobalTheory.FourCopiesIso.nonempty_isoKG <;> assumption)
