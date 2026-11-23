module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjDualPartsKilledOfPerfectPairing
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.conj_dual_parts_killed_of_perfect_pairing : ∀ (O : Type) [CommRing O] (bar : O →+* O) (U : Type) [CommRing U] [IsDomain U] (M M' : Type) [CommGroup M] [CommGroup M'] (α : O → M →* M) (α' : O → M' →* M'), (∀ y, α 1 y = y) → (∀ a b y, α (a * b) y = α a (α b y)) → (∀ a b y, α (a + b) y = α a y * α b y) → (∀ x, α' 1 x = x) → (∀ a b x, α' (a * b) x = α' a (α' b x)) → (∀ a b x, α' (a + b) x = α' a x * α' b x) → (∀ a, bar (bar a) = a) → ∀ (e : M' →* M →* Uˣ) (e' : M →* M' →* Uˣ), Function.Injective e → Function.Injective e' → (∀ a x y, e (α' a x) y = e x (α (bar a) y)) → (∀ a y x, e' (α a y) x = e' y (α' (bar a) x)) → ∀ (u w : Ideal O) (n : ℕ), u ≤ w → u ⊔ u.map bar = ⊤ → (∀ a ∈ (u * u.map bar) ^ n, (∀ y, α a y = 1) ∧ ∀ x, α' a x = 1) → (∀ y, (∃ m : ℕ, ∀ a ∈ u ^ m, α a y = 1) → ∀ a ∈ w, α a y = 1) → Finite {y : M // ∀ a ∈ w, α a y = 1} → (∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1) ∧ Nat.card {x : M' // ∀ a ∈ w.map bar, α' a x = 1} = Nat.card {y : M // ∀ a ∈ w, α a y = 1} := by
  first | (exact @GlobalTheory.DualParts.conj_dual_parts) | (exact GlobalTheory.DualParts.conj_dual_parts) | (intros; apply GlobalTheory.DualParts.conj_dual_parts <;> assumption)
