module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTransvectionMovesLatticeAtPrime
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.unitaryTransvection_moves_lattice_at_prime : ∀ (D : D7) (n q : ℕ) (P : Ideal (𝓞 D.host.E)), (∀ a ∈ P, sgO D a ∈ P) → ∀ (M : Lat D n) (b x : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) → (∀ y ∈ M, IntE D (hE D y (b + x))) → IntE D (hE D (b + x) (b + x)) → lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x) (b + x) = 0 → Nat.Coprime m q → (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) → (∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x)) = (p : D.host.E)) → ∃ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (M ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
  first | exact @GlobalTheory.UnitaryTransvection.transvection | exact GlobalTheory.UnitaryTransvection.transvection | (intros; apply GlobalTheory.UnitaryTransvection.transvection <;> assumption)
