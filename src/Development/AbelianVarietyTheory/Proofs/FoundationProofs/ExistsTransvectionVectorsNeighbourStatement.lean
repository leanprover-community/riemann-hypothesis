module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTransvectionVectorsNeighbour
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_transvection_vectors_neighbour : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → (q : 𝓞 D.host.E) ∈ P → (∀ a ∈ P, sgO D a ∈ P) → ∀ (B : Lat D n) (x : Fin n → D.host.E), SD D B → NbD D P B x → ∃ (b x' : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), B = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {b} ∧ nbr D B x = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {x'} ∧ (∀ p ∈ P, p • b ∈ nbM D B x ∧ p • x' ∈ nbM D B x) ∧ ¬ IntE D (hE D b x') ∧ NbD D P B (b + x') ∧ nbM D B (b + x') = nbM D B x ∧ lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x') (b + x') = 0 ∧ Nat.Coprime m q ∧ (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) ∧ ∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x')) = (p : D.host.E) := by
  first | exact @GlobalTheory.NbVec.exists_vectors | exact GlobalTheory.NbVec.exists_vectors | (intros; apply GlobalTheory.NbVec.exists_vectors <;> assumption)
