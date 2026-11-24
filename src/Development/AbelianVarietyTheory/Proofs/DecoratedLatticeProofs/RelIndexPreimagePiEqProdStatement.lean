module

public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProd
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

@[expose] public section


theorem _root_.GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi : ∀ {G : Type} [Group G] {r : ℕ} {H : Fin r → Type} [∀ i, Group (H i)] (φ : G →* ((i : Fin r) → H i)) (U U' : Subgroup G) (K J : (i : Fin r) → Subgroup (H i)), (∀ i, J i ≤ K i) → (∀ g ∈ U, ∀ i, φ g i ∈ K i) → (∀ x : (i : Fin r) → H i, (∀ i, x i ∈ K i) → ∃ g ∈ U, φ g = x) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i) → U'.relIndex U = ∏ i, (J i).relIndex (K i) := by
  first | exact @GlobalTheory.relIndex_preimage_pi_eq_prod | exact GlobalTheory.relIndex_preimage_pi_eq_prod | (intros; apply GlobalTheory.relIndex_preimage_pi_eq_prod <;> assumption)
