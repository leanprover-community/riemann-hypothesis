module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerComplexLiftAndExtensionLemmas
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

@[expose] public section

open CategoryTheory GlobalTheory.CxCoh

theorem _root_.GlobalTheory.T.tower_complex_lift_and_extension_lemmas : (∀ (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n (c n x) = 0) → (∀ n x, s n (c (n + 1) x) = c n (r n x)) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (r n)) → (∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w) → ∀ b : ∀ n, B n, (∀ n, t n (b (n + 1)) = b n) → (∀ n, ∃ a, d n a = b n) → ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n) ∧ ∀ (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n x ∈ Z n) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (s n)) → (∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) → (∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) → ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n := by
  first | exact @GlobalTheory.TowerLift.tower_lemmas | exact GlobalTheory.TowerLift.tower_lemmas | (intros; apply GlobalTheory.TowerLift.tower_lemmas <;> assumption)
