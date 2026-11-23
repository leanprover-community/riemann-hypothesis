module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCorrectionNextLevel
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

open MvPolynomial

theorem _root_.GlobalTheory.T.homogeneous_correction_next_level_alt : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ i, ∃ N : ℕ, (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F ∈ K e) → F ∈ K e) → (∀ e, ∀ a ∈ I ^ (e + 1), C a ∈ K e) → (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ I ^ (e + 1)) ∧ (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F - G ∈ K (e + 1)) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1) := by
  first | exact @GlobalTheory.homogeneous_correction_next_level | exact GlobalTheory.homogeneous_correction_next_level | (intros; apply GlobalTheory.homogeneous_correction_next_level <;> assumption)
