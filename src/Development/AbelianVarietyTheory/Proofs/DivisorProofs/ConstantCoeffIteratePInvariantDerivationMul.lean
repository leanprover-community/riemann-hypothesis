module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawLeibniz
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
public import Mathlib.Data.Nat.Choose.Dvd
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

open MvPowerSeries in
set_option autoImplicit false in
private lemma iterate_mul_eq_sum_antidiagonal_choose {A : Type} [CommRing A] (D : A → A)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hmul : ∀ a b, D (a * b) = D a * b + a * D b) (n : ℕ)
    (a b : A) :
    D^[n] (a * b) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • (D^[ij.1] a * D^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → A), D (∑ x ∈ s, f x) = ∑ x ∈ s, D (f x) :=
      fun s f => map_sum (AddMonoidHom.mk' D hadd) f s
    have hns : ∀ (m : ℕ) (x : A), D (m • x) = m • D x :=
      fun m x => map_nsmul (AddMonoidHom.mk' D hadd) m x
    have hc := Finset.sum_antidiagonal_choose_succ_nsmul (fun i j => D^[i] a * D^[j] b) n
    beta_reduce at hc
    rw [Function.iterate_succ_apply', ih, hsum, hc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [← Nat.choose_symm_of_eq_add hij.symm, hns, hmul, ← smul_add]
    simp only [Function.iterate_succ_apply']
    rw [add_comm]


set_option autoImplicit false in
theorem _root_.GlobalTheory.LawDer.constantCoeff_iterate_invDer_mul : ∀ (p : ℕ) [Fact p.Prime] (R : Type)
    [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) →
    _root_.GlobalTheory.Katz.op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) =
      (fun i => X i) →
    ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), constantCoeff F = 0 → constantCoeff G = 0 →
      ∃ r : R, constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[p] (F * G)) = p * r := by
  intro p hp R _ d μ hμ hid u F G hF hG
  have hlin := _root_.GlobalTheory.LawDer.Linear.invDer_linear R d μ hμ u

  rw [iterate_mul_eq_sum_antidiagonal_choose _ hlin.1
  (_root_.GlobalTheory.LawDer.invDer_mul R d μ hμ hid u), map_sum]
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rw [map_nsmul, map_mul, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos ij.1 with h1 | h1
  · rw [h1, Function.iterate_zero, id, hF]; simp
  rcases Nat.eq_zero_or_pos ij.2 with h2 | h2
  · rw [h2, Function.iterate_zero, id, hG]; simp
  have hdvd : p ∣ p.choose ij.1 := hp.out.dvd_choose_self h1.ne' (by omega)
  exact Dvd.dvd.mul_right (Nat.cast_dvd_cast hdvd) _

end GlobalTheory.LawDer
