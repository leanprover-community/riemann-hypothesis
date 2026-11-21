import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonneAt
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot

noncomputable section

open CategoryTheory WittVector Ideal TensorProduct Coalgebra

namespace GlobalTheory.PrismModel

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

section Eps

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

private theorem zeta_add_pow_p_pow_eq_zeta (ε : PreTilt O p) (n k : ℕ) :
    zeta ε (n + k) ^ p ^ k = zeta ε n := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, zeta_succ_pow, ih]

theorem isPrimitiveSystem_of_one {ε : PreTilt O p} (h : IsPrimitiveRoot (zeta ε 1) p) :
    IsPrimitiveSystem ε := by
  intro n
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    have h0 := zeta_add_pow_p_pow_eq_zeta ε 0 1
    rw [zero_add, pow_one] at h0
    rw [← h0, h.pow_eq_one]
  | succ n =>
    have h1 : zeta ε (n + 1) ^ p ^ n = zeta ε 1 := by
      have h2 := zeta_add_pow_p_pow_eq_zeta ε 1 n
      rwa [add_comm 1 n] at h2
    rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [h1]
      exact h.ne_one (Fact.out : p.Prime).one_lt
    · rw [pow_succ, pow_mul, h1, h.pow_eq_one]

theorem frobenius_mu (ε : PreTilt O p) :
    frobenius (Sandwich.mu ε) = frobenius (xi ε) * Sandwich.mu ε := by
  have key : frobenius (Sandwich.nu ε) = Sandwich.mu ε := by
    rw [Sandwich.nu, map_sub, map_one, frobenius_eq_map_frobenius, map_teichmuller, Sandwich.root,
      frobenius_apply_frobeniusEquiv_symm]
    rfl
  conv_lhs => rw [← xi_mul_nu ε]
  rw [map_mul, key]

theorem theta_xi [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    fontaineTheta O p (xi ε) = 0 := by
  have h1 := hε 1
  rw [pow_one] at h1
  rw [xi, map_sum]
  simp only [map_pow, fontaineTheta_teichmuller]
  exact h1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt

end Eps


theorem exists_system (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C]
    [NormedAlgebra ℚ_[p] C] [IsAlgClosed C] (O : Type) [CommRing O] [Algebra O C]
    (H : IsIntegers O C) [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] :
    ∃ ε : PreTilt O p, IsPrimitiveSystem ε := by
  have : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : CharZero C := (RingHom.charZero_iff (algebraMap ℚ_[p] C).injective).mp inferInstance
  have hv : (NormedField.valuation (K := C)).Integers O :=
    { hom_inj := H.inj
      map_le_one := fun a => by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnnorm]
        exact (H.mem_iff _).1 ⟨a, rfl⟩
      exists_of_le_one := fun r hr => by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnnorm] at hr
        exact (H.mem_iff r).2 hr }
  obtain ⟨ε, hε⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) C NormedField.valuation O hv
  exact ⟨ε, isPrimitiveSystem_of_one hε⟩


section Mu

variable {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A]







variable {p : ℕ} [Fact p.Prime]





end Mu

end GlobalTheory.PrismModel
