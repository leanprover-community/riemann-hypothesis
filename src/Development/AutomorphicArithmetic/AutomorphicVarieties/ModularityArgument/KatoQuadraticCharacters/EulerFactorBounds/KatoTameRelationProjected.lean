import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopCocG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoNormRelationTwistTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SXiCoh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiDist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoNormRelationTamePrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.TraceHeckeCongruenceVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.MemAOfPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SInteg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvMemO
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymEx
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.MlTRedCoe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral

section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem frac_eq (D D' : ℕ) [NeZero D] (h : D' = D) (a : ℤ) :
    ∃ j : ℤ, (a : ℚ) / (D' : ℚ) = (((a : ZMod D).val : ℕ) : ℚ) / D + j := by
  subst h
  refine ⟨a / (D' : ℤ), ?_⟩
  have h1 : ((((a : ZMod D').val : ℕ) : ℤ)) = a % (D' : ℤ) := ZMod.val_intCast a
  have h2 : (((a : ZMod D').val : ℕ) : ℚ) = ((a % (D' : ℤ) : ℤ) : ℚ) := by
    rw [← h1]
    push_cast
    rfl
  have hD : (D' : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne D'
  have e : a % (D' : ℤ) = a - (D' : ℤ) * (a / (D' : ℤ)) := Int.emod_def a D'
  rw [h2, e]
  push_cast
  field_simp
  ring

private theorem two_ne (l D : ℕ) [Fact l.Prime] (hl : l ≠ 2) (hD : l ∣ D) (a : ℤ) (ha : (a : ZMod l) ≠ 0) :
    (2 : ZMod D) * (a : ZMod D) ≠ 0 := by
  intro h0
  have h1 := congrArg (ZMod.castHom hD (ZMod l)) h0
  simp only [map_mul, map_ofNat, map_intCast, map_zero] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have h3 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h3)
  · exact ha h2

private theorem bar_mul (l L N p : ℕ) (hL : L ≠ 0) (h : Nat.Coprime p (N * l ^ L)) :
    ((bar l L N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := by
  by_cases hM : N * l ^ L = 0
  · have hp : p = 1 := by
      simpa [hM] using h
    subst hp
    have hv : ((1 : ZMod (N * l ^ L))⁻¹).val = 1 := by
      rw [ZMod.inv_one, ZMod.val_one'' (by omega)]
    simp only [bar, Nat.cast_one, hv, Int.cast_one, mul_one]
  · haveI : NeZero (N * l ^ L) := ⟨hM⟩
    have hdvd : l ∣ N * l ^ L := Dvd.dvd.mul_left (dvd_pow_self l hL) N
    have hu : ((p : ZMod (N * l ^ L)) * (p : ZMod (N * l ^ L))⁻¹) = 1 := ZMod.coe_mul_inv_eq_one p h
    have h1 := congrArg (ZMod.castHom hdvd (ZMod l)) hu
    rw [map_mul, map_one, map_natCast] at h1
    have h2 : ((bar l L N p : ℤ) : ZMod l) = ZMod.castHom hdvd (ZMod l) ((p : ZMod (N * l ^ L))⁻¹) := by
      unfold bar
      rw [Int.cast_natCast, ZMod.natCast_val]
      rfl
    rw [h2, mul_comm]
    exact h1

theorem UpperTheory.V.Z.Kato.Nb.sTopT :
    UpperTheory.V.Z.Kato.Nb.STopT := by
  intro Ω _ _ _ ε X l _ N p _ _ x c d w g hH hP hcop hLw hLift n r
  obtain ⟨ws, hws⟩ := hLw
  have api := sApi Ω ε X l
  have inv := sInvApi Ω ε X l N w
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨fun σ _ => (inv 0).2.2.2.2.2.2.1 _, fun σ _ τ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _,
      ⟨∅, fun σ _ τ _ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _⟩⟩
  · have hl2 : l ≠ 2 := hH.odd
    have hlp : l.Prime := Fact.out
    have hL0 : r + n ≠ 0 := by omega
    have hpl : p.Coprime l := Nat.Coprime.coprime_dvd_right ⟨N * c * d, by ring⟩ hcop
    have hpN : p.Coprime N := Nat.Coprime.coprime_dvd_right ⟨l * c * d, by ring⟩ hcop
    have hpc : p.Coprime c := Nat.Coprime.coprime_dvd_right ⟨l * N * d, by ring⟩ hcop
    have hpNL : p.Coprime (N * l ^ (r + n)) := Nat.Coprime.mul_right hpN (Nat.Coprime.pow_right _ hpl)
    have hcN : c.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hH.cc
    have hcl : c.Coprime l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hH.cc
    have hdN : d.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hH.cd
    have hdl : d.Coprime l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hH.cd
    have hpd : p.Coprime d := Nat.Coprime.coprime_dvd_right ⟨l * N * c, by ring⟩ hcop
    have hM0 : N * l ^ (r + n) * p ≠ 0 :=
      mul_ne_zero (mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hlp.ne_zero)) (NeZero.ne p)
    haveI : NeZero (N * l ^ (r + n) * p) := ⟨hM0⟩
    have hMeq : lvT l n r N p = N * (N * l ^ (r + n) * p) := by
      unfold lvT
      ring
    haveI : NeZero (lvT l n r N p) := ⟨by rw [hMeq]; exact mul_ne_zero (NeZero.ne N) hM0⟩
    have hLev : Lev l n N (N * l ^ (r + n) * p) (lvT l n r N p) g :=
      ⟨hMeq, ⟨l ^ (r + n) * p, by ring⟩, ⟨N * l ^ r * p, by ring⟩, hn, hH.cop, hH.g0⟩
    have hLv : Lv c d (N * l ^ (r + n) * p) :=
      ⟨Nat.pos_of_ne_zero hM0,
        Nat.Coprime.mul_right (Nat.Coprime.mul_right hcN (Nat.Coprime.pow_right _ hcl)) hpc.symm,
        Nat.Coprime.mul_right (Nat.Coprime.mul_right hdN (Nat.Coprime.pow_right _ hdl)) hpd.symm⟩
    have hdvdl : l ∣ N * l ^ (r + n) * p := Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self l hL0) N) p
    have hbp : ((bar l (r + n) N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := bar_mul l (r + n) N p hL0 hpNL
    have hlL : ((l : ZMod l)) ^ (r + n) = 0 := by
      rw [ZMod.natCast_self]
      exact zero_pow hL0
    have hN0 : (N : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hlp).mp hH.cop
    have ha0 : (((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) ≠ 0 := by
      have e : (((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) = (N : ZMod l) := by
        push_cast
        linear_combination (N : ZMod l) * hbp + (((bar l (r + n) N p : ℤ) : ZMod l) * ((x.val : ℕ) : ZMod l) * ((topT l (r + n) N : ℕ) : ZMod l) * (p : ZMod l) + (N : ZMod l)) * hlL
      rw [e]
      exact hN0
    have hb1 : (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) ≠ 0 := by
      have e : (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) = (N : ZMod l) := by
        push_cast
        linear_combination (N : ZMod l) * hbp + (N : ZMod l) * hlL
      rw [e]
      exact hN0
    let x₀ : Row (N * l ^ (r + n) * p) :=
      ![(((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod (N * l ^ (r + n) * p)),
        (((0 : ℤ)) : ZMod (N * l ^ (r + n) * p))]
    let y₀ : Row (N * l ^ (r + n) * p) :=
      ![(((bar l (r + n) N p * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n) * (p : ℤ)) : ℤ) : ZMod (N * l ^ (r + n) * p)),
        (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod (N * l ^ (r + n) * p))]
    have hOk : Ok x₀ y₀ := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h1 := congrFun h 0
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        exact two_ne l _ hl2 hdvdl _ ha0 h1
      · have h1 := congrFun h 1
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        exact two_ne l _ hl2 hdvdl _ hb1 h1
    have hx : ∀ i : Fin 2, ∃ j : ℤ, ixUT l (r + n) N p x i = toQ (N * l ^ (r + n) * p) x₀ i + j := by
      intro i
      fin_cases i
      · exact frac_eq _ _ rfl _
      · exact frac_eq _ _ rfl _
    have hy : ∀ i : Fin 2, ∃ j : ℤ, ixVT l (r + n) N p i = toQ (N * l ^ (r + n) * p) y₀ i + j := by
      intro i
      fin_cases i
      · exact frac_eq _ _ rfl _
      · exact frac_eq _ _ rfl _
    obtain ⟨β, hβ, hcg⟩ := sTopRel Ω ε X l n N (N * l ^ (r + n) * p) (lvT l n r N p) w g hLev hLift c d ws hws hLv
      x₀ y₀ hOk _ _ hx hy
    exact sTopCocG Ω ε X l n N _ _ w g hLev hLift x₀ y₀ hOk (ws n _) (hws.coc n _ hLv) _ β hβ hcg
end

section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.NormOneTraceTorsion

private def rw0 (M : ℕ) (v : Fin 2 → ℤ) : Row M := fun i => (v i : ZMod M)

private theorem val_cast {M D : ℕ} [NeZero M] (h : D ∣ M) (a : ℤ) : (((a : ZMod M).val : ℕ) : ZMod D) = (a : ZMod D) := by
  rw [ZMod.natCast_val, ZMod.cast_intCast h]

private theorem exists_int_div_eq_toQ_rw0_add (M : ℕ) [NeZero M] (v : Fin 2 → ℤ) (i : Fin 2) : ∃ j : ℤ, (v i : ℚ) / (M : ℚ) = toQ M (rw0 M v) i + j := by
  refine ⟨v i / (M : ℤ), ?_⟩
  have hM : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have h1 : (((v i : ZMod M).val : ℕ) : ℤ) = v i % (M : ℤ) := ZMod.val_intCast (v i)
  have h2 : v i % (M : ℤ) + (M : ℤ) * (v i / (M : ℤ)) = v i := Int.emod_add_mul_ediv _ _
  rw [← h1] at h2
  have h3 := congrArg (fun z : ℤ => (z : ℚ)) h2
  push_cast at h3
  simp only [toQ, rw0]
  rw [← h3, add_div, mul_div_cancel_left₀ _ hM]

private theorem dn_rw0_mul_eq_rw0 (k M : ℕ) (v : Fin 2 → ℤ) : dn k M (rw0 (k * M) v) = rw0 M v := by
  funext i
  simp only [dn, rw0, map_intCast]

private theorem two_ne {l M : ℕ} [Fact l.Prime] (hl : l ≠ 2) (h : l ∣ M) (v : Fin 2 → ℤ) (i : Fin 2) (hv : (v i : ZMod l) ≠ 0) :
    (2 : ZMod M) • rw0 M v ≠ 0 := by
  intro h0
  have h1 := congrFun h0 i
  simp only [Pi.smul_apply, smul_eq_mul, rw0, Pi.zero_apply] at h1
  have h2 := congrArg (ZMod.castHom h (ZMod l)) h1
  simp only [map_mul, map_intCast, map_ofNat, map_zero] at h2
  have h3 : (2 : ZMod l) ≠ 0 := by
    intro h4
    have h5 : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).mp (by exact_mod_cast h4)
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h5)
  exact hv ((mul_eq_zero.mp h2).resolve_left h3)

private def rU (l L N p : ℕ) (x : ZMod N) : Fin 2 → ℤ :=
  ![bar l L N p * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) * p + N * (l : ℤ) ^ L, 0]

private def rV (l L N p : ℕ) : Fin 2 → ℤ :=
  ![bar l L N p * (topT l L N : ℤ) * (l : ℤ) ^ L * p, bar l L N p * N * p + N * (l : ℤ) ^ L]

private theorem ixUT_eq (l L N p : ℕ) (x : ZMod N) (i : Fin 2) :
    ixUT l L N p x i = (rU l L N p x i : ℚ) / ((N * l ^ L * p : ℕ) : ℚ) := by
  fin_cases i <;> rfl

private theorem ixVT_eq (l L N p : ℕ) (i : Fin 2) : ixVT l L N p i = (rV l L N p i : ℚ) / ((N * l ^ L * p : ℕ) : ℚ) := by
  fin_cases i <;> rfl

private theorem bar_mul {l L N p D : ℕ} [NeZero (N * l ^ L)] (hp : Nat.Coprime p (N * l ^ L)) (h : D ∣ N * l ^ L) :
    (bar l L N p : ZMod D) * p = 1 := by
  have h1 : (p : ZMod (N * l ^ L)) * (p : ZMod (N * l ^ L))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime p _).mpr hp)
  have h2 := congrArg (ZMod.castHom h (ZMod D)) h1
  simp only [map_mul, map_natCast, map_one] at h2
  simp only [bar]
  push_cast
  rw [ZMod.natCast_val, mul_comm]
  exact h2

private theorem rows_l {l L N p : ℕ} [Fact l.Prime] [NeZero N] (x : ZMod N) (hL : 1 ≤ L) (hp : Nat.Coprime p (N * l ^ L)) :
    (rU l L N p x 0 : ZMod l) = N ∧ (rV l L N p 1 : ZMod l) = N ∧ rU l L N p x 1 = 0 := by
  haveI : NeZero (N * l ^ L) := ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hb : (bar l L N p : ZMod l) * p = 1 := bar_mul hp (Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N)
  have h0 : (l : ZMod l) ^ L = 0 := by rw [ZMod.natCast_self, zero_pow (by omega)]
  refine ⟨?_, ?_, rfl⟩
  · simp only [rU, Matrix.cons_val_zero]
    push_cast
    rw [h0]
    linear_combination (N : ZMod l) * hb
  · simp only [rV, Matrix.cons_val_one, Matrix.cons_val_zero]
    push_cast
    rw [h0]
    linear_combination (N : ZMod l) * hb

private theorem crt {m n : ℕ} (h : Nat.Coprime m n) {a b : ℤ} (h1 : (a : ZMod m) = b) (h2 : (a : ZMod n) = b) :
    (a : ZMod (m * n)) = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1 h2 ⊢
  push_cast
  exact (Nat.isCoprime_iff_coprime.mpr h).mul_dvd h1 h2

private theorem topT_succ {l L N : ℕ} [NeZero N] (h : Nat.Coprime l N) :
    (topT l (L + 1) N : ZMod (N * l ^ L)) * (l : ZMod (N * l ^ L)) ^ (L + 1) = (topT l L N : ZMod (N * l ^ L)) * (l : ZMod (N * l ^ L)) ^ L := by
  have key : ∀ s : ℕ, ((topT l s N : ℕ) : ZMod N) * (l : ZMod N) ^ s = 1 := by
    intro s
    have h1 : ((l ^ s : ℕ) : ZMod N) * ((l ^ s : ℕ) : ZMod N)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr (Nat.Coprime.pow_left s h))
    push_cast at h1
    simp only [topT, ZMod.natCast_zmod_val]
    rw [mul_comm]
    exact h1
  have e := crt (m := N) (n := l ^ L) (Nat.Coprime.pow_right L h.symm)
    (a := (topT l (L + 1) N : ℤ) * (l : ℤ) ^ (L + 1)) (b := (topT l L N : ℤ) * (l : ℤ) ^ L) ?_ ?_
  · push_cast at e
    exact e
  · push_cast
    rw [key, key]
  · push_cast
    have hz : (l : ZMod (l ^ L)) ^ L = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [pow_succ, hz]
    ring

private theorem eval_succ_eq_smul_of_inv_p_of_k_eq_one {R : Type*} [CommRing R] (b1 b0 t1 t0 N l xv p k : R) (L : ℕ)
    (hb1 : b1 * p = 1) (hb0 : b0 * p = 1) (ht : t1 * l ^ (L + 1) = t0 * l ^ L) (hz : N * l ^ L = 0) (k1 : k = 1) :
    b1 * (N + xv * t1 * l ^ (L + 1)) * p + N * l ^ (L + 1) = k * (b0 * (N + xv * t0 * l ^ L) * p + N * l ^ L) := by
  linear_combination (N + xv * t1 * l ^ (L + 1)) * hb1 - (N + xv * t0 * l ^ L) * hb0 + xv * ht + (l - 1) * hz -
    (b0 * (N + xv * t0 * l ^ L) * p + N * l ^ L) * k1

private theorem eval_succ_eq_smul_of_p_eq_zero_of_k_eq_l {R : Type*} [CommRing R] (b1 b0 t1 t0 N l xv p k : R) (L : ℕ)
    (hp : p = 0) (k2 : k = l) :
    b1 * (N + xv * t1 * l ^ (L + 1)) * p + N * l ^ (L + 1) = k * (b0 * (N + xv * t0 * l ^ L) * p + N * l ^ L) := by
  linear_combination (b1 * (N + xv * t1 * l ^ (L + 1)) - k * b0 * (N + xv * t0 * l ^ L)) * hp - N * l ^ L * k2

private theorem twist_succ_eq_smul_of_inv_p_of_k_eq_one {R : Type*} [CommRing R] (b1 b0 t1 t0 l p k : R) (L : ℕ)
    (hb1 : b1 * p = 1) (hb0 : b0 * p = 1) (ht : t1 * l ^ (L + 1) = t0 * l ^ L) (k1 : k = 1) :
    b1 * t1 * l ^ (L + 1) * p = k * (b0 * t0 * l ^ L * p) := by
  linear_combination t1 * l ^ (L + 1) * hb1 + ht - t0 * l ^ L * hb0 - t0 * l ^ L * b0 * p * k1

private theorem twist_succ_eq_smul_of_p_eq_zero {R : Type*} [CommRing R] (b1 b0 t1 t0 l p k : R) (L : ℕ) (hp : p = 0) :
    b1 * t1 * l ^ (L + 1) * p = k * (b0 * t0 * l ^ L * p) := by
  linear_combination (b1 * t1 * l ^ (L + 1) - k * b0 * t0 * l ^ L) * hp

private theorem const_succ_eq_smul_of_inv_p_of_k_eq_one {R : Type*} [CommRing R] (b1 b0 N l p k : R) (L : ℕ)
    (hb1 : b1 * p = 1) (hb0 : b0 * p = 1) (hz : N * l ^ L = 0) (k1 : k = 1) :
    b1 * N * p + N * l ^ (L + 1) = k * (b0 * N * p + N * l ^ L) := by
  linear_combination N * hb1 - N * hb0 + (l - 1) * hz - (b0 * N * p + N * l ^ L) * k1

private theorem const_succ_eq_smul_of_p_eq_zero_of_k_eq_l {R : Type*} [CommRing R] (b1 b0 N l p k : R) (L : ℕ) (hp : p = 0) (k2 : k = l) :
    b1 * N * p + N * l ^ (L + 1) = k * (b0 * N * p + N * l ^ L) := by
  linear_combination (b1 * N - k * b0 * N) * hp - N * l ^ L * k2

private theorem rows_succ {l L N p k : ℕ} [Fact l.Prime] [NeZero N] (x : ZMod N) (h : Nat.Coprime l N)
    (hp : Nat.Coprime p (N * l ^ (L + 1))) (k1 : (k : ZMod (N * l ^ L)) = 1) (k2 : (k : ZMod p) = l) :
    rw0 (N * l ^ L * p) (rU l (L + 1) N p x) = (k : ZMod (N * l ^ L * p)) • rw0 (N * l ^ L * p) (rU l L N p x) ∧
    rw0 (N * l ^ L * p) (rV l (L + 1) N p) = (k : ZMod (N * l ^ L * p)) • rw0 (N * l ^ L * p) (rV l L N p) := by
  haveI : NeZero (N * l ^ (L + 1)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  haveI : NeZero (N * l ^ L) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hdv : N * l ^ L ∣ N * l ^ (L + 1) := Nat.mul_dvd_mul_left N (pow_dvd_pow l (Nat.le_succ L))
  have hp0 : Nat.Coprime p (N * l ^ L) := Nat.Coprime.coprime_dvd_right hdv hp
  have hb1 := bar_mul (D := N * l ^ L) hp hdv
  have hb0 := bar_mul (D := N * l ^ L) hp0 dvd_rfl
  have ht := topT_succ (L := L) h
  have hz : (N : ZMod (N * l ^ L)) * (l : ZMod (N * l ^ L)) ^ L = 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_self]
  have hpz : (p : ZMod p) = 0 := ZMod.natCast_self p
  have c1 : ∀ a b : ℤ, (a : ZMod (N * l ^ L)) = (k : ZMod (N * l ^ L)) * (b : ZMod (N * l ^ L)) →
      (a : ZMod p) = (k : ZMod p) * (b : ZMod p) →
      (a : ZMod (N * l ^ L * p)) = (k : ZMod (N * l ^ L * p)) * (b : ZMod (N * l ^ L * p)) := by
    intro a b h1 h2
    have e := crt hp0.symm (a := a) (b := (k : ℤ) * b) (by push_cast; exact h1) (by push_cast; exact h2)
    rw [e]
    push_cast
    ring
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩ <;> fin_cases i
  · show ((rU l (L + 1) N p x 0 : ℤ) : ZMod (N * l ^ L * p)) = (k : ZMod _) * ((rU l L N p x 0 : ℤ) : ZMod _)
    apply c1 <;> simp only [rU, Matrix.cons_val_zero] <;> push_cast
    · exact eval_succ_eq_smul_of_inv_p_of_k_eq_one _ _ _ _ _ _ _ _ _ L hb1 hb0 ht hz k1
    · exact eval_succ_eq_smul_of_p_eq_zero_of_k_eq_l _ _ _ _ _ _ _ _ _ L hpz k2
  · show ((rU l (L + 1) N p x 1 : ℤ) : ZMod (N * l ^ L * p)) = (k : ZMod _) * ((rU l L N p x 1 : ℤ) : ZMod _)
    simp [rU]
  · show ((rV l (L + 1) N p 0 : ℤ) : ZMod (N * l ^ L * p)) = (k : ZMod _) * ((rV l L N p 0 : ℤ) : ZMod _)
    apply c1 <;> simp only [rV, Matrix.cons_val_zero] <;> push_cast
    · exact twist_succ_eq_smul_of_inv_p_of_k_eq_one _ _ _ _ _ _ _ L hb1 hb0 ht k1
    · exact twist_succ_eq_smul_of_p_eq_zero _ _ _ _ _ _ _ L hpz
  · show ((rV l (L + 1) N p 1 : ℤ) : ZMod (N * l ^ L * p)) = (k : ZMod _) * ((rV l L N p 1 : ℤ) : ZMod _)
    apply c1 <;> simp only [rV, Matrix.cons_val_one, Matrix.head_cons] <;> push_cast
    · exact const_succ_eq_smul_of_inv_p_of_k_eq_one _ _ _ _ _ _ L hb1 hb0 hz k1
    · exact const_succ_eq_smul_of_p_eq_zero_of_k_eq_l _ _ _ _ _ _ L hpz k2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem down (hA : SApi) (hC : SCohApi) (hM : SXiMul) (hX : SXiCoh) (hD : SXiDist) (hS : SXiScal) (hG : SSlD)
    (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M M' w c d : ℕ) [NeZero N] [NeZero M₀] [NeZero M] [NeZero M'] [NeZero (l * M₀)]
    (g : SL(2, ℤ)) (lev : Lev l n N M₀ M g) (hL : LiftsWith X l N w (cL X l N w)) (h : M ∣ M') (e : M' = N * (l * M₀))
    (ws) (law : Laws X l c d ws) (lv : Lv c d (l * M₀)) (x' y' : Row (l * M₀)) (x y : Row M₀) (ok' : Ok x' y') (ok : Ok x y)
    (bas : Bas l N x' y') (ν : (ZMod M)ˣ) (n1 : ((ν : ZMod M).val : ZMod N) = 1) (n2 : ((ν : ZMod M).val : ZMod (l ^ n)) = 1)
    (ex : dn l M₀ x' = ((ν : ZMod M).val : ZMod M₀) • x) (ey : dn l M₀ y' = ((ν : ZMod M).val : ZMod M₀) • y)
    (A : Type) [CommGroup A] (π : (ZMod M)ˣ →* A) :
    CohB X l N w n (fun s => (π (cycM M s))⁻¹)
      (fun s t => Xi X l (n + 1) N (l * M₀) M' w g x' y'
        (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws (n + 1) (l * M₀) s))
      (fun s t => Xi X l n N M₀ M w g x y (fun z => π z = t * π ν ^ 2) (ws n M₀ s)) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hCA := hC Ω ε X l N w n hN A (fun s => (π (cycM M s))⁻¹)
  have hE := hCA.1
  have hAp := hA Ω ε X l n
  have lev' : Lev l n N (l * M₀) M' g :=
    ⟨e, dvd_mul_of_dvd_right lev.dN l, dvd_mul_of_dvd_right lev.dl l, lev.pos, lev.cop, lev.g0⟩
  have hκ : (fun s : Ω ≃ₐ[ℚ] Ω => ((π.comp (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom)) (cycM M' s))⁻¹) =
      (fun s : Ω ≃ₐ[ℚ] Ω => (π (cycM M s))⁻¹) := by
    funext s
    have e4 := ((hG Ω ε X 1 one_pos).2.2.2.2.2.2.2 M' s).2.2.2.2 M h
    exact congrArg (fun u => (π u)⁻¹) e4
  have C1 := hCA.2.1
    (fun s t => Xi X l (n + 1) N (l * M₀) M' w g x' y'
      (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws (n + 1) (l * M₀) s))
    (fun s t => Xi X l n N (l * M₀) M' w g x' y'
      (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws (n + 1) (l * M₀) s))
    (fun s t => (hM Ω ε X l n N (l * M₀) M' w g lev' x' y' ok' _).2.2.1 _)
  have C2 := hX Ω ε X l n N (l * M₀) M' w g lev' hL x' y' ok' A
    (π.comp (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom)) _ _ (law.red n (l * M₀) lv)
  rw [hκ] at C2
  have C3 := hCA.2.1
    (fun s t => Xi X l n N (l * M₀) M' w g x' y'
      (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws n (l * M₀) s))
    (fun s t => Xi X l n N M₀ M w g (((ν : ZMod M).val : ZMod M₀) • x) (((ν : ZMod M).val : ZMod M₀) • y)
      (fun z => π z = t) (pushD X l M₀ (ws n (l * M₀) s)))
    (fun s t => by
      have h3 := hD Ω ε X l n N M₀ M w g lev M' h e x' y' bas (fun z => π z = t) (ws n (l * M₀) s)
      rw [ex, ey] at h3
      exact h3)
  have hdv : ∀ j : ℕ, (l : ℤ_[l]) ^ n ∣ (((ν : ZMod M).val : ℕ) : ℤ_[l]) ^ j - 1 := by
    intro j
    have h1 : ((l ^ n : ℕ) : ℤ) ∣ (((ν : ZMod M).val : ℕ) : ℤ) - 1 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (((ν : ZMod M).val : ℕ) : ℤ) (l ^ n)).mp (by push_cast; exact n2.symm)
    have h2 : ((l ^ n : ℕ) : ℤ) ∣ (((ν : ZMod M).val : ℕ) : ℤ) ^ j - 1 := by
      have h4 := sub_dvd_pow_sub_pow ((((ν : ZMod M).val : ℕ) : ℤ)) 1 j
      rw [one_pow] at h4
      exact dvd_trans h1 h4
    have h3 := map_dvd (Int.castRingHom ℤ_[l]) h2
    simpa using h3
  have hsc : ∀ (k : ℤ_[l]) (F : X.Fn l), (l : ℤ_[l]) ^ n ∣ k - 1 → CgF X l n (k • F) F := by
    intro k F hk u
    have h5 := hAp.2.2.2.2.1 k 1 (F u) hk
    simpa using h5
  have hpred : ∀ t : A, (fun z : (ZMod M)ˣ => π (z * ν⁻¹ ^ 2) = t) = (fun z => π z = t * π ν ^ 2) := by
    intro t
    funext z
    rw [map_mul, map_pow, map_inv, inv_pow, mul_inv_eq_iff_eq_mul]
  have C4 := hCA.2.1
    (fun s t => Xi X l n N M₀ M w g (((ν : ZMod M).val : ZMod M₀) • x) (((ν : ZMod M).val : ZMod M₀) • y)
      (fun z => π z = t) (pushD X l M₀ (ws n (l * M₀) s)))
    (fun s t => Xi X l n N M₀ M w g x y (fun z => π z = t * π ν ^ 2) (pushD X l M₀ (ws n (l * M₀) s)))
    (fun s t => by
      have hs := hS Ω ε X l n N M₀ M w g lev x y (fun z => π z = t) (pushD X l M₀ (ws n (l * M₀) s)) ν n1
      beta_reduce at hs
      rw [hpred t] at hs
      exact hAp.1.trans (hAp.1.symm (hsc _ _ (hdv w))) (hAp.1.trans hs (hsc _ _ (hdv 2))))
  have C5 := hX Ω ε X l n N M₀ M w g lev hL x y ok A π _ _ (law.dist n l M₀ lv)
  have C6 := hCA.2.2.2.1 1 (π ν ^ 2) _ _ C5
  simp only [one_smul] at C6
  exact hE.trans C1 (hE.trans C2 (hE.trans C3 (hE.trans C4 C6)))

private theorem topXi (hT : STopRel) (hB : SBridge)
    (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w c d : ℕ) [NeZero N] [NeZero M₀] [NeZero M]
    (g : SL(2, ℤ)) (lev : Lev l n N M₀ M g) (hL : LiftsWith X l N w (cL X l N w))
    (ws) (law : Laws X l c d ws) (lv : Lv c d M₀) (U V : Fin 2 → ℤ) (ok : Ok (rw0 M₀ U) (rw0 M₀ V)) (x' y' : Fin 2 → ℚ)
    (hx : ∀ i, x' i = (U i : ℚ) / (M₀ : ℚ)) (hy : ∀ i, y' i = (V i : ℚ) / (M₀ : ℚ))
    (A : Type) [Group A] [DecidableEq A] (π : (ZMod M)ˣ →* A) :
    CohB X l N w n (fun s => (π (cycM M s))⁻¹) (GlobalTheory.KA.push π (shB X l M (clsG X l n N M w c d g x' y')))
      fun s t => Xi X l n N M₀ M w g (rw0 M₀ U) (rw0 M₀ V) (fun z => π z = t) (ws n M₀ s) := by
  have hx' : ∀ i, ∃ j : ℤ, x' i = toQ M₀ (rw0 M₀ U) i + j := fun i => by
    obtain ⟨j, hj⟩ := exists_int_div_eq_toQ_rw0_add M₀ U i
    exact ⟨j, by rw [hx i, hj]⟩
  have hy' : ∀ i, ∃ j : ℤ, y' i = toQ M₀ (rw0 M₀ V) i + j := fun i => by
    obtain ⟨j, hj⟩ := exists_int_div_eq_toQ_rw0_add M₀ V i
    exact ⟨j, by rw [hy i, hj]⟩
  obtain ⟨β, hβ, hσ⟩ := hT Ω ε X l n N M₀ M w g lev hL c d ws law lv (rw0 M₀ U) (rw0 M₀ V) ok x' y' hx' hy'
  exact hB Ω ε X l n N M₀ M w g lev hL (rw0 M₀ U) (rw0 M₀ V) ok (ws n M₀) (law.coc n M₀ lv) _ β hβ hσ A π

private def rdH (l n r N p : ℕ) : (ZMod (lvT l n r N p))ˣ →* (ZMod p)ˣ × (ZMod (l ^ r))ˣ :=
  (Units.map (ZMod.castHom (Dvd.intro_left _ rfl : p ∣ lvT l n r N p) (ZMod p)).toMonoidHom).prod
   (Units.map (ZMod.castHom ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right p)
     (ZMod (l ^ r))).toMonoidHom)

private theorem rdH_comp (l n r N p : ℕ) (h : lvT l n r N p ∣ lvT l (n + 1) r N p) (z : (ZMod (lvT l (n + 1) r N p))ˣ) :
    rdH l n r N p (Units.map (ZMod.castHom h (ZMod (lvT l n r N p))).toMonoidHom z) = rdH l (n + 1) r N p z := by
  have e1 : ∀ {a b c : ℕ} (h1 : b ∣ a) (h2 : c ∣ b) (h3 : c ∣ a) (z : ZMod a),
      ZMod.castHom h2 (ZMod c) (ZMod.castHom h1 (ZMod b) z) = ZMod.castHom h3 (ZMod c) z :=
    fun h1 h2 h3 z => RingHom.congr_fun (RingHom.ext_zmod ((ZMod.castHom h2 _).comp (ZMod.castHom h1 _)) (ZMod.castHom h3 _)) z
  have d2 : l ^ r ∣ lvT l n r N p :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)) p
  have d3 : l ^ r ∣ lvT l (n + 1) r N p := dvd_trans d2 h
  have q2 : p ∣ lvT l n r N p := Dvd.intro_left _ rfl
  have q3 : p ∣ lvT l (n + 1) r N p := Dvd.intro_left _ rfl
  apply Prod.ext <;> apply Units.ext <;>
    simp only [rdH, MonoidHom.prod_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  · exact e1 h q2 q3 _
  · erw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact e1 h d2 d3 _

private theorem rdH_cyc (hG : SSlD) (hZ : SCycZ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N p : ℕ) [NeZero N] [NeZero p] :
    (fun s : Ω ≃ₐ[ℚ] Ω => (rdH l n r N p (cycM (lvT l n r N p) s))⁻¹) = kT l r p := by
  funext s
  have h := ((hG Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2 (lvT l n r N p) s).2.2.2.2
  unfold kT
  rw [(hZ Ω l r s).1]
  exact Prod.ext (congrArg Inv.inv (h p _)) (congrArg Inv.inv (h (l ^ r) _))

private theorem main (hA : SApi) (hC : SCohApi) (hM : SXiMul) (hX : SXiCoh) (hD : SXiDist) (hS : SXiScal) (hG : SSlD)
    (hT : STopRel) (hB : SBridge) (hZ : SCycZ) : KatoTwistedClassCompatibleModPowers := by
  unfold KatoTwistedClassCompatibleModPowers
  intro Ω _ _ _ ε X l _ N p _ _ x c d w g hyp hpp hcop hws hL n r
  obtain ⟨ws, law⟩ := hws
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hCA := hC Ω ε X l N w n hN ((ZMod p)ˣ × (ZMod (l ^ r))ˣ) (kT l r p)
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exact hCA.2.2.2.2.2.1 _ _
  have hE := hCA.1
  have lp : l.Prime := Fact.out
  haveI : NeZero l := ⟨lp.ne_zero⟩
  have hl0 : l ≠ 0 := lp.ne_zero
  have hpl : Nat.Coprime p l := Nat.Coprime.coprime_dvd_right
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right l N) c) d) hcop
  have hpN : Nat.Coprime p N := Nat.Coprime.coprime_dvd_right
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left N l) c) d) hcop
  have hpc : Nat.Coprime p c := Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left c (l * N)) d) hcop
  have hpd : Nat.Coprime p d := Nat.Coprime.coprime_dvd_right (dvd_mul_left d (l * N * c)) hcop
  have hpNL : ∀ j, Nat.Coprime p (N * l ^ j) := fun j => Nat.Coprime.mul_right hpN (Nat.Coprime.pow_right j hpl)
  have cpq : ∀ q j, Nat.Coprime q (6 * l * N) → Nat.Coprime p q →
      Nat.Coprime q (N * l ^ j * p) ∧ Nat.Coprime q (l * (N * l ^ j * p)) := by
    intro q j hq hpq
    have qN : Nat.Coprime q N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N (6 * l)) hq
    have ql : Nat.Coprime q l := Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left l 6) N) hq
    have h1 : Nat.Coprime q (N * l ^ j * p) :=
      Nat.Coprime.mul_right (Nat.Coprime.mul_right qN (Nat.Coprime.pow_right j ql)) hpq.symm
    exact ⟨h1, Nat.Coprime.mul_right ql h1⟩
  have pos0 : ∀ j, 0 < N * l ^ j * p := fun j =>
    Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl0)) (NeZero.ne p))
  have lvM : ∀ j, Lv c d (N * l ^ j * p) := fun j => ⟨pos0 j, (cpq c j hyp.cc hpc).1, (cpq d j hyp.cd hpd).1⟩
  have lvM1 : ∀ j, Lv c d (l * (N * l ^ j * p)) := fun j =>
    ⟨Nat.mul_pos lp.pos (pos0 j), (cpq c j hyp.cc hpc).2, (cpq d j hyp.cd hpd).2⟩
  have dl0 : l ^ n ∣ N * l ^ (r + n) * p :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow l (Nat.le_add_left n r)) N) p
  have lev0 : Lev l n N (N * l ^ (r + n) * p) (lvT l n r N p) g :=
    ⟨by simp only [lvT]; ring, Dvd.dvd.mul_right (dvd_mul_right N _) p, dl0, hn, hyp.cop, hyp.g0⟩
  have lev1 : Lev l (n + 1) N (l * (N * l ^ (r + n) * p)) (lvT l (n + 1) r N p) g :=
    ⟨by simp only [lvT]; ring, dvd_mul_of_dvd_right (Dvd.dvd.mul_right (dvd_mul_right N _) p) l,
     by rw [pow_succ']; exact Nat.mul_dvd_mul_left l dl0, by omega, hyp.cop, hyp.g0⟩
  have e1 : lvT l (n + 1) r N p = N * (l * (N * l ^ (r + n) * p)) := by simp only [lvT]; ring
  haveI i0 : NeZero (N * l ^ (r + n) * p) := ⟨(pos0 _).ne'⟩
  haveI i1 : NeZero (l * (N * l ^ (r + n) * p)) := ⟨(Nat.mul_pos lp.pos (pos0 _)).ne'⟩
  haveI i2 : NeZero (lvT l n r N p) := ⟨by rw [lev0.eq]; exact mul_ne_zero (NeZero.ne N) (pos0 _).ne'⟩
  haveI i3 : NeZero (lvT l (n + 1) r N p) := ⟨by rw [e1]; exact mul_ne_zero (NeZero.ne N) (NeZero.ne _)⟩
  have hNl : (N : ZMod l) ≠ 0 := by
    intro h0
    exact (Nat.Prime.coprime_iff_not_dvd lp).mp hyp.cop ((ZMod.natCast_eq_zero_iff N l).mp h0)
  have okOf : ∀ (Mx : ℕ) (U V : Fin 2 → ℤ), l ∣ Mx → (U 0 : ZMod l) ≠ 0 → (V 1 : ZMod l) ≠ 0 →
      Ok (rw0 Mx U) (rw0 Mx V) := by
    intro Mx U V hd hU hV
    exact ⟨two_ne hyp.odd hd U 0 hU, two_ne hyp.odd hd V 1 hV⟩
  have rl0 := rows_l (l := l) (L := r + n) (N := N) (p := p) x (by omega) (hpNL _)
  have rl1 := rows_l (l := l) (L := r + n + 1) (N := N) (p := p) x (by omega) (hpNL _)
  have ok0 := okOf (N * l ^ (r + n) * p) (rU l (r + n) N p x) (rV l (r + n) N p)
    (Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N) p)
    (by rw [rl0.1]; exact hNl) (by rw [rl0.2.1]; exact hNl)
  have ok1 := okOf (l * (N * l ^ (r + n) * p)) (rU l (r + n + 1) N p x) (rV l (r + n + 1) N p)
    (dvd_mul_right l _) (by rw [rl1.1]; exact hNl) (by rw [rl1.2.1]; exact hNl)
  have TA := topXi hT hB X l n N (N * l ^ (r + n) * p) (lvT l n r N p) w c d g lev0 hL ws law (lvM _)
    (rU l (r + n) N p x) (rV l (r + n) N p) ok0 (ixUT l (r + n) N p x) (ixVT l (r + n) N p)
    (ixUT_eq l (r + n) N p x) (ixVT_eq l (r + n) N p) _ (rdH l n r N p)
  rw [rdH_cyc hG hZ X l n r N p] at TA
  have hx1 : ∀ i, ixUT l (r + (n + 1)) N p x i =
      (rU l (r + n + 1) N p x i : ℚ) / ((l * (N * l ^ (r + n) * p) : ℕ) : ℚ) := by
    intro i
    rw [ixUT_eq]
    congr 1
    push_cast
    ring
  have hy1 : ∀ i, ixVT l (r + (n + 1)) N p i =
      (rV l (r + n + 1) N p i : ℚ) / ((l * (N * l ^ (r + n) * p) : ℕ) : ℚ) := by
    intro i
    rw [ixVT_eq]
    congr 1
    push_cast
    ring
  have TB := topXi hT hB X l (n + 1) N (l * (N * l ^ (r + n) * p)) (lvT l (n + 1) r N p) w c d g lev1 hL ws law
    (lvM1 _) (rU l (r + n + 1) N p x) (rV l (r + n + 1) N p) ok1 (ixUT l (r + (n + 1)) N p x)
    (ixVT l (r + (n + 1)) N p) hx1 hy1 _ (rdH l (n + 1) r N p)
  rw [rdH_cyc hG hZ X l (n + 1) r N p] at TB
  have TB' := hCA.2.2.2.2.1 _ _ TB
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (Nat.Coprime.symm (hpNL (r + n))) 1 l
  have k1 : (k : ZMod (N * l ^ (r + n))) = 1 := by
    have h0 := (ZMod.natCast_eq_natCast_iff k 1 (N * l ^ (r + n))).mpr hk1
    simpa using h0
  have k2 : (k : ZMod p) = l := (ZMod.natCast_eq_natCast_iff k l p).mpr hk2
  have k1' : ∀ D, D ∣ N * l ^ (r + n) → (k : ZMod D) = 1 := by
    intro D hD
    have h0 := congrArg (ZMod.castHom hD (ZMod D)) k1
    rw [map_natCast, map_one] at h0
    exact h0
  have kcNL : Nat.Coprime k (N * l ^ (r + n)) := (ZMod.isUnit_iff_coprime k _).mp (by rw [k1]; exact isUnit_one)
  have kcp : Nat.Coprime k p :=
    (ZMod.isUnit_iff_coprime k p).mp (by rw [k2]; exact (ZMod.isUnit_iff_coprime l p).mpr hpl.symm)
  have kcM : Nat.Coprime k (lvT l n r N p) := by
    have kN : Nat.Coprime k N := Nat.Coprime.coprime_dvd_right (dvd_mul_right N _) kcNL
    have kl : Nat.Coprime k (l ^ (r + n)) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ N) kcNL
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right kl (Nat.Coprime.mul_right kN kN)) kcp
  have vcast : ∀ D, D ∣ lvT l n r N p →
      ((((ZMod.unitOfCoprime k kcM : (ZMod (lvT l n r N p))ˣ) : ZMod (lvT l n r N p)).val : ℕ) : ZMod D) = (k : ZMod D) := by
    intro D hD
    show (((k : ZMod (lvT l n r N p)).val : ℕ) : ZMod D) = (k : ZMod D)
    rw [ZMod.natCast_val, ZMod.cast_natCast hD]
  have dN : N ∣ lvT l n r N p := Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_right N N) _) p
  have dLn : l ^ n ∣ lvT l n r N p := Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_left n r)) _) p
  have dM0 : N * l ^ (r + n) * p ∣ lvT l n r N p := ⟨N, by simp only [lvT]; ring⟩
  have n1 := (vcast N dN).trans (k1' N (dvd_mul_right N _))
  have n2 := (vcast (l ^ n) dLn).trans (k1' (l ^ n) (Dvd.dvd.mul_left (pow_dvd_pow l (Nat.le_add_left n r)) N))
  have rs := rows_succ (l := l) (L := r + n) (N := N) (p := p) (k := k) x hyp.cop (hpNL _) k1 k2
  have ex : dn l (N * l ^ (r + n) * p) (rw0 (l * (N * l ^ (r + n) * p)) (rU l (r + n + 1) N p x)) =
      ((((ZMod.unitOfCoprime k kcM : (ZMod (lvT l n r N p))ˣ) : ZMod (lvT l n r N p)).val : ℕ) :
        ZMod (N * l ^ (r + n) * p)) • rw0 (N * l ^ (r + n) * p) (rU l (r + n) N p x) := by
    rw [dn_rw0_mul_eq_rw0, vcast _ dM0, rs.1]
  have ey : dn l (N * l ^ (r + n) * p) (rw0 (l * (N * l ^ (r + n) * p)) (rV l (r + n + 1) N p)) =
      ((((ZMod.unitOfCoprime k kcM : (ZMod (lvT l n r N p))ˣ) : ZMod (lvT l n r N p)).val : ℕ) :
        ZMod (N * l ^ (r + n) * p)) • rw0 (N * l ^ (r + n) * p) (rV l (r + n) N p) := by
    rw [dn_rw0_mul_eq_rw0, vcast _ dM0, rs.2]
  have bas : Bas l N (rw0 (l * (N * l ^ (r + n) * p)) (rU l (r + n + 1) N p x))
      (rw0 (l * (N * l ^ (r + n) * p)) (rV l (r + n + 1) N p)) := by
    refine ⟨hyp.cop, ?_⟩
    simp only [rw0, val_cast (dvd_mul_right l (N * l ^ (r + n) * p)), rl1.1, rl1.2.1, rl1.2.2, Int.cast_zero,
      zero_mul, sub_zero, ZMod.val_zero, Nat.cast_zero]
    exact mul_ne_zero hNl hNl
  have hdvd : lvT l n r N p ∣ lvT l (n + 1) r N p := ⟨l, by simp only [lvT]; ring⟩
  have TC := down hA hC hM hX hD hS hG X l n N (N * l ^ (r + n) * p) (lvT l n r N p) (lvT l (n + 1) r N p) w c d g
    lev0 hL hdvd e1 ws law (lvM1 _) _ _ _ _ ok1 ok0 bas (ZMod.unitOfCoprime k kcM) n1 n2 ex ey _ (rdH l n r N p)
  rw [rdH_cyc hG hZ X l n r N p] at TC
  simp only [rdH_comp] at TC
  have hlu : IsUnit (l : ZMod p) := (ZMod.isUnit_iff_coprime l p).mpr hpl.symm
  have hinv : ((inv1 p l : (ZMod p)ˣ) : ZMod p) * l = 1 := by
    simp only [inv1, dif_pos hlu]
    exact hlu.val_inv_mul
  have hν1 : (((rdH l n r N p (ZMod.unitOfCoprime k kcM)).1 : (ZMod p)ˣ) : ZMod p) = l := by
    show ZMod.castHom (Dvd.intro_left _ rfl : p ∣ lvT l n r N p) (ZMod p) (k : ZMod (lvT l n r N p)) = _
    rw [map_natCast, k2]
  have hν2 : (rdH l n r N p (ZMod.unitOfCoprime k kcM)).2 = 1 := by
    apply Units.ext
    show ZMod.castHom ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right p)
      (ZMod (l ^ r)) (k : ZMod (lvT l n r N p)) = 1
    erw [map_natCast]
    exact k1' (l ^ r) (Dvd.dvd.mul_left (pow_dvd_pow l (Nat.le_add_right r n)) N)
  have hc : ∀ y : (ZMod p)ˣ × (ZMod (l ^ r))ˣ,
      y * (inv1 p l ^ (2 * (r + (n + 1))), 1) * rdH l n r N p (ZMod.unitOfCoprime k kcM) ^ 2 =
        y * (inv1 p l ^ (2 * (r + n)), 1) := by
    intro y
    apply Prod.ext
    · apply Units.ext
      simp only [Prod.fst_mul, Prod.pow_fst, Units.val_mul, Units.val_pow_eq_pow_val, hν1]
      linear_combination ((y.1 : ZMod p) * ((inv1 p l : (ZMod p)ˣ) : ZMod p) ^ (2 * (r + n)) *
        (((inv1 p l : (ZMod p)ˣ) : ZMod p) * l + 1)) * hinv
    · simp only [Prod.snd_mul, Prod.pow_snd, hν2, one_pow, mul_one]
  have cA := hCA.2.2.2.1 1 (inv1 p l ^ (2 * (r + n)), 1) _ _ TA
  have cB := hCA.2.2.2.1 1 (inv1 p l ^ (2 * (r + (n + 1))), 1) _ _ TB'
  have cC := hCA.2.2.2.1 1 (inv1 p l ^ (2 * (r + (n + 1))), 1) _ _ TC
  simp only [one_smul] at cA cB cC
  simp only [hc] at cC
  have hY : ∀ m, YT X l m r N p x c d w g = fun s y => GlobalTheory.KA.push (rdT l m r N p)
      (shB X l (lvT l m r N p) (clsT X l m r N p x c d w g)) s (y * (inv1 p l ^ (2 * (r + m)), 1)) := by
    intro m
    funext s y
    exact congrArg (GlobalTheory.KA.push (rdT l m r N p) (shB X l (lvT l m r N p) (clsT X l m r N p x c d w g)) s)
      (Prod.ext rfl (mul_one y.2).symm)
  rw [hY (n + 1), hY n]
  exact hE.trans cB (hE.trans cC (hE.symm cA))

end UpperTheory.V.Z.Kato.Nb.NormOneTraceTorsion

theorem UpperTheory.V.Z.Kato.Nb.kato_normRelation_levelTower :
    UpperTheory.V.Z.Kato.Nb.KatoTwistedClassCompatibleModPowers :=
  UpperTheory.V.Z.Kato.Nb.NormOneTraceTorsion.main sApi sCohApi sXiMul sXiCoh sXiDist sXiScal sSlD sTopRel sBridge sCycZ
end

section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sLiftOk :
    UpperTheory.V.Z.Kato.Nb.SLiftOk := by
  intro Ω _ _ _ ε X l _ N w _ hl hc hw
  have h : ∃ c, LiftsWith X l N w c :=
    UpperTheory.Kd.K4.liftH ε X l N w hl (Nat.pos_of_ne_zero (NeZero.ne N)) hc hw
  exact Classical.epsilon_spec h
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

theorem UpperTheory.V.Z.Kato.Nb.sRel0 :
    UpperTheory.V.Z.Kato.Nb.SRel0 := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he c₀ Y hY r n
  obtain ⟨bB, hL, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, heq, -⟩ := hA
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h2 : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  rw [h2] at hL
  obtain ⟨-, -, -, -, -, -, -, hcy⟩ := sSlD Ω ε X N hN
  have hfix : ∀ (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (topM l n r (N * N)))ˣ),
      (repM (topM l n r (N * N)) y)⁻¹ * s * repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹) ∈
        fixMu Ω (topMu l n r N) := by
    intro s y
    have hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l n r (N * N)) (s * t) = cycM (topM l n r (N * N)) s * cycM (topM l n r (N * N)) t :=
      fun s t => (hcy (topM l n r (N * N)) s).2.1 t
    have hr := (hcy (topM l n r (N * N)) s).2.2.1
    refine (hcy (topM l n r (N * N)) _).2.2.2.1.2 ?_
    have h1 : y * cycM (topM l n r (N * N)) ((repM (topM l n r (N * N)) y)⁻¹ * s) = cycM (topM l n r (N * N)) s := by
      conv_lhs => rw [← hr y]
      rw [← hm, hr, mul_inv_cancel_left]
    rw [hm, hr, eq_inv_mul_of_mul_eq h1]
    simp [mul_comm, mul_left_comm]
  have hB := sBStab Ω ε X l N (2 * e - 1) hN
  obtain ⟨-, -, -, hsum, -, -, hgal, -⟩ := sApi Ω ε X l n
  let P : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hadd
  refine ⟨GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB), b, fun s y => ⟨?_, ?_⟩, hb, fun s y => ?_⟩
  · exact Submodule.sum_mem _ fun y' _ => (hB _ (hL _ (hfix s y')).1).1 _
  · have h1 := hsum _ (Finset.univ.filter fun y' => redM l n r (N * N) y' = y) _ _
      (fun y' _ => hgal (repM (topM l n r (N * N)) y') _ (((l : ℤ_[l]) ^ c₀) • _) (hL _ (hfix s y')).2)
    have h3 : (∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y) =
        ∑ y' ∈ Finset.univ.filter (fun y' => redM l n r (N * N) y' = y),
          shB X l (topM l n r (N * N)) (clsBmu X l n r N x c d (2 * e + 1) gm) s y' := by
      simp only [Y0, GlobalTheory.KA.push, shB, clsBmu_eq, h2, map_sum]
      exact Finset.sum_comm
    simp only [map_smul, ← Finset.smul_sum] at h1
    beta_reduce
    rw [h3]
    exact h1
  · have h4 : pr (GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y) = YfB X l pr W e ψ n r N bB s y := by
      refine (map_sum P _ _).trans (Finset.sum_congr rfl fun y' _ => ?_)
      exact heq _ _ (hL _ (hfix s y')).1
    rw [h4]
    exact hC s y
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem lsq_eq (l p L : ℕ) (h : Nat.Coprime p l) : lsqInv l p L = inv1 p l ^ (2 * L) := by
  have h1 : IsUnit (l : ZMod p) := (ZMod.isUnit_iff_coprime l p).2 h.symm
  have h2 : IsUnit ((l : ZMod p) ^ (2 * L)) := h1.pow _
  unfold lsqInv inv1
  rw [dif_pos h1, dif_pos h2, inv_pow]
  congr 1
  ext
  simp

private theorem arg_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) [NeZero M]
    (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ) : (repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹) ∈ fixMu Ω M := by
  obtain ⟨-, -, -, -, -, -, -, hM⟩ := sSlD Ω ε X 1 one_pos
  have mul : ∀ a b : Ω ≃ₐ[ℚ] Ω, cycM M (a * b) = cycM M a * cycM M b := fun a b => (hM M a).2.1 b
  have rep : ∀ y : (ZMod M)ˣ, cycM M (repM (Ω := Ω) M y) = y := (hM M s).2.2.1
  let f : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ := MonoidHom.mk' (cycM M) mul
  rw [(hM M _).2.2.2.1]
  have e : f ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    change (cycM M (repM (Ω := Ω) M y))⁻¹ * cycM M s * cycM M (repM (Ω := Ω) M (y * (cycM M s)⁻¹)) = 1
    rw [rep, rep, mul_comm y, ← mul_assoc, mul_inv_cancel_right, inv_mul_cancel]
  exact e

private theorem lift_push {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (N w n c M : ℕ) [NeZero N] [NeZero M] {T ι : Type} [DecidableEq T] [Fintype ι] (π : (ZMod M)ˣ → T)
    (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (h : ∀ σ ∈ fixMu Ω M, LiftB X l N w n c (∑ i, z i σ) (bB σ)) (s : Ω ≃ₐ[ℚ] Ω) (t : T) :
    LiftB X l N w n c (∑ i, GlobalTheory.KA.push π (shB X l M (z i)) s t) (GlobalTheory.KA.push π (shB X l M bB) s t) := by
  obtain ⟨-, -, -, hSum, -, -, hGal, -⟩ := sApi Ω ε X l n
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have key : ∀ y : (ZMod M)ˣ, LiftB X l N w n c (∑ i, shB X l M (z i) s y) (shB X l M bB s y) := by
    intro y
    have hy := h _ (arg_mem X M s y)
    refine ⟨(sBStab Ω ε X l N w hN _ hy.1).1 _, ?_⟩
    have hc : CgF X l n (bB ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)))
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := hy.2
    have hg := hGal (repM M y) _ _ hc
    have e : (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y = X.galB l (repM M y)
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := by
      simp only [shB, map_smul, map_sum]
    intro u
    have hu := hg u
    rw [← e] at hu
    exact hu
  have hpush : ∀ Y : (Ω ≃ₐ[ℚ] Ω) → (ZMod M)ˣ → X.Fn l,
      GlobalTheory.KA.push π Y s t = ∑ y ∈ Finset.univ.filter (fun y => π y = t), Y s y := fun Y => rfl
  simp only [hpush]
  rw [Finset.sum_comm]
  refine ⟨Submodule.sum_mem _ (fun y _ => (key y).1), ?_⟩
  have hs := hSum _ (Finset.univ.filter (fun y => π y = t)) (fun y => shB X l M bB s y)
    (fun y => (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y) (fun y _ => (key y).2)
  rw [← Finset.smul_sum] at hs
  exact hs

theorem UpperTheory.V.Z.Kato.Nb.sRelT :
    UpperTheory.V.Z.Kato.Nb.SRelT := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he p _ hp c₀ Y hY r n
  obtain ⟨bB, hB, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, hgal, -⟩ := hA
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hB' : ∀ σ ∈ fixMu Ω (lvT l n r N p), LiftB X l N (2 * e - 1) n c₀ (∑ r₀, clsT X l n r N p x c d (2 * e - 1) (gm r₀) σ) (bB σ) := by
    intro σ hσ
    rw [← hw]
    exact hB σ hσ
  refine ⟨fun s y => GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s (y.1 * inv1 p l ^ (2 * (r + n)), y.2), b,
    fun s y => lift_push X l N _ n c₀ _ (rdT l n r N p) _ bB hB' s _, hb, fun s y => ?_⟩
  have key : ∀ t, pr (GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s t) = YfBT X l pr W e ψ n r N p bB s t := by
    intro t
    have hs := map_sum (AddMonoidHom.mk' pr hadd) (shB X l (lvT l n r N p) bB s)
      (Finset.univ.filter fun y' => rdT l n r N p y' = t)
    refine hs.trans (Finset.sum_congr rfl fun y' _ => ?_)
    exact hgal _ _ (hB' _ (arg_mem X _ s y')).1
  have := hC s y
  rw [lsq_eq l p _ hp, ← key] at this
  exact this
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.SquareNormRepresentation

private def ZM {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) :
    Submodule ℤ_[l] (X.Fn l) where
  carrier := {a | ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (a u) = 0}
  add_mem' {a b} ha hb u := by
    show AdicCompletion.eval (idl l) (X.Kl l) n (a u + b u) = 0
    rw [map_add, ha u, hb u, add_zero]
  zero_mem' u := by
    show AdicCompletion.eval (idl l) (X.Kl l) n 0 = 0
    exact map_zero _
  smul_mem' c a ha u := by
    show AdicCompletion.eval (idl l) (X.Kl l) n (c • a u) = 0
    rw [map_smul, ha u, smul_zero]

private def Sm {l : ℕ} [Fact l.Prime] (n : ℕ) (x : Fin 2 → Qbar l) : Prop := ∀ i, ‖x i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖

private theorem Sm.add {l : ℕ} [Fact l.Prime] {n : ℕ} {x y : Fin 2 → Qbar l} (hx : Sm n x) (hy : Sm n y) : Sm n (x + y) := by
  unfold Sm at *
  intro i
  rw [Pi.add_apply]
  exact (PadicAlgCl.isNonarchimedean l (x i) (y i)).trans (max_le (hx i) (hy i))

private theorem Sm.smul {l : ℕ} [Fact l.Prime] {n : ℕ} {x : Fin 2 → Qbar l} {k : Qbar l} (hk : ‖k‖ ≤ 1) (hx : Sm n x) :
    Sm n (k • x) := fun i => by
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hk).trans (hx i)

private theorem Sm.sub {l : ℕ} [Fact l.Prime] {n : ℕ} {x y : Fin 2 → Qbar l} (hx : Sm n x) (hy : Sm n y) : Sm n (x - y) := by
  unfold Sm at *
  intro i
  rw [Pi.sub_apply, sub_eq_add_neg]
  refine (PadicAlgCl.isNonarchimedean l _ _).trans (max_le (hx i) ?_)
  rw [norm_neg]
  exact hy i

private theorem Sm.sum {l : ℕ} [Fact l.Prime] {n : ℕ} {T : Type} (S : Finset T) (x : T → Fin 2 → Qbar l) (h : ∀ t, Sm n (x t)) :
    Sm n (∑ t ∈ S, x t) := by
  induction S using Finset.induction_on with
  | empty => intro i; simp
  | insert a S ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] c.O).FG)
  have hB : ∀ x : c.O, ‖(x : PadicAlgCl l)‖ ≤ ∑ g ∈ s, ‖(g : PadicAlgCl l)‖ := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (s : Set c.O) := by
      rw [hs]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem g hg =>
      exact Finset.single_le_sum (f := fun g : c.O => ‖(g : PadicAlgCl l)‖)
        (fun _ _ => norm_nonneg _) hg
    | zero =>
      simp only [ZeroMemClass.coe_zero, norm_zero]
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    | add x y _ _ hx hy =>
      rw [AddMemClass.coe_add]
      exact (PadicAlgCl.isNonarchimedean l _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [SetLike.val_smul, Algebra.smul_def, norm_mul]
      have hr : ‖algebraMap ℤ_[l] (PadicAlgCl l) r‖ ≤ 1 := by
        rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
        exact (PadicAlgCl.norm_extends l _).trans_le (PadicInt.norm_le_one r)
      exact (mul_le_of_le_one_left (norm_nonneg _) hr).trans hx
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ g ∈ s, ‖(g : PadicAlgCl l)‖) hlt
  have hle : ‖a ^ n‖ ≤ ∑ g ∈ s, ‖(g : PadicAlgCl l)‖ := hB ⟨a ^ n, c.O.pow_mem ha n⟩
  rw [norm_pow] at hle
  linarith

end UpperTheory.V.Z.Kato.Nb.SquareNormRepresentation

open UpperTheory.V.Z.Kato.Nb.SquareNormRepresentation in
theorem UpperTheory.V.Z.Kato.Nb.sN2rho :
    UpperTheory.V.Z.Kato.Nb.SN2rho := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hAdm he hmat
  obtain ⟨cp, hcp⟩ := UpperTheory.Kd.K4.pur ε X l N (2 * e - 1)
  refine ⟨cp + cL X l N (2 * e - 1), ?_⟩
  intro p _ hp hcop a δ ha hδ hab c₀ c₁ r n Y Y' z z' hR hR' hC
  obtain ⟨β, b1, hβ, hb1, hY⟩ := hR
  obtain ⟨β', b2, hβ', hb2, hY'⟩ := hR'
  obtain ⟨B0, hB0, hC⟩ := hC
  choose L hL using fun y => (hB0 y).2.2
  obtain ⟨_, _, _, _, hpr_add, hpr_smul, hprO, hprG, _⟩ := hAdm
  obtain ⟨hEqv, hAS, hSm, hSum, _, hAct, hGal, _⟩ := UpperTheory.V.Z.Kato.Nb.sApi Ω ε X l n
  have hStab := UpperTheory.V.Z.Kato.Nb.sBStab Ω ε X l N (2 * e - 1) (NeZero.pos N)
  set w := 2 * e - 1 with hw
  set cl := cL X l N w with hcl
  set i := inv1 (l ^ r) p with hi
  let P : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hpr_add
  have hPs : ∀ u v, pr (u - v) = pr u - pr v := fun u v => map_sub P u v
  have hPsum : ∀ {T : Type} (S : Finset T) (f : T → X.Fn l), pr (∑ t ∈ S, f t) = ∑ t ∈ S, pr (f t) :=
    fun S f => map_sum P f S
  have hPn : ∀ (k : ℕ) (v : X.Fn l), pr ((k : ℤ_[l]) • v) = (k : Qbar l) • pr v := by
    intro k v
    rw [hpr_smul]
    simp
  have hPl : ∀ (j : ℕ) (v : X.Fn l), pr ((l : ℤ_[l]) ^ j • v) = (l : Qbar l) ^ j • pr v := by
    intro j v
    rw [← Nat.cast_pow, hPn, Nat.cast_pow]
  have hPp : ∀ (j : ℕ) (v : X.Fn l), pr ((p : ℤ_[l]) ^ j • v) = (p : Qbar l) ^ j • pr v := by
    intro j v
    rw [← Nat.cast_pow, hPn, Nat.cast_pow]
  have hnO : ∀ k : ℕ, (k : Qbar l) ∈ cf.O := fun k => natCast_mem cf.O k
  have hTB : ∀ v ∈ X.B N l w, X.heckeT N l p v ∈ X.B N l w := fun v hv => (hStab v hv).2.2 p hp hcop
  have hDB : ∀ v ∈ X.B N l w, X.diam N l p v ∈ X.B N l w := by
    intro v hv
    exact (hStab v hv).2.1 _ (GlobalTheory.KZ.Betti.isDiam_sgD (NeZero.ne N) (Fact.out : l.Prime).ne_zero
      (Nat.Coprime.coprime_mul_left_right hcop)).1
  have hTc : ∀ u v, CgF X l n u v → CgF X l n (X.heckeT N l p u) (X.heckeT N l p v) := by
    intro u v h
    simp only [GlobalTheory.KZ.Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply]
    exact (hAS _ _ _ _ (hSum _ _ _ _ fun j _ => hAct _ _ _ h) (hAct _ _ _ h)).1
  have hDc : ∀ u v, CgF X l n u v → CgF X l n (X.diam N l p u) (X.diam N l p v) := by
    intro u v h
    exact hAct _ _ _ h
  have hCS : ∀ {u v : Fin 2 → Qbar l}, Cv n u v → Sm n (u - v) := fun h j => h j
  have hSC : ∀ {u v : Fin 2 → Qbar l}, Sm n (u - v) → Cv n u v := fun h j => h j
  let b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l := fun y =>
    ((l : Qbar l) ^ (cp + cl) * p) • ∑ t, b2 (t, y)
      - (l : Qbar l) ^ (cp + cl + c₁) • ((p : Qbar l) • b1 y - a • b1 (y * i)
        + ((p : Qbar l) ^ w * δ) • b1 (y * i ^ 2))
      + (l : Qbar l) ^ (cp + (c₀ + c₁)) • pr (L y)
  refine ⟨b, ?_, ?_⟩
  · intro y j
    simp only [b, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    refine add_mem (sub_mem (mul_mem (mul_mem (pow_mem (hnO l) _) (hnO p))
      (sum_mem fun t _ => hb2 _ _)) (mul_mem (pow_mem (hnO l) _) (add_mem (sub_mem
      (mul_mem (hnO p) (hb1 _ _)) (mul_mem ha (hb1 _ _))) (mul_mem (mul_mem (pow_mem (hnO p) _) hδ)
      (hb1 _ _))))) (mul_mem (pow_mem (hnO l) _) (hprO _ (hL y).1 j))
  intro s y
  have hb : ∀ y', β s y' ∈ X.B N l w := fun y' => (hβ s y').1
  have hβc : ∀ y', CgF X l n (β s y') ((l : ℤ_[l]) ^ c₀ • z s y') := fun y' => (hβ s y').2
  have hβ'c : ∀ t, CgF X l n (β' s (t, y)) ((l : ℤ_[l]) ^ (c₀ + c₁) • z' s (t, y)) := fun t => (hβ' s (t, y)).2
  have hLc : ∀ y', CgF X l n (L y') ((l : ℤ_[l]) ^ cl • B0 y') := fun y' => (hL y').2
  have hadd : ∀ {u v u' v' : X.Fn l}, CgF X l n u v → CgF X l n u' v' → CgF X l n (u + u') (v + v') :=
    fun h h' => (hAS _ _ _ _ h h').1
  have hsub : ∀ {u v u' v' : X.Fn l}, CgF X l n u v → CgF X l n u' v' → CgF X l n (u - u') (v - v') :=
    fun h h' => (hAS _ _ _ _ h h').2
  have hEB : (l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y) ∈ X.B N l w := by
    refine sub_mem (Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _
      (sum_mem fun t _ => (hβ' s (t, y)).1)) (Submodule.smul_mem _ _ (add_mem (sub_mem
      (Submodule.smul_mem _ _ (hb y)) (hTB _ (hb _))) (Submodule.smul_mem _ _ (hDB _ (hb _)))))))
      (Submodule.smul_mem _ _ (sub_mem ((hStab _ (hL _).1).1 s) (hL y).1))
  have hE1 : CgF X l n ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)) ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, (l : ℤ_[l]) ^ (c₀ + c₁) • z' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • (l : ℤ_[l]) ^ c₀ • z s y - X.heckeT N l p ((l : ℤ_[l]) ^ c₀ • z s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p ((l : ℤ_[l]) ^ c₀ • z s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s ((l : ℤ_[l]) ^ cl • B0 (y * (cycMod ℚ Ω l r s)⁻¹)) - (l : ℤ_[l]) ^ cl • B0 y)) :=
    hsub (hSm _ _ _ (hsub (hSm _ _ _ (hSum _ _ _ _ fun t _ => hβ'c t)) (hSm _ _ _ (hadd (hsub
      (hSm _ _ _ (hβc y)) (hTc _ _ (hβc _))) (hSm _ _ _ (hDc _ _ (hβc _)))))))
      (hSm _ _ _ (hsub (hGal _ _ _ (hLc _)) (hLc y)))
  have hCsy := hC s y
  beta_reduce at hCsy
  have hzero : ∀ {u v : X.Fn l}, CgF X l n u v → CgF X l n (u - v) 0 := by
    intro u v h
    have h' := hsub h (hEqv.refl v)
    rwa [sub_self] at h'
  have h1 := hzero hCsy
  have h2 := hSm ((l : ℤ_[l]) ^ (cl + (c₀ + c₁))) _ _ h1
  rw [smul_zero] at h2
  have hEz : CgF X l n ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)) 0 := by
    refine hEqv.trans hE1 ?_
    convert h2 using 2
    simp only [map_smul, ← Finset.smul_sum]
    module
  obtain ⟨E', hE'B, hEE'⟩ := hcp n _ hEB hEz
  have hsmall : Sm n (pr ((l : ℤ_[l]) ^ cp • ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)))) := by
    rw [hEE', hPl]
    intro j
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (nle cf (hprO _ hE'B j))
  have hprE : pr ((l : ℤ_[l]) ^ cp • ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y))) = (l : Qbar l) ^ cp • ((l : Qbar l) ^ cl • ((p : Qbar l) • ∑ t, pr (β' s (t, y)) - (l : Qbar l) ^ c₁ • ((p : Qbar l) • pr (β s y) - a • pr (β s (y * i)) + (p : Qbar l) ^ w • δ • pr (β s (y * i ^ 2)))) - (l : Qbar l) ^ (c₀ + c₁) • (rhoK W e ψ s *ᵥ pr (L (y * (cycMod ℚ Ω l r s)⁻¹)) - pr (L y))) := by
    simp only [hPl, hPs, hpr_add, hPsum, hPn, hPp]
    rw [(hab _ (hb _)).1, (hab _ (hb _)).2, hprG s _ (hL _).1]
  have hk : ∀ {k : Qbar l}, k ∈ cf.O → ‖k‖ ≤ 1 := fun hk => nle cf hk
  have hbig : Sm n (((l : Qbar l) ^ (cp + cl) * p) • ∑ t, (Y' s (t, y) - (pr (β' s (t, y)) + (rhoK W e ψ s *ᵥ b2 ((t, y) * kT l r p s) - b2 (t, y)))) - (l : Qbar l) ^ (cp + cl + c₁) • ((p : Qbar l) • (Y s (y) - (pr (β s (y)) + (rhoK W e ψ s *ᵥ b1 ((y) * (cycMod ℚ Ω l r s)⁻¹) - b1 (y)))) - a • (Y s (y * i) - (pr (β s (y * i)) + (rhoK W e ψ s *ᵥ b1 ((y * i) * (cycMod ℚ Ω l r s)⁻¹) - b1 (y * i)))) + ((p : Qbar l) ^ w * δ) • (Y s (y * i ^ 2) - (pr (β s (y * i ^ 2)) + (rhoK W e ψ s *ᵥ b1 ((y * i ^ 2) * (cycMod ℚ Ω l r s)⁻¹) - b1 (y * i ^ 2))))) + pr ((l : ℤ_[l]) ^ cp • ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)))) :=
    Sm.add (Sm.sub (Sm.smul (hk (mul_mem (pow_mem (hnO l) _) (hnO p)))
      (Sm.sum _ _ fun t => hCS (hY' s (t, y)))) (Sm.smul (hk (pow_mem (hnO l) _))
      (Sm.add (Sm.sub (Sm.smul (hk (hnO p)) (hCS (hY s y))) (Sm.smul (hk ha) (hCS (hY s _))))
      (Sm.smul (hk (mul_mem (pow_mem (hnO p) _) hδ)) (hCS (hY s _)))))) hsmall
  apply hSC
  convert hbig using 1
  rw [hprE]
  simp only [b]
  have hre : ∑ t, rhoK W e ψ s *ᵥ b2 ((t, y) * kT l r p s)
      = rhoK W e ψ s *ᵥ ∑ t, b2 (t, y * (cycMod ℚ Ω l r s)⁻¹) := by
    rw [← Matrix.mulVecLin_apply, map_sum]
    exact Fintype.sum_equiv (Equiv.mulRight (cycM p s)⁻¹) _ _ (fun t => rfl)
  rw [show y * i * (cycMod ℚ Ω l r s)⁻¹ = y * (cycMod ℚ Ω l r s)⁻¹ * i from mul_right_comm _ _ _,
    show y * i ^ 2 * (cycMod ℚ Ω l r s)⁻¹ = y * (cycMod ℚ Ω l r s)⁻¹ * i ^ 2 from mul_right_comm _ _ _]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hre, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul]
  module
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := _root_.SharedProofs.SInteg.nle (c := c) (ha := ha)

private theorem sadd {l : ℕ} [Fact l.Prime] {δ : ℝ} {a b : Qbar l} (ha : ‖a‖ ≤ δ) (hb : ‖b‖ ≤ δ) : ‖a + b‖ ≤ δ :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private theorem smul' {l : ℕ} [Fact l.Prime] {δ : ℝ} {a b : Qbar l} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ δ) : ‖a * b‖ ≤ δ := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hb

private theorem shift {l : ℕ} [Fact l.Prime] {U : Type} [CommGroup U] [Fintype U] {δ : ℝ} (hδ : 0 ≤ δ) (η F : U → Qbar l) (t : U)
    (c : Qbar l) (h : ∀ y, ‖η (y * t) - η y * c‖ ≤ δ) (hF : ∀ y, ‖F y‖ ≤ 1) :
    ‖∑ y, η y * F (y * t⁻¹) - c * ∑ y, η y * F y‖ ≤ δ := by
  have e : ∑ y, η y * F (y * t⁻¹) = ∑ y, η (y * t) * F y :=
    (Fintype.sum_equiv (Equiv.mulRight t) _ _ fun y => by simp).symm
  rw [e, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hδ fun y _ => ?_
  have : η (y * t) * F y - c * (η y * F y) = F y * (η (y * t) - η y * c) := by ring
  rw [this]
  exact smul' (hF y) (h y)

private theorem unit_of {l r : ℕ} [hl : Fact l.Prime] (hr : r ≠ 0) (y : (ZMod (l ^ r))ˣ) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = ((y : ZMod (l ^ r)).val : ℕ) := by
  have h := Nat.Coprime.coprime_dvd_right (dvd_pow_self l hr) (ZMod.val_coe_unit_coprime y)
  have : IsUnit (((y : ZMod (l ^ r)).val : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact h.symm
  exact this

private theorem inv_cg {l r : ℕ} [hl : Fact l.Prime] (c : Coef l) (hr : r ≠ 0) (e : ℕ) (y t : (ZMod (l ^ r))ˣ) (τ : ℤ_[l]ˣ)
    (h : PadicInt.toZModPow r (τ : ℤ_[l]) = t) :
    ‖((((((y * t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : Qbar l)) ^ e)⁻¹ -
      (((((y : ZMod (l ^ r)).val : ℕ) : Qbar l)) ^ e)⁻¹ * ((algebraMap ℤ_[l] (Qbar l) τ) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  obtain ⟨u, hu⟩ := unit_of hr (y * t)
  obtain ⟨v, hv⟩ := unit_of hr y
  have h1 : (l : ℤ_[l]) ^ r ∣ ((v * τ : ℤ_[l]ˣ) : ℤ_[l]) - u := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, Units.val_mul, map_mul, hu, hv, h,
      map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.val_mul, sub_self]
  obtain ⟨k, hk⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ e)
  have inv : ∀ w : ℤ_[l]ˣ, (algebraMap ℤ_[l] (Qbar l) w ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ((w⁻¹ : ℤ_[l]ˣ) ^ e) := fun w => by
    apply inv_eq_of_mul_eq_one_right
    rw [← map_pow, ← map_mul, ← mul_pow, Units.mul_inv, one_pow, map_one]
  rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)) (ZMod.val _), ← map_natCast (algebraMap ℤ_[l] (Qbar l)) (ZMod.val _), ← hu, ← hv,
    inv, inv, inv, ← map_mul, ← map_sub]
  have e1 : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e - ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((τ⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e =
      (k * ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e) * (l : ℤ_[l]) ^ r := by
    have a1 : ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((v * τ : ℤ_[l]ˣ) : ℤ_[l]) ^ e = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e := by
      rw [← mul_pow, ← Units.val_mul, inv_mul_cancel_right]
    have a2 : ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * (u : ℤ_[l]) ^ e =
        ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((τ⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e := by
      rw [← mul_pow, ← mul_pow, ← Units.val_mul, ← Units.val_mul, mul_comm u⁻¹, inv_mul_cancel_right, mul_inv]
    rw [← a1, ← a2, ← mul_sub, hk]; ring
  rw [e1, map_mul, map_pow, map_natCast]
  exact smul' (nle c (c.O.algebraMap_mem _)) le_rfl

theorem UpperTheory.V.Z.Kato.Nb.sSpec :
    UpperTheory.V.Z.Kato.Nb.SSpec := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hW p r hp hlp a δ k ha hδ hk Y V b hY hb H
  obtain ⟨hθ, h1, hmul, hψ, hρ, -, -⟩ := sInteg l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hW
  rcases eq_or_ne r 0 with rfl | hr
  · refine ⟨0, fun i => zero_mem _, fun s i => ?_⟩
    have z : ∀ y : (ZMod (l ^ 0))ˣ, (y : ZMod (l ^ 0)).val = 0 := fun y =>
      Nat.lt_one_iff.1 (by simpa using ZMod.val_lt (y : ZMod (l ^ 0)))
    simp only [Cg, spec, z, Nat.cast_zero, zero_pow (show e ≠ 0 by omega), inv_zero, zero_mul, zero_smul, Finset.sum_const_zero]
    simp
  have hS := (sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2
  let rd : (ZMod (l ^ r))ˣ →* (ZMod l)ˣ := Units.map (ZMod.castHom (dvd_pow_self l hr) (ZMod l)).toMonoidHom
  have hrd : ∀ y, chiK l ψ r y = ψ (rd y : (ZMod l)ˣ) := fun y => by
    rw [chiK, ZMod.natCast_val]; rfl
  set η : (ZMod (l ^ r))ˣ → Qbar l := fun x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x with hη
  have uO : ∀ w : ℤ_[l]ˣ, (algebraMap ℤ_[l] (Qbar l) w)⁻¹ ∈ cf.O := fun w => by
    rw [show (algebraMap ℤ_[l] (Qbar l) w)⁻¹ = algebraMap ℤ_[l] (Qbar l) (w⁻¹ : ℤ_[l]ˣ) from
      inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])]
    exact cf.O.algebraMap_mem _
  have ηO : ∀ y, η y ∈ cf.O := fun y => by
    obtain ⟨u, hu⟩ := unit_of hr y
    simp only [hη]
    rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)), ← hu, ← inv_pow, hrd]
    exact mul_mem (pow_mem (uO u) e) (hψ _)
  have key : ∀ (t : (ZMod (l ^ r))ˣ) (τ : ℤ_[l]ˣ), PadicInt.toZModPow r (τ : ℤ_[l]) = t → ∀ y,
      ‖η (y * t) - η y * (((algebraMap ℤ_[l] (Qbar l) τ) ^ e)⁻¹ * ψ (rd t : (ZMod l)ˣ))‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := fun t τ h y => by
    simp only [hη]
    rw [hrd, hrd, map_mul, hmul]
    have := smul' (nle cf (mul_mem (hψ (rd y)) (hψ (rd t)))) (inv_cg cf hr e y t τ h)
    convert this using 2
    ring
  have hp1 : (p : ZMod l) = 1 := by
    obtain ⟨m, hm⟩ := hlp
    rw [show p = l * m + 1 by have := hp.pos; omega]
    simp
  have hcop : Nat.Coprime l p := by
    rw [Nat.Prime.coprime_iff_not_dvd hl.out, ← ZMod.natCast_eq_zero_iff, hp1]
    exact one_ne_zero
  obtain ⟨π, hπ⟩ : IsUnit (p : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]; exact hcop
  have hq : IsUnit (p : ZMod (l ^ r)) := (ZMod.isUnit_iff_coprime _ _).2 (hcop.symm.pow_right r)
  have hinv : inv1 (l ^ r) p = hq.unit⁻¹ := dif_pos hq
  have hπ' : algebraMap ℤ_[l] (Qbar l) π = p := by rw [hπ, map_natCast]
  have hrq : ((rd hq.unit : (ZMod l)ˣ) : ZMod l) = 1 := by
    rw [← hp1]; exact map_natCast (ZMod.castHom (dvd_pow_self l hr) (ZMod l)) p
  have k1 := key hq.unit π (by rw [hπ, map_natCast]; rfl)
  have k2 := key (hq.unit ^ 2) (π ^ 2) (by rw [Units.val_pow_eq_pow_val, map_pow, hπ, map_natCast]; rfl)
  rw [hπ', hrq, h1] at k1
  rw [Units.val_pow_eq_pow_val, map_pow, hπ', map_pow, Units.val_pow_eq_pow_val, hrq, one_pow, h1] at k2
  have hpO : (p : Qbar l)⁻¹ ∈ cf.O := hπ' ▸ uO π
  have hp0 : (p : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpn : ‖(p : Qbar l)‖ ≤ 1 := nle cf (natCast_mem _ p)
  refine ⟨fun i => (p : Qbar l)⁻¹ * ∑ y, η y * b y i, fun i => mul_mem hpO (sum_mem fun y _ => mul_mem (ηO y) (hb y i)), fun s i => ?_⟩
  have k3 := key (cycMod ℚ Ω l r s) (cycZ ℚ Ω l s) rfl
  have hth : ((algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]ˣ)) ^ e)⁻¹ * ψ (rd (cycMod ℚ Ω l r s) : (ZMod l)ˣ) = thK l e ψ s := by
    have a1 : rd (cycMod ℚ Ω l r s) = cycM l s := by
      rw [(sCycZ Ω l r s).1]; exact (hS (l ^ r) s).2.2.2.2 l (dvd_pow_self l hr)
    have a2 := (hS (l ^ 1) s).2.2.2.2 l (dvd_pow_self l one_ne_zero)
    rw [← (sCycZ Ω l 1 s).1] at a2
    rw [a1, ← a2, thK, ZMod.natCast_val]; rfl
  rw [hth] at k3
  have h0 := norm_nonneg (((l : ℕ) : Qbar l) ^ r)
  have s1 := shift h0 η (fun y => Y s y i) _ _ k1 fun y => hY s y i
  have s2 := shift h0 η (fun y => Y s y i) _ _ k2 fun y => hY s y i
  have s3 := fun j => shift h0 η (fun y => b y j) _ _ k3 fun y => nle cf (hb y j)
  have s0 := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (s := Finset.univ) h0 fun y _ => smul' (nle cf (ηO y)) (H s y i)
  have hθ0 : thK l e ψ s ≠ 0 := fun h => by simpa [h] using hθ s
  have hWρ : ∀ j, mat W s i j = thK l e ψ s * rhoK W e ψ s i j := fun j => by
    rw [rhoK, Matrix.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hθ0]
  have E : ∑ y, η y * (((p : Qbar l) • V s y) i - (k • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
          ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) =
      p * ∑ y, η y * V s y i - (k * (p * ∑ y, η y * Y s y i - a * ∑ y, η y * Y s (y * hq.unit⁻¹) i +
        ((p : Qbar l) ^ (2 * e - 1) * δ) * ∑ y, η y * Y s (y * (hq.unit ^ 2)⁻¹) i) +
        (rhoK W e ψ s i 0 * ∑ y, η y * b (y * (cycMod ℚ Ω l r s)⁻¹) 0 + rhoK W e ψ s i 1 * ∑ y, η y * b (y * (cycMod ℚ Ω l r s)⁻¹) 1 -
          ∑ y, η y * b y i)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hinv, inv_pow, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [E] at s0
  have fin := smul' (nle cf hpO) (sadd (sadd (sadd (sadd s0 (smul' (a := -(k * a)) (by rw [norm_neg]; exact smul' hk ha) s1))
    (smul' (a := k * ((p : Qbar l) ^ (2 * e - 1) * δ)) (smul' hk (smul' (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hpn) hδ)) s2))
    (smul' (nle cf (hρ s i 0)) (s3 0))) (smul' (nle cf (hρ s i 1)) (s3 1)))
  unfold Cg
  convert fin using 2
  simp only [spec, eul, Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, hWρ]
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [show 2 * (e' + 1) - 1 = 2 * e' + 1 by omega]
  field_simp
  ring
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.PushforwardPsi

private theorem exF {Γ A C : Type} [Group Γ] [CommGroup A] [CommGroup C] (c : Γ →* A) (ψ : Γ →* C)
    (h : ∀ s, c s = 1 → ψ s = 1) : ∃ f : A → C, ∀ a s, f (a * (c s)⁻¹) = f a * ψ s := by
  have h1 : ∀ a : A, ∃ s, c s = a⁻¹ * (QuotientGroup.mk a : A ⧸ c.range).out := fun a =>
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk a : A ⧸ c.range)).symm
  choose σ hσ using h1
  refine ⟨fun a => ψ (σ a), fun a s => ?_⟩
  have e : (QuotientGroup.mk (a * (c s)⁻¹) : A ⧸ c.range) = QuotientGroup.mk a :=
    QuotientGroup.eq.2 ⟨s, by simp⟩
  have h2 := h ((σ (a * (c s)⁻¹))⁻¹ * (σ a * s)) (by
    rw [map_mul, map_mul, map_inv, hσ, hσ, e, inv_mul_eq_one, mul_inv, inv_inv, mul_right_comm])
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul] at h2
  exact h2

private theorem exC (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] :
    ∃ c : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ, ∀ s, cycM M s = c s ∧ ∀ z : Ω, z ^ M = 1 → s z = z ^ (c s : ZMod M).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨hζ.autToPow ℚ, fun s => ?_⟩
  have hs : ∀ z : Ω, z ^ M = 1 → s z = z ^ (hζ.autToPow ℚ s : ZMod M).val := fun w hw => by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
    rw [map_pow, ← hζ.autToPow_spec ℚ s, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨?_, hs⟩
  have hM := cycM_spec M s ⟨_, hs⟩
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((hM ζ hζ.pow_eq_one).symm.trans (hs ζ hζ.pow_eq_one))

private theorem push_prod {Γ A B B' V : Type} [Group Γ] [AddCommMonoid V] [Fintype A] [Fintype B'] [DecidableEq B]
    {i1 : Fintype (A × B')} {i2 : DecidableEq (A × B)} (g : B' → B) (Z : Γ → A × B' → V) (s : Γ) (a : A) (y : B) :
    @push Γ (A × B) (A × B') i1 i2 V _ (Prod.map id g) Z s (a, y) = ∑ y', if g y' = y then Z s (a, y') else 0 := by
  obtain rfl : i1 = instFintypeProd A B' := Subsingleton.elim _ _
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun y' _ => ?_
  by_cases h : g y' = y <;> simp [h]

end UpperTheory.V.Z.Kato.Nb.PushforwardPsi

open UpperTheory.V.Z.Kato.Nb.PushforwardPsi in
theorem UpperTheory.V.Z.Kato.Nb.sPushPsi :
    UpperTheory.V.Z.Kato.Nb.SPushPsi := by
  intro l _ Ω _ _ _ cf ρ p n _ ψw hψ Y hc hp hcont hO
  obtain ⟨c, hcs⟩ := exC Ω p
  obtain ⟨f, hf⟩ := exF c ψw fun s hs => hψ s fun z hz => by
    rw [(hcs s).2 z hz, hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hz, pow_one]
  refine ⟨fun r s x => ∑ t, if f t = x.1 then Y r s (t, x.2) else 0, fun r s s' x => ?_, fun r x i => ?_,
    fun r s x i => ?_, fun r s => ?_, fun r s y => ?_⟩
  · have e : ∑ t, (if f t = (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).1 then
        Y r s' (t, (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).2) else 0) =
        ∑ t, if f t = x.1 then Y r s' ((t, x.2) * cycT l r p s) else 0 := by
      symm
      refine Fintype.sum_equiv (Equiv.mulRight (c s)⁻¹) _ _ fun t => ?_
      simp [hf, cycT, (hcs s).1]
    beta_reduce
    rw [e, Matrix.mulVec_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · exact hc r s s' _
    · simp
  · simp only [Finset.sum_apply]
    refine continuous_finset_sum _ fun t _ => ?_
    split_ifs
    · exact hcont r _ i
    · exact continuous_const
  · simp only [Finset.sum_apply]
    refine sum_mem fun t _ => ?_
    split_ifs
    · exact hO r s _ i
    · exact zero_mem _
  · funext ⟨a, y⟩
    rw [push_prod]
    have e : ∀ t, Y r s (t, y) = ∑ y', if redL l r y' = y then Y (r + 1) s (t, y') else 0 := fun t => by
      rw [hp r, push_prod]
    simp only [e]
    have e2 : ∀ (P : Prop) [Decidable P] {ι : Type} [Fintype ι] (v : ι → Fin 2 → Qbar l),
        (if P then ∑ j, v j else 0) = ∑ j, if P then v j else 0 := fun P _ _ _ v => by split_ifs <;> simp
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun t _ => ?_
    change (if f t = a then if redL l r y' = y then _ else 0 else 0) = if redL l r y' = y then if f t = a then _ else 0 else 0
    split_ifs <;> rfl
  · rw [Finset.sum_comm]
    simp
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nsum {l : ℕ} [Fact l.Prime] {ι : Type} (S : Finset ι) (f : ι → Qbar l) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i ∈ S, ‖f i‖ ≤ C) : ‖∑ i ∈ S, f i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

private theorem cv_wsum {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] (n : ℕ) (cw : ι → Qbar l) (hc : ∀ x, ‖cw x‖ ≤ 1)
    (a b : ι → Fin 2 → Qbar l) (h : ∀ x, Cv n (a x) (b x)) : Cv n (∑ x, cw x • a x) (∑ x, cw x • b x) := by
  intro i
  unfold Cg
  rw [Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
  refine nsum _ _ _ (norm_nonneg _) fun x _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hc x)).trans (h x i)

private theorem coh_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (N w n : ℕ) (hN : 0 < N) (A : Type) [CommGroup A] (κ : (Ω ≃ₐ[ℚ] Ω) → A) {ι : Type} (S : Finset ι)
    (z z' : ι → (Ω ≃ₐ[ℚ] Ω) → A → X.Fn l) (h : ∀ i, CohB X l N w n κ (z i) (z' i)) :
    CohB X l N w n κ (∑ i ∈ S, z i) (∑ i ∈ S, z' i) := by
  obtain ⟨h1, -, h3, -⟩ := sCohApi Ω ε X l N w n hN A κ
  induction S using Finset.induction_on with
  | empty => simpa using h1.refl _
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h3 _ _ _ _ (h i) ih).1

theorem UpperTheory.V.Z.Kato.Nb.kato_tame_relation_projected :
    UpperTheory.V.Z.Kato.Nb.KatoTameRelationProjected := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ cw c d gm ψ cf S hNf hmat hgm hlN hl2 he hcw hj hadm c₀ Y hY
  obtain ⟨hadm3, hcwO⟩ := hadm
  obtain ⟨x₀, hx₀⟩ := hcw
  have hA0 := hadm3 x₀ hx₀
  have hlp : l.Prime := Fact.out
  obtain ⟨c₁, hc₁⟩ := mlTOf symEx sApi sInvApi sBStab sSlD sCohApi sCycZ sTopT kato_normRelation_twistTower kato_normRelation_levelTower l Ω ε X N e hlN hl2 he
  have hm := fun x : {x // cw x ≠ 0} => sN2rho l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he hmat
  choose m hm using hm
  have hInt := sInteg l Ω ι e gN A W ε X pr N x₀ c d gm ψ cf hA0 he hmat
  obtain ⟨Yx, hYx, hYsum⟩ := hY
  obtain ⟨S', hSS', hS'⟩ := sEuler l Ω ι e gN A W ε X pr N x₀ c d gm ψ cf hA0 he hlN S hNf hmat
  refine ⟨Finset.univ.sup m + c₁, S', fun w hw => hNf.unr w (fun h => hw (hSS' h)), ?_⟩
  intro n hn w hw hdiv ψw hK hsurj
  obtain ⟨hpP, hpcop, a, δ, ha, hδ, hhec, hfrob⟩ := hS' w hw
  haveI : NeZero (normV w) := ⟨hpP.ne_zero⟩
  have hpl : (normV w).Coprime l := Nat.Coprime.coprime_dvd_right ⟨N * c * d, by ring⟩ hpcop
  have hplN : (normV w).Coprime (l * N) := Nat.Coprime.coprime_dvd_right ⟨c * d, by ring⟩ hpcop
  have hY' := fun x : {x // cw x ≠ 0} => hc₁ (c₀ + c₁) (by omega) ι gN A W pr x.1 c d gm ψ cf (hadm3 x.1 x.2)
    (normV w) hpP hpcop
  choose Y' hY'Z hY'coc hY'push hY'cont hY'O using hY'
  have hEC := sEulCg l Ω ι e gN A W ε X pr N x₀ c d gm ψ cf hA0 he (normV w) n hpP hn hdiv a δ ha hδ
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hc1, hd1, hcc, hdc, -, -, -, -, -, -, hgN, -⟩ := hA0
  have hLaws : ∃ ws, Laws X l c d ws :=
    symEx Ω ε X l c d hlp hc1 hd1 (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hcc)
      (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hdc)
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hLW := sLiftOk Ω ε X l N (2 * e - 1) hl2 hlN hodd
  have hHyp : ∀ r₀, Hyp l N c d (gm r₀) := fun r₀ => ⟨hl2, hlN, hc1, hd1, hcc, hdc, hgN r₀⟩
  have hkey := fun (x : {x // cw x ≠ 0}) (r : ℕ) =>
    hm x (normV w) hpP hplN a δ ha hδ hhec c₀ c₁ r r (Yx x.1 r) (Y' x r) _ _
      (sRel0 l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he c₀ (Yx x.1) (hYx x.1) r r)
      (sRelT l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he (normV w) hpl (c₀ + c₁) (Y' x) (hY'Z x) r r)
      (by
        clear hc₁ hm hY'Z hY'coc hY'push hY'cont hY'O hYx hYsum hS' hInt hEC hadm3 hmat hNf hgm hj hfrob hhec
        have h := coh_sum X l N (2 * e - 1) r hN0 _ (fun s => ((cycMod ℚ Ω l r) s)⁻¹) Finset.univ _ _
          (fun r₀ => kato_norm_relation_tame_prime Ω ε X l N (normV w) x.1 c d (2 * e - 1) (gm r₀) (hHyp r₀) hpP hpcop hLaws hLW r r)
        convert h using 1
        all_goals try rfl
        all_goals funext s y
        all_goals simp [Finset.sum_apply, Finset.smul_sum, map_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        all_goals exact Finset.sum_comm)
  choose bN hbN hCvN using hkey
  have hO1 : ∀ z ∈ cf.O, ‖z‖ ≤ 1 := fun z hz => GlobalTheory.CoefCoord.norm_le_one cf ⟨z, hz⟩
  have hlO : ((l : ℕ) : Qbar l) ∈ cf.O := natCast_mem cf.O l
  have hldvd : l ∣ normV w - 1 := dvd_trans (dvd_pow_self l (by omega : n ≠ 0)) hdiv
  have hsp := fun (x : {x // cw x ≠ 0}) (r : ℕ) =>
    sSpec l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he hmat (normV w) r hpP hldvd a δ
      (((l : ℕ) : Qbar l) ^ (m x + c₁)) (hO1 a ha) (hO1 δ hδ) (hO1 _ (pow_mem hlO _)) (Yx x.1 r)
      (fun s y => ((l : ℕ) : Qbar l) ^ (m x) • ∑ t, Y' x r s (t, y)) (bN x r)
      ((sInteg l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he hmat).2.2.2.2.2.2 c₀ (Yx x.1) (hYx x.1) r)
      (hbN x r) (fun s y => by
        have h := hCvN x r s y
        rw [mul_comm, ← smul_smul] at h
        exact h)
  choose b' hb'O hb'Cv using hsp
  set M := Finset.univ.sup m with hM
  have hmM : ∀ x, m x ≤ M := fun x => Finset.le_sup (Finset.mem_univ x)
  obtain ⟨Yt, hYt⟩ : ∃ Yt : (r : ℕ) → (Ω ≃ₐ[ℚ] Ω) → (ZMod (normV w))ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
      ∀ r s y, Yt r s y = ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ M) • Y' x r s y :=
    ⟨fun r s y => _, fun r s y => rfl⟩
  have hcoc : ∀ r s s' y, Yt r (s * s') y = Yt r s y + rhoK W e ψ s *ᵥ Yt r s' (y * cycT l r (normV w) s) := by
    intro r s s' y
    simp only [hYt, hY'coc, smul_add, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hpush : ∀ r, Yt r = push (Prod.map id (redL l r)) (Yt (r + 1)) := by
    intro r
    funext s y
    simp only [push, hYt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hY'push x r]
    simp only [push, Finset.smul_sum]
  have hcont : ∀ r y i, Continuous fun s => Yt r s y i := by
    intro r y i
    simp only [hYt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact continuous_finset_sum _ fun x _ => continuous_const.mul (hY'cont x r y i)
  have hmem : ∀ r s u i, Yt r s u i ∈ cf.O := by
    intro r s u i
    rw [hYt, Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun x _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hcwO x.1) (pow_mem hlO _)) (hY'O x r s u i)
  obtain ⟨Yw, hYw1, hYw2, hYw3, hYw4, hYw5⟩ :=
    sPushPsi l Ω cf (rhoK W e ψ) (normV w) n ψw hK Yt hcoc hpush hcont hmem
  have hsub : ∀ f : ZMod N → (Fin 2 → Qbar l), ∑ x, cw x • f x = ∑ x : {x // cw x ≠ 0}, cw x.1 • f x.1 := by
    intro f
    rw [← Finset.sum_filter_of_ne (p := fun x => cw x ≠ 0) (fun x _ h hc => h (by simp [hc]))]
    exact Finset.sum_subtype _ (fun x => by simp) _
  refine ⟨Yw, eul l e (normV w) a δ, 1, fun r => ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) • b' x r,
    hYw1, hYw2, hYw3, hYw4, hEC.1, by simp, ?_, ?_, ?_⟩
  · intro r i
    beta_reduce
    rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun x _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hcwO x.1) (pow_mem hlO _)) (hb'O x r i)
  · intro r s i
    have hcv := cv_wsum r (fun x => cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x))
      (fun x => by
        rw [norm_mul, norm_pow]
        exact mul_le_one₀ (hO1 _ (hcwO x.1)) (by positivity) (pow_le_one₀ (norm_nonneg _) (hO1 _ hlO)))
      _ _ (fun x => hb'Cv x r s)
    have hL : ∀ η : (ZMod (l ^ r))ˣ → Qbar l, (∑ a, spec η (fun s x => Yw r s (a, x)) s) =
        ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) •
          spec η (fun s y => ((l : ℕ) : Qbar l) ^ (m x) • ∑ t, Y' x r s (t, y)) s := by
      intro η
      simp only [spec]
      calc ∑ a, ∑ y, η y • Yw r s (a, y) = ∑ y, η y • ∑ a, Yw r s (a, y) := by
            rw [Finset.sum_comm]
            simp only [Finset.smul_sum]
        _ = ∑ y, η y • ∑ t, Yt r s (t, y) := by simp only [hYw5]
        _ = _ := by
            simp only [hYt, Finset.smul_sum, smul_smul]
            refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
            refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
              Finset.sum_congr rfl fun t _ => ?_
            have hp : ((l : ℕ) : Qbar l) ^ M = ((l : ℕ) : Qbar l) ^ (M - m x) * ((l : ℕ) : Qbar l) ^ (m x) := by
              rw [← pow_add, Nat.sub_add_cancel (hmM x)]
            rw [hp]
            congr 1
            ring
    have hR : ∀ η : (ZMod (l ^ r))ˣ → Qbar l,
        eul l e (normV w) a δ • ((l : ℕ) : Qbar l) ^ (M + c₁) • spec η (Y r) s +
          (mat W s *ᵥ (∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) • b' x r) -
            ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) • b' x r) =
        ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) •
          (eul l e (normV w) a δ • ((l : ℕ) : Qbar l) ^ (m x + c₁) • spec η (Yx x.1 r) s +
            (mat W s *ᵥ b' x r - b' x r)) := by
      intro η
      simp only [smul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [spec, hYsum, hsub, Finset.smul_sum, smul_smul]
        refine Finset.sum_comm.trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_)
        have hp : ((l : ℕ) : Qbar l) ^ (M + c₁) =
            ((l : ℕ) : Qbar l) ^ (M - m x) * ((l : ℕ) : Qbar l) ^ (m x + c₁) := by
          rw [← pow_add]
          congr 1
          have := hmM x
          omega
        rw [hp]
        congr 1
        ring
      · simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]
    beta_reduce
    rw [hL, hR]
    exact hcv i
  · intro B σ hB hF
    obtain ⟨he1, htr, hdet⟩ := hfrob B σ hB hF
    exact hEC.2 σ hInt.2.1 he1 htr hdet
end
