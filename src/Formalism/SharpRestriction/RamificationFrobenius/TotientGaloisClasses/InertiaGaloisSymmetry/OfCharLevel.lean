module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfCharFrame
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

@[expose] public section

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

theorem unitsMap_unitOfCoprime {M N : ℕ} (h : M ∣ N) (a : ℕ) (ha : Nat.Coprime a N) :
    ZMod.unitsMap h (ZMod.unitOfCoprime a ha) = ZMod.unitOfCoprime a (ha.coprime_dvd_right h) := by
  ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]

theorem HostRaw.art_eq_of_prim_eq {φ : Frame} (H : HostRaw φ) {θ θ' : φ.Char} (h : H.prim θ = H.prim θ')
    (u : (ZMod H.condN)ˣ) : θ (H.art u) = θ' (H.art u) := by
  have h1 := (H.isPrimOf_prim θ).2 _ (ZMod.val_coe_unit_coprime u)
  have h2 := ((H.isPrimOf_iff θ' _).mpr h).2 _ (ZMod.val_coe_unit_coprime u)
  have h3 := h1.symm.trans h2
  rw [HostRaw.dirAt, HostRaw.dirAt, ZMod.natCast_zmod_val, H.dir_unit, H.dir_unit] at h3
  exact Units.ext h3

namespace EvenGrp

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

def ann : Subgroup (ZMod M)ˣ := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).symm (OrderDual.toDual Ξ)

theorem mem_ann (u : (ZMod M)ˣ) : u ∈ ann Ξ ↔ ∀ χ ∈ Ξ, χ u = 1 := by
  simp [ann]

theorem mem_iff (χ : DirichletCharacter ℂ M) : χ ∈ Ξ ↔ ∀ u ∈ ann Ξ, χ u = 1 := by
  have h1 := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).apply_symm_apply (OrderDual.toDual Ξ)
  have h2 : χ ∈ Ξ ↔ χ ∈ OrderDual.ofDual ((MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ) (ann Ξ)) := by
    simp only [ann, h1, OrderDual.ofDual_toDual]
  rw [h2]
  generalize ann Ξ = S
  simp

abbrev B : Type := (ZMod M)ˣ ⧸ ann Ξ

theorem card_B : Nat.card (B Ξ) = Nat.card Ξ := by
  rw [← MulChar.card_subgroupOrderIsoSubgroupMulChar (R := ℂ), ann, OrderIso.apply_symm_apply]
  rfl

instance neZero_lcm : NeZero (Nat.lcm (2 ^ (e + 2)) M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩

def xiW : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ →* B Ξ := (QuotientGroup.mk' _).comp (ZMod.unitsMap (Nat.dvd_lcm_right _ _))

theorem xiW_surj : Function.Surjective (xiW Ξ e) := by
  intro b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (ann Ξ) b
  obtain ⟨c, rfl⟩ := ZMod.unitsMap_surjective (Nat.dvd_lcm_right (2 ^ (e + 2)) M) a
  exact ⟨c, rfl⟩

def Good (m : ℕ) : Prop := m ∣ Nat.lcm (2 ^ (e + 2)) M ∧ 2 ^ (e + 2) ∣ m ∧
  ∀ u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ, (u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val ≡ 1 [MOD m] → xiW Ξ e u = 1

theorem exists_good : ∃ m, Good Ξ e m := by
  refine ⟨Nat.lcm (2 ^ (e + 2)) M, dvd_rfl, Nat.dvd_lcm_left _ _, fun u hu => ?_⟩
  have h1 : ((u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val : ZMod (Nat.lcm (2 ^ (e + 2)) M)) =
      ((1 : ℕ) : ZMod (Nat.lcm (2 ^ (e + 2)) M)) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h1
  have h2 : u = 1 := Units.ext (by rw [h1, Units.val_one])
  rw [h2, map_one]

open Classical in
def QS : ℕ := Nat.find (exists_good Ξ e)

open Classical in
theorem good_QS : Good Ξ e (QS Ξ e) := Nat.find_spec (exists_good Ξ e)

open Classical in
theorem not_good {m : ℕ} (h : m < QS Ξ e) : ¬ Good Ξ e m := Nat.find_min (exists_good Ξ e) h

theorem QS_dvd : QS Ξ e ∣ Nat.lcm (2 ^ (e + 2)) M := (good_QS Ξ e).1

theorem QS_dvd_mul : QS Ξ e ∣ 2 ^ (e + 2) * M :=
  (QS_dvd Ξ e).trans (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))

theorem QS_pos : 0 < QS Ξ e := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have h1 := QS_dvd Ξ e
  rw [h, zero_dvd_iff] at h1
  exact (NeZero.ne _) h1

instance neZero_QS : NeZero (QS Ξ e) := ⟨(QS_pos Ξ e).ne'⟩

def xi : (ZMod (QS Ξ e))ˣ →* B Ξ :=
  (ZMod.unitsMap (QS_dvd Ξ e)).liftOfSurjective (ZMod.unitsMap_surjective _)
    ⟨xiW Ξ e, fun u hu => (good_QS Ξ e).2.2 u ((unitsMap_eq_one_iff _ u).mp hu)⟩

theorem xi_unitsMap (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) : xi Ξ e (ZMod.unitsMap (QS_dvd Ξ e) u) = xiW Ξ e u :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem xi_surj : Function.Surjective (xi Ξ e) := by
  intro b
  obtain ⟨u, rfl⟩ := xiW_surj Ξ e b
  exact ⟨_, xi_unitsMap Ξ e u⟩

variable (hev : ∀ χ ∈ Ξ, χ.Even)

theorem dvd_of_dvd_QS {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (h : l ∣ QS Ξ e) : l ∣ M := by
  rcases (Nat.Prime.dvd_mul hl).mp (h.trans (QS_dvd_mul Ξ e)) with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h1)) h2
  · exact h1

def thetaB (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : B Ξ →* ℂˣ :=
  QuotientGroup.lift (ann Ξ) χ.toUnitHom fun u hu =>
    Units.ext ((MulChar.coe_toUnitHom χ u).trans ((mem_ann Ξ u).mp hu χ hχ))

section Host

variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)

include hH hc in
theorem coprime_QS : Nat.Coprime (QS Ξ e) (q * d) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH
  have h2 : Nat.Coprime 2 (q * d) := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · exact (Nat.coprime_primes Nat.prime_two hq).mpr (by omega)
    · exact (Nat.coprime_primes Nat.prime_two hd).mpr (by omega)
  exact Nat.Coprime.coprime_dvd_left (QS_dvd_mul Ξ e) (Nat.Coprime.mul_left (Nat.Coprime.pow_left _ h2) hc)

end Host

end EvenGrp

end Formalism.HC

end
