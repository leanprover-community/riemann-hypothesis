module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfChar
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSymOfModEq
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

@[expose] public section

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

theorem unitsMap_eq_iff {M N : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (u : (ZMod N)ˣ) (v : (ZMod M)ˣ) :
    ZMod.unitsMap h u = v ↔ (u : ZMod N).val ≡ (v : ZMod M).val [MOD M] := by
  rw [Units.ext_iff, D7.unitsMap_val, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]

theorem unitsMap_eq_one_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h u = 1 ↔ (u : ZMod N).val ≡ 1 [MOD M] := by
  haveI : NeZero M := ⟨by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd h)⟩
  rw [unitsMap_eq_iff h u 1, Units.val_one, ZMod.val_one_eq_one_mod]
  exact ⟨fun h1 => h1.trans (Nat.mod_modEq 1 M), fun h1 => h1.trans (Nat.mod_modEq 1 M).symm⟩

theorem unitsMap_val_modEq {M N : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (u : (ZMod N)ˣ) :
    (u : ZMod N).val ≡ ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M).val [MOD M] :=
  (unitsMap_eq_iff h u _).mp rfl

theorem exists_unit_three {a b c : ℕ} [NeZero (a * b * c)] (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (x y z : ℕ) (hx : Nat.Coprime x a) (hy : Nat.Coprime y b) (hz : Nat.Coprime z c) :
    ∃ u : (ZMod (a * b * c))ˣ, (u : ZMod (a * b * c)).val ≡ x [MOD a] ∧
      (u : ZMod (a * b * c)).val ≡ y [MOD b] ∧ (u : ZMod (a * b * c)).val ≡ z [MOD c] := by
  obtain ⟨t1, h1a, h1b⟩ := Nat.chineseRemainder hab x y
  obtain ⟨t, h2ab, h2c⟩ := Nat.chineseRemainder (Nat.Coprime.mul_left hac hbc) t1 z
  have hta : t ≡ x [MOD a] := (h2ab.of_mul_right b).trans h1a
  have htb : t ≡ y [MOD b] := (h2ab.of_mul_left a).trans h1b
  have hca : Nat.Coprime t a := hta.gcd_eq.trans hx
  have hcb : Nat.Coprime t b := htb.gcd_eq.trans hy
  have hcc : Nat.Coprime t c := h2c.gcd_eq.trans hz
  have hcop : Nat.Coprime t (a * b * c) := Nat.Coprime.mul_right (Nat.Coprime.mul_right hca hcb) hcc
  have hm := Nat.mod_modEq t (a * b * c)
  refine ⟨ZMod.unitOfCoprime t hcop, ?_, ?_, ?_⟩ <;> rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  · exact ((hm.of_mul_right c).of_mul_right b).trans hta
  · exact ((hm.of_mul_right c).of_mul_left a).trans htb
  · exact (hm.of_mul_left (a * b)).trans h2c

attribute [instance] EvenData.grp

namespace EvenData

variable (D : EvenData)

instance neZero : NeZero D.m := ⟨D.m_pos.ne'⟩

instance : Finite D.R := Finite.of_surjective _ D.eta.rangeRestrict_surjective

instance : Fintype (Additive D.R) := Fintype.ofFinite _

section Host

variable {q d : ℕ} (hH : HostHyp q d)

variable (hc : Nat.Coprime D.m (q * d))

variable (he : 2 ≤ D.e) (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ D.m → jacobiSym (-(d : ℤ)) l = 1)

end Host

end EvenData

end Formalism.HC

end
