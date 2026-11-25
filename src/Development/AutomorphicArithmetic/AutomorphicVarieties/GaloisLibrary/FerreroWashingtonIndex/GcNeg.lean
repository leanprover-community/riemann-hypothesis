module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.gcNeg :
    ∀ (M c : ℕ) [NeZero M] (s : ZMod M), c.Coprime M → Odd c → s ≠ 0 → gc M c (-s) = -gc M c s := by
  intro M c _ s hc hodd hs
  unfold gc
  have hcu : IsUnit (c : ZMod M) := (ZMod.isUnit_iff_coprime c M).mpr hc
  have ht : (c : ZMod M)⁻¹ * -s = -((c : ZMod M)⁻¹ * s) := by ring
  have ht0 : (c : ZMod M)⁻¹ * s ≠ 0 := by
    intro h0
    apply hs
    calc s = ((c : ZMod M) * (c : ZMod M)⁻¹) * s := by rw [ZMod.mul_inv_of_unit _ hcu, one_mul]
      _ = (c : ZMod M) * ((c : ZMod M)⁻¹ * s) := by ring
      _ = 0 := by rw [h0, mul_zero]
  haveI : NeZero ((c : ZMod M)⁻¹ * s) := ⟨ht0⟩
  rw [ht, ZMod.val_neg_of_ne_zero]
  have hv0 : 0 < ((c : ZMod M)⁻¹ * s).val := ZMod.val_pos.mpr ht0
  have hvM : ((c : ZMod M)⁻¹ * s).val < M := ZMod.val_lt _
  generalize ((c : ZMod M)⁻¹ * s).val = v at hv0 hvM ⊢
  have hMpos : 0 < M := by omega
  have hcpos : 0 < c := hodd.pos
  have hndvd : (c * v) % M ≠ 0 := by
    intro h0
    have h1 : M ∣ c * v := Nat.dvd_of_mod_eq_zero h0
    have h2 : M ∣ v := (Nat.Coprime.dvd_mul_left hc.symm).mp h1
    have := Nat.le_of_dvd hv0 h2
    omega
  have hlt : c * v < c * M := Nat.mul_lt_mul_of_pos_left hvM hcpos
  have hpos : 0 < c * v := Nat.mul_pos hcpos hv0
  have hltM : c * v < M * c := Nat.mul_comm c M ▸ hlt
  have h1 := Nat.mul_sub_div (c * v - 1) M c (Nat.lt_of_le_of_lt (Nat.sub_le _ 1) hltM)
  have h2 := Nat.succ_div_of_mod_ne_zero (a := c * v - 1) (b := M)
    ((Nat.sub_add_cancel hpos).symm ▸ hndvd)
  rw [Nat.sub_add_cancel hpos] at h2
  rw [Nat.sub_add_cancel hpos, Nat.mul_comm M c, ← h2] at h1
  have hlt' : c * v / M < c := Nat.div_lt_of_lt_mul hltM
  have key : (c * M - c * v) / M + c * v / M + 1 = c := by
    rw [h1, Nat.add_assoc, Nat.sub_add_cancel hlt']
  rw [mul_tsub]
  obtain ⟨m, rfl⟩ := hodd
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm]
  generalize ((2 * m + 1) * M - (2 * m + 1) * v) / M = P at key ⊢
  generalize (2 * m + 1) * v / M = Q at key ⊢
  omega
