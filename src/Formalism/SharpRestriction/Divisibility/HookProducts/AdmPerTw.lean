module
public import Formalism.LocalRingCardinality.DataErr
public import Formalism.LocalRingCardinality.DataKerP
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces

@[expose] public section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField

namespace Formalism.MainNotions.DIV.HookProducts.AdmPerTw

variable {D : D7}

theorem vAdd_dvd_le (w : D.what₂.places.Pl) {n N : ℕ} (hN : N ≠ 0) (hd : n ∣ N) :
    (vAdd (D.plEq w) (n : D.what₂.LL) : ℝ) ≤ ur D w (padicValNat (D.what₂.places.resChar w) N : ℝ) := by
  let p := D.what₂.places.resChar w
  have hp : p.Prime := D.what₂.places.resChar_prime w
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (ne_zero_of_dvd_ne_zero hN hd) p hp.ne_one
  have hm0 : (m : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr fun h => hm (h ▸ dvd_zero p)
  rw [Nat.cast_mul, Nat.cast_pow, OrbitPlaces.vAdd_mul w (pow_ne_zero _ (OrbitPlaces.p_ne w)) hm0,
    OrbitPlaces.vAdd_pow]
  rw [show vAdd (D.plEq w) (m : D.what₂.LL) = 0 by
      simpa [D.val_eq w _ hm0] using OrbitPlaces.val_coprime w m (hp.coprime_iff_not_dvd.mpr hm).symm,
    add_zero, ur, mul_comm (D.what₂.places.ramIdx w : ℝ), Nat.padicValNat_def]
  push_cast
  gcongr
  exact (Nat.pow_dvd_iff_le_multiplicity hp.ne_one hN).mp ((dvd_mul_right _ _).trans hd)

theorem card_stabilizer_dvd₂ (hD : DGamDef D) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (c : (T.fm u μ).clsP) :
    Nat.card ((T.fm u μ).stabilizer₂ c) ∣ (D.mem u).C.DGam := by
  rw [← DGamDef.one hD u u μ]
  refine dvd_trans ?_ ((D.chTw u μ).dvd_DGam D.R.m le_rfl ((T.fm u μ).til c))
  rw [Nat.card_congr (MonoidHom.ofInjective ((T.fm u μ).stabMap_inj c)).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end Formalism.MainNotions.DIV.HookProducts.AdmPerTw
