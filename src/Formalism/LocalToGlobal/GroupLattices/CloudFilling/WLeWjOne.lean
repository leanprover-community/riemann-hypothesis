module

public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.CloudBound
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.SharpRestriction.InertJacobiLevels.VVEqEmptyOfNotIsResidueClassZero

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.FrobeniusOrbits

namespace Formalism.L2.G

theorem wG_idx (R : Ranks) (e : Fin R.m → ℚ) (b j : ℕ) (hb : b < R.m) (hj : j - 1 < R.m) (h : b = j - 1) (h1 : 1 ≤ j) :
    wG R (e ⟨b, hb⟩) (b + 1) = wG R (e ⟨j - 1, hj⟩) j := by
  subst h
  rw [Nat.sub_add_cancel h1]

theorem wRec_eq (D : D7) (u : D.what₂.Word) (g : D.R.Psi) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    ((wRec D u g j : ℤ) : ℝ) = wj D j (D.eTau.symm g) - Formalism.MainNotions.G.kaJ D j := by
  have hj' := Finset.mem_Icc.1 hj
  have hjm : j - 1 < D.R.m := by omega
  have h := (D.fm u).lam_eq D.R.m le_rfl (D.eTau.symm g)
    ⟨D.R.k + (min j D.R.m - 1) * (D.R.t + 1), blkIdx_lt D.R j⟩
  rw [dite_eq_right (by show ¬ D.R.k + (min j D.R.m - 1) * (D.R.t + 1) < D.R.k; omega)] at h
  have hb : (D.R.k + (min j D.R.m - 1) * (D.R.t + 1) - D.R.k) / (D.R.t + 1) = j - 1 := by
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _), min_eq_left hj'.2]
  have h' : ((((D.fm u).lam D.R.m (D.eTau.symm g)).w
      ⟨D.R.k + (min j D.R.m - 1) * (D.R.t + 1), blkIdx_lt D.R j⟩ : ℤ) : ℚ) =
      -wG D.R ((D.hcW u (D.eTau.symm g)).e ⟨j - 1, hjm⟩) j := by
    rw [h]
    exact congrArg Neg.neg (wG_idx D.R _ _ j _ hjm hb hj'.1)
  rw [D.hcW_e] at h'
  have h'' := congrArg (fun q : ℚ => (q : ℝ)) h'
  simp only [wG] at h''
  push_cast at h''
  unfold wRec wj Formalism.MainNotions.G.kaJ
  rw [dite_eq_left hjm]
  push_cast
  rw [h'']
  ring

theorem lamRec_real (D : D7) (u : D.what₂.Word) (g : D.R.Psi) (i : Fin (D.R.k - 1 + 1)) (hi : i.1 < D.R.k) :
    ((lamRec D u g i : ℤ) : ℝ) =
      (((D.hcW u (D.eTau.symm g)).u ⟨i.1, hi⟩ : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ)) := by
  have h := (D.fm u).lam_eq 0 (Nat.zero_le _) (D.eTau.symm g) ⟨i.1, by simp only [Ranks.N]; omega⟩
  rw [dite_eq_left hi] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [hcToWeightQ, rhoVec] at h'
  push_cast at h'
  exact h'

theorem lamRec_top {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (g : D.R.Psi) (t : D.host.TT)
    (ht : (g : D.R.GG) = D.R.tau1 t) :
    lamRec D u g 0 = L.aT t ∧ lamRec D u g (Fin.last _) = -L.bT t := by
  have hk := k_pred D.R
  have hk0 : 0 < D.R.k := by omega
  have hkR : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have tu := L.top_u (D.eTau.symm g) t hk0 (by rw [Equiv.apply_symm_apply]; exact ht)
  constructor
  · have h := lamRec_real D u g 0 (by simpa using hk0)
    apply Int.cast_injective (α := ℝ)
    rw [h]
    have e : (⟨(0 : Fin (D.R.k - 1 + 1)).1, by simpa using hk0⟩ : Fin D.R.k) = ⟨0, hk0⟩ := Fin.ext (by simp)
    rw [e, D.hcW_first u _ hk0, tu.1]
    simp
  · have h := lamRec_real D u g (Fin.last _) (by simp only [Fin.val_last]; omega)
    apply Int.cast_injective (α := ℝ)
    rw [h]
    have e : (⟨(Fin.last (D.R.k - 1)).1, by simp only [Fin.val_last]; omega⟩ : Fin D.R.k) =
        ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only [Fin.val_last])
    rw [e, D.hcW_last u _ hk0, tu.2]
    simp only [Fin.val_last]
    rw [hkR]
    push_cast
    ring

end Formalism.L2.G
