import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaGeCOfNorm
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThRestGcVOf
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.BiadditiveSecondVariable

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section Idx

variable {n' ν : ℕ} [NeZero ν] (hn : n' = 2 * ν)

theorem ea_eS_val (s : Fin n') : (ea_eS hn s).val = s.val := by
  show (((s.val : ℕ) : ZMod (2 * ν))).val = s.val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hn ▸ s.isLt)]


theorem ea_eS_posAdd (s : Fin n') (k : ℕ) : ea_eS hn (posAdd s k) = ea_eS hn s + (k : ZMod (2 * ν)) := by
  subst hn
  show (((s.val + k) % (2 * ν) : ℕ) : ZMod (2 * ν)) = (s.val : ZMod (2 * ν)) + k
  rw [ZMod.natCast_mod, Nat.cast_add]

theorem ea_eS_sub_val (s s' : Fin n') : (ea_eS hn s' - ea_eS hn s).val = (s'.val + n' - s.val) % n' := by
  subst hn
  have hle : s.val ≤ s'.val + 2 * ν := by have := s.isLt; omega
  show (((s'.val : ℕ) : ZMod (2 * ν)) - ((s.val : ℕ) : ZMod (2 * ν))).val = _
  rw [← ZMod.val_natCast (n := 2 * ν) (s'.val + 2 * ν - s.val)]
  congr 1
  rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero]

end Idx

theorem ea_card_fin (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun c : Fin N => P c.val).card = ((range N).filter P).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.isLt, hc⟩
  · rintro ⟨hx, hP⟩
    exact ⟨⟨x, hx⟩, hP, rfl⟩

theorem ea_lg (p x : ℕ) : Formalism.InvariantFactorPaths.G7.lgN p x = lgp p (x : ℤ) := by
  unfold Formalism.InvariantFactorPaths.G7.lgN lgp
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [if_neg (by omega), if_neg (by omega)]
    simp

section Num

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ} {ν : ℕ} [NeZero ν] (hn : n' = 2 * ν)

def ea_cN (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (J : ℕ) (s : ZMod (2 * ν)) : ℕ :=
  (nu t lam0 w J ((ea_eS hn).symm s) 1).toNat

def ea_hT (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (J : ℕ) (s : ZMod (2 * ν))
    (x : Fin (ea_cN hn t lam0 w J s)) : ℕ := ea_colH t lam0 w J ((ea_eS hn).symm s) x.val

def ea_tT (TT : Finset (Fin n')) : Finset (ZMod (2 * ν)) := TT.map (ea_eS hn).toEmbedding

theorem ea_mem_tT (s : ZMod (2 * ν)) : s ∈ ea_tT hn TT ↔ (ea_eS hn).symm s ∈ TT := by
  unfold ea_tT
  rw [Finset.mem_map_equiv]

variable (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m)

include h hJ1 hJ

theorem ea_alG (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) =
      al TT lam0 ((ea_eS hn).symm s) := by
  unfold Formalism.InvariantFactorPaths.G7.alG al
  by_cases hs : (ea_eS hn).symm s ∈ TT
  · rw [if_pos ((ea_mem_tT hn s).2 hs), if_pos hs]
    have e := ea_card_fin (ea_cN hn t lam0 w J s) (fun x => ea_colH t lam0 w J ((ea_eS hn).symm s) x = 1)
    unfold ea_hT
    rw [e]
    exact ea_card_one h hJ1 hJ _
  · rw [if_neg (fun h' => hs ((ea_mem_tT hn s).1 h')), if_neg hs]
    rfl

theorem ea_cN_cast (s : ZMod (2 * ν)) :
    ((ea_cN hn t lam0 w J s : ℕ) : ℤ) = nu t lam0 w J ((ea_eS hn).symm s) 1 :=
  Int.toNat_of_nonneg (ea_nu_nonneg h hJ1 hJ _ 1)

theorem ea_al_eq (s : Fin n') (hs : s ∈ TT) : al TT lam0 s = nu t lam0 w J s 1 - nu t lam0 w J s 2 := by
  have hk : 2 ≤ k1 + 1 := by
    have := h.two_r
    have := h.r_pos
    omega
  unfold al
  rw [if_pos hs, ea_nu_head J s le_rfl (by omega), ea_nu_head J s (by omega : 1 ≤ 2) hk]
  ring

theorem ea_capG (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) =
      cap t TT lam0 w J ((ea_eS hn).symm s) := by
  have hA := ea_alG hn h hJ1 hJ s
  have hC := ea_cN_cast hn h hJ1 hJ s
  unfold Formalism.InvariantFactorPaths.G7.capG cap
  by_cases hs : (ea_eS hn).symm s ∈ TT
  · rw [if_pos hs]
    have hal := ea_al_eq h hJ1 hJ _ hs
    have h2 := ea_nu_nonneg h hJ1 hJ ((ea_eS hn).symm s) 2
    have hle : Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s ≤
        ea_cN hn t lam0 w J s := by
      have : ((Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) ≤
          ((ea_cN hn t lam0 w J s : ℕ) : ℤ) := by rw [hA, hC, hal]; omega
      exact_mod_cast this
    rw [Nat.cast_sub hle, hA, hC, hal]
    ring
  · rw [if_neg hs]
    have h0 : Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s = 0 := by
      unfold Formalism.InvariantFactorPaths.G7.alG
      rw [if_neg (mt (ea_mem_tT hn s).1 hs)]
    rw [h0, Nat.sub_zero, hC]

theorem ea_lsG (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) =
      lsz t TT lam0 w J ((ea_eS hn).symm s) := by
  have hle : Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s ≤
      ∑ c : Fin (ea_cN hn t lam0 w J s), ea_hT hn t lam0 w J s c := by
    unfold Formalism.InvariantFactorPaths.G7.alG
    split_ifs
    · rw [Finset.card_filter]
      exact Finset.sum_le_sum fun c _ => by split_ifs with h1 <;> omega
    · exact Nat.zero_le _
  unfold Formalism.InvariantFactorPaths.G7.lsG lsz
  rw [Nat.cast_sub hle, ea_alG hn h hJ1 hJ s, ← ea_sum_colH h hJ1 hJ]
  congr 2
  unfold ea_hT ea_cN
  exact Fin.sum_univ_eq_sum_range (fun x => ea_colH t lam0 w J ((ea_eS hn).symm s) x) _

end Num

section Num2

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ} {ν : ℕ} [NeZero ν] (hn : n' = 2 * ν)

theorem ea_dSet (s : Fin n') : Formalism.InvariantFactorPaths.G7.dSet (ea_tT hn TT) (ea_eS hn s) = dSet TT s := by
  unfold Formalism.InvariantFactorPaths.G7.dSet dSet ea_tT
  rw [Finset.filter_map, Finset.map_eq_image, Finset.image_image]
  congr 1
  · funext s'
    simp only [Function.comp_apply, Equiv.coe_toEmbedding]
    rw [ea_eS_sub_val]
  · ext s'
    simp only [Finset.mem_filter, Function.comp_apply, Equiv.coe_toEmbedding, ea_eS_val]

theorem ea_sum_tT {M : Type} [AddCommMonoid M] (f : ZMod (2 * ν) → M) :
    ∑ s ∈ ea_tT hn TT, f s = ∑ s ∈ TT, f (ea_eS hn s) := Finset.sum_map _ _ _

variable (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m)

include h hJ1 hJ

theorem ea_alG_R (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℝ) =
      (al TT lam0 ((ea_eS hn).symm s) : ℝ) := by
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (ea_alG hn h hJ1 hJ s)

theorem ea_capG_R (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℝ) =
      (cap t TT lam0 w J ((ea_eS hn).symm s) : ℝ) := by
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (ea_capG hn h hJ1 hJ s)

theorem ea_deLoss :
    Formalism.InvariantFactorPaths.G7.deLoss p (NN k1 t (J - 1)) (NN k1 t J) (ea_tT hn TT)
      (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))
      (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J)) = de p t TT lam0 w J := by
  have hal : ∀ s, ((Formalism.InvariantFactorPaths.G7.lgN p (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J)
      (ea_hT hn t lam0 w J) s) : ℕ) : ℝ) = (lgp p (al TT lam0 ((ea_eS hn).symm s)) : ℝ) := by
    intro s; rw [ea_lg, ea_alG hn h hJ1 hJ s]
  have hls : ∀ s, ((Formalism.InvariantFactorPaths.G7.lgN p (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J)
      (ea_hT hn t lam0 w J) s) : ℕ) : ℝ) = (lgp p (lsz t TT lam0 w J ((ea_eS hn).symm s)) : ℝ) := by
    intro s; rw [ea_lg, ea_lsG hn h hJ1 hJ s]
  unfold Formalism.InvariantFactorPaths.G7.deLoss de
  congr 1
  · rw [← (ea_eS hn).sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hal, hls, Equiv.symm_apply_apply]
  · rw [ea_sum_tT hn]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hal, Equiv.symm_apply_apply]

theorem gain_of_capacity_loss :
    Formalism.GrowthSums.excessGain (p : ℝ) (ea_tT hn TT) (Formalism.InvariantFactorPaths.G7.dSet (ea_tT hn TT))
      (fun s => (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (fun s => (Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (Formalism.InvariantFactorPaths.G7.deLoss p (NN k1 t (J - 1)) (NN k1 t J) (ea_tT hn TT)
        (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))
        (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))) = gA p t TT lam0 w J := by
  unfold Formalism.GrowthSums.excessGain gA
  rw [ea_deLoss hn h hJ1 hJ, ea_sum_tT hn]
  simp only [← ea_eS_posAdd hn, ea_dSet hn, ea_alG_R hn h hJ1 hJ, ea_capG_R hn h hJ1 hJ,
    Equiv.symm_apply_apply]

theorem ea_gainG :
    Formalism.GrowthSums.gainG (p : ℝ) (ea_tT hn TT) (Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT))
      (fun s => (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (fun s => (Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (Formalism.InvariantFactorPaths.G7.deLoss p (NN k1 t (J - 1)) (NN k1 t J) (ea_tT hn TT)
        (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))
        (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))) = gB p t TT lam0 w J := by
  have hodd : Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT) = (TT.filter fun s => IsOddPos s).map (ea_eS hn).toEmbedding := by
    unfold Formalism.InvariantFactorPaths.G7.oddT ea_tT
    rw [Finset.filter_map]
    congr 1
    ext s
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, ea_eS_val]
    exact Iff.rfl
  have hg : Formalism.GrowthSums.gamP (p : ℝ) = gam p := by
    unfold Formalism.GrowthSums.gamP Formalism.GrowthSums.rhoP gam; ring
  unfold Formalism.GrowthSums.gainG gB
  rw [ea_deLoss hn h hJ1 hJ, ea_sum_tT hn, hodd, Finset.sum_map, hg]
  simp only [Equiv.coe_toEmbedding, ← ea_eS_posAdd hn, ea_alG_R hn h hJ1 hJ, ea_capG_R hn h hJ1 hJ,
    Equiv.symm_apply_apply]

theorem ea_sumEven :
    ∑ s ∈ ea_tT hn TT \ Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT),
      (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ) =
      ((∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), al TT lam0 s : ℤ) : ℝ) := by
  have hodd : Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT) = (TT.filter fun s => IsOddPos s).map (ea_eS hn).toEmbedding := by
    unfold Formalism.InvariantFactorPaths.G7.oddT ea_tT
    rw [Finset.filter_map]
    congr 1
    ext s
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, ea_eS_val]
    exact Iff.rfl
  have hev : ea_tT hn TT \ Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT) =
      (TT.filter fun s => ¬ IsOddPos s).map (ea_eS hn).toEmbedding := by
    rw [hodd]
    unfold ea_tT
    rw [← Finset.map_sdiff]
    congr 1
    ext s
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [hev, Finset.sum_map, Int.cast_sum]
  simp only [Equiv.coe_toEmbedding, ea_alG_R hn h hJ1 hJ, Equiv.symm_apply_apply]

end Num2

theorem ea_brNum {p : ℕ} [Fact p.Prime] (X : Sys p) : ea_BrNum X := by
  intro v j hj
  exact ⟨gain_of_capacity_loss (ea_hn X v) (X.std v) (J := j + 1) (by omega) hj,
    ea_gainG (ea_hn X v) (X.std v) (J := j + 1) (by omega) hj,
    ea_sumEven (ea_hn X v) (X.std v) (J := j + 1) (by omega) hj⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Res

variable {ι κ R : Type} [CommRing R] (f : κ → ι)

theorem ea_coeff_resV (a : MvPowerSeries ι R) (n : κ →₀ ℕ) :
    MvPowerSeries.coeff n (resV f a) = MvPowerSeries.coeff (n.mapDomain f) a := rfl

variable {f} (hf : Function.Injective f)

include hf

theorem ea_resV_mul (a b : MvPowerSeries ι R) : resV f (a * b) = resV f a * resV f b := by
  classical
  ext n
  rw [ea_coeff_resV, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  simp_rw [ea_coeff_resV]
  symm
  refine Finset.sum_nbij' (fun q => (q.1.mapDomain f, q.2.mapDomain f))
    (fun q => (q.1.comapDomain f hf.injOn, q.2.comapDomain f hf.injOn)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [← Finsupp.mapDomain_add, hq]
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [← Finsupp.comapDomain_add_of_injective hf, hq, Finsupp.comapDomain_mapDomain f hf]
  · intro q _
    simp only [Finsupp.comapDomain_mapDomain f hf]
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hs : ∀ m : ι →₀ ℕ, m ≤ n.mapDomain f → (↑m.support : Set ι) ⊆ Set.range f := by
      intro m hm x hx
      have hx' : x ∈ (n.mapDomain f).support := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff] at hx
        rw [Finsupp.mem_support_iff]
        have := hm x
        omega
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx')
      exact ⟨y, rfl⟩
    have h1 : q.1 ≤ n.mapDomain f := hq ▸ le_self_add
    have h2 : q.2 ≤ n.mapDomain f := hq ▸ le_add_self
    ext1
    · exact Finsupp.mapDomain_comapDomain f hf _ (hs _ h1)
    · exact Finsupp.mapDomain_comapDomain f hf _ (hs _ h2)
  · intro q _
    rfl

theorem ea_resV_C (c : R) : resV f (MvPowerSeries.C c : MvPowerSeries ι R) = MvPowerSeries.C c := by
  classical
  ext n
  rw [ea_coeff_resV, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  have h : n.mapDomain f = 0 ↔ n = 0 := by
    constructor
    · intro h
      exact Finsupp.mapDomain_injective hf (by rw [h, Finsupp.mapDomain_zero])
    · rintro rfl
      exact Finsupp.mapDomain_zero
  by_cases hn : n = 0
  · rw [if_pos (h.2 hn), if_pos hn]
  · rw [if_neg (mt h.1 hn), if_neg hn]

def ea_resHom : MvPowerSeries ι R →+* MvPowerSeries κ R where
  toFun := resV f
  map_one' := by
    have := ea_resV_C hf (1 : R)
    rwa [map_one, map_one] at this
  map_mul' := ea_resV_mul hf
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ea_resHom_apply (a : MvPowerSeries ι R) : ea_resHom hf a = resV f a := rfl

omit hf in
theorem ea_resV_atPi (vp : R) (a : MvPowerSeries ι R) : resV f (atPi vp a) = atPi vp (resV f a) := by
  ext n
  rw [ea_coeff_resV]
  simp only [atPi, MvPowerSeries.coeff_apply, resV, Finsupp.degree_mapDomain]

end Res

theorem ea_atPi_subst {σ R : Type} [CommRing R] (vp : R) (a : MvPowerSeries σ R) :
    MvPowerSeries.subst (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x : MvPowerSeries σ R)) a = atPi vp a := by
  have h : (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x : MvPowerSeries σ R)) =
      (Function.const σ vp) • MvPowerSeries.X := by
    funext x
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [h, ← MvPowerSeries.rescale_eq_subst]
  ext n
  rw [MvPowerSeries.coeff_rescale]
  simp only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, atPi,
    MvPowerSeries.coeff_apply, Finsupp.degree]
  rfl

theorem ea_eS_posSub {n' ν : ℕ} [NeZero ν] (hn : n' = 2 * ν) (s : Fin n') (d : ℕ) :
    ea_eS hn (posSub s d) = ea_eS hn s - (d : ZMod (2 * ν)) := by
  subst hn
  have hd : d ≤ (s : ℕ) + 2 * ν * d :=
    le_add_left (Nat.le_mul_of_pos_left d (by have := NeZero.pos ν; omega))
  show ((((s : ℕ) + 2 * ν * d - d) % (2 * ν) : ℕ) : ZMod (2 * ν)) = ((s : ℕ) : ZMod (2 * ν)) - (d : ZMod (2 * ν))
  have h0 : ((2 * ν : ℕ) : ZMod (2 * ν)) = 0 := ZMod.natCast_self _
  rw [ZMod.natCast_mod, Nat.cast_sub hd]
  push_cast at h0 ⊢
  rw [h0]
  ring

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem ea_eps_inj (v : X.Pl) (j : ℕ) : Function.Injective (ea_eps X v j) := by
  intro y z h
  simp only [ea_eps, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext ((ea_e X v).symm.injective h1) (Prod.ext h2 h3)

theorem ea_res_sSA (K' : Type) [Field K'] (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j))
    (b : Fin (NN X.G.P.m X.t (j + 1))) :
    resV (ea_eps X v j) (X.sSA K' j v s a b) = Formalism.InvariantFactorPaths.G7.sPos p (ea_e X v s) (a, b) := by
  classical
  have key : ∀ l : ℕ, ea_eps X v j (ea_e X v s - 2 * (l : ZMod _), a, b) =
      (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) := by
    intro l
    simp only [ea_eps, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and, and_true]
    rw [Equiv.symm_apply_eq]
    simp only [ea_e]
    rw [ea_eS_posSub]
    push_cast
    ring
  ext n
  rw [ea_coeff_resV]
  simp only [Sys.sSA, Formalism.InvariantFactorPaths.G7.sPos, MvPowerSeries.coeff_apply, Finsupp.degree_mapDomain]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hs : (Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l))) =
      Finsupp.mapDomain (ea_eps X v j) (Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)) := by
    rw [Finsupp.mapDomain_single, key l, pow_mul]
  have hiff : Finsupp.mapDomain (ea_eps X v j) n = Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l)) ↔
      n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l) := by
    rw [hs]
    exact (Finsupp.mapDomain_injective (ea_eps_inj X v j)).eq_iff
  by_cases h : n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (mt hiff.1 h), if_neg h]

theorem ea_res_hhA (K' : Type) [Field K'] (v : X.Pl) (j : ℕ) (u : Fin (X.G.P.n' v) → K') :
    resV (ea_eps X v j) (X.hhA K' j v u) = Formalism.InvariantFactorPaths.G7.hhS p fun s => u ((ea_e X v).symm s) := by
  rw [← ea_resHom_apply (ea_eps_inj X v j)]
  simp only [Sys.hhA, map_sum, map_mul, map_pow, ea_resHom_apply, ea_resV_C (ea_eps_inj X v j),
    ea_res_sSA]
  simp only [Formalism.InvariantFactorPaths.G7.hhS, Fintype.sum_prod_type]
  refine Fintype.sum_equiv (ea_e X v) _ _ (fun s => ?_)
  rw [Equiv.symm_apply_apply]
  simp only [ea_e, ea_eS_posAdd, Nat.cast_one]

theorem ea_brClass : ea_BrClass X := by
  intro v j K' _ _ vp u F hF
  obtain ⟨g, hg, hc⟩ := hF
  rw [ea_atPi_subst, ← ea_resV_atPi, ← ea_res_hhA]
  refine ⟨fun i => resV (ea_eps X v j) (g i), fun i n => ?_, fun n => ?_⟩
  · rw [ea_coeff_resV]
    exact hg i _
  · rw [ea_coeff_resV, hc, Finsupp.degree_mapDomain]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← ea_resHom_apply (ea_eps_inj X v j), ← map_pow, ← map_mul]
    rw [ea_resHom_apply, ea_coeff_resV]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem ea_applyD_scale {σ τ K : Type} [Field K] (q E : ℕ) (P : MvPolynomial σ (MvPolynomial τ ℤ))
    (f : MvPowerSeries σ K) :
    applyD ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) f = ((q : K) ^ E) • applyD P f := by
  classical
  have hc : ∀ n, MvPolynomial.coeff n ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) =
      (q : MvPolynomial τ ℤ) ^ E * MvPolynomial.coeff n P := by
    intro n
    have : (q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E = MvPolynomial.C ((q : MvPolynomial τ ℤ) ^ E) := by
      rw [map_pow, map_natCast]
    rw [this, MvPolynomial.coeff_C_mul]
  have hsub : ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P).support ⊆ P.support := by
    intro n hn
    rw [MvPolynomial.mem_support_iff, hc] at hn
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [h0, mul_zero] at hn
    exact hn rfl
  unfold applyD
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.notMem_support_iff.1 hn, map_zero, smul_zero]), Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc, map_mul, map_pow, map_natCast, smul_comm]
  congr 1
  rw [MvPolynomial.smul_eq_C_mul, map_pow, map_natCast]

theorem ea_applyD_zero {σ τ K : Type} [Field K] (f : MvPowerSeries σ K) :
    applyD (0 : MvPolynomial σ (MvPolynomial τ ℤ)) f = 0 := by
  unfold applyD
  rw [MvPolynomial.support_zero, Finset.sum_empty]

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem ea_PIvS_eq (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    PIvS X j I i0 v = (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^
      (∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I i0 v s c) * X.PIv j I v := by
  unfold PIvS Sys.PIv
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem ea_colFac_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ)
    (h : ¬ Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) : X.colFac j I v s c = 0 := by
  unfold Function.Injective at h
  push Not at h
  obtain ⟨x, y, hxy, hne⟩ := h
  unfold Sys.colFac
  refine Matrix.det_zero_of_column_eq hne fun k => ?_
  show (∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c x.val)⟩ : X.ZA j)) =
    ∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c y.val)⟩ : X.ZA j)
  have hxy' : I v s c x.val = I v s c y.val := hxy
  rw [hxy']

theorem ea_card_img {H N : ℕ} (g : Fin H → Fin N) (hg : Function.Injective g) (i : ℕ) :
    ((univ.image g) ∩ univ.filter (fun b : Fin N => b.val < i)).card =
      (univ.filter fun x : Fin H => (g x).val < i).card := by
  rw [← Finset.card_image_of_injective _ hg]
  congr 1
  ext b
  simp only [mem_inter, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨x, rfl⟩, hb⟩
    exact ⟨x, hb, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩

theorem ea_Exp_eq (v : X.Pl) (j i : ℕ) (I : X.ColCh j)
    (h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) :
    ∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I (fun _ => i) v s c =
      ea_Exp X v j i I := by
  unfold ea_Exp
  refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
  rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 := ea_card_img (ea_Ic X v j I s' c) (h ((ea_e X v).symm s') c.val) i
  have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
    (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
  have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
      univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
      ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
        fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
  rw [e3]
  unfold Sys.colExp
  have hv : ((ea_e X v).symm s').val = s'.val := rfl
  by_cases hodd : s'.val % 2 = 0
  · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
    rfl
  · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]

theorem ea_brScale : ea_BrScale X := by
  intro v j i K' _ F I n
  by_cases h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), c ∈ range (X.nuv v (j + 1) s 1).toNat →
      X.colFac j I v s c ≠ 0
  · by_cases h2 : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ),
        Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val
    · right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul, ea_Exp_eq X v j i I h2]
    ·
      right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul]
      congr 2
      unfold ea_Exp
      refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
      rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hinj : Function.Injective fun i' : Fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val) =>
          I v ((ea_e X v).symm s') c.val i'.val := by
        by_contra hni
        exact h _ c.val (mem_range.2 c.isLt) (ea_colFac_zero X j I v _ _ hni)
      have e1 := ea_card_img (ea_Ic X v j I s' c) hinj i
      have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
        (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
      have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
          univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
          ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
            fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
      rw [e3]
      unfold Sys.colExp
      have hv : ((ea_e X v).symm s').val = s'.val := rfl
      by_cases hodd : s'.val % 2 = 0
      · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
        rfl
      · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]
  · left
    push Not at h
    obtain ⟨s, c, hc, h0⟩ := h
    have hz : PIvS X j I (fun _ => i) v = 0 := by
      unfold PIvS
      refine Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero hc ?_)
      rw [h0, mul_zero]
    rw [hz, ea_applyD_zero, MvPolynomial.coeff_zero]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

structure nm_Hyp {K : Type*} [Field K] (R : Subring K) (p : ℕ) : Prop where
  one_lt : 1 < p
  val : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R
  rk : ∀ x : K, x ≠ 0 → (∃ n : ℕ, (p : K) ^ n / x ∈ R) ∧ (x⁻¹ ∉ R → ∃ n : ℕ, x ^ n / (p : K) ∈ R)
  pinv : (p : K)⁻¹ ∉ R

variable {K : Type*} [Field K] {R : Subring K} {p : ℕ}

theorem nm_p_ne (h : nm_Hyp R p) : (p : K) ≠ 0 := by
  intro h0
  apply h.pinv
  rw [h0, inv_zero]
  exact R.zero_mem

theorem nm_root (h : nm_Hyp R p) {y : K} {k : ℕ} (hk : 0 < k) (hy : y ^ k ∈ R) : y ∈ R := by
  by_contra hyR
  have hy0 : y ≠ 0 := fun h0 => hyR (h0 ▸ R.zero_mem)
  have hinv : y⁻¹ ∈ R := (h.val y).resolve_left hyR
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e : y ^ (m + 1) * y⁻¹ ^ m = y := by
    rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hy0, one_pow, mul_one]
  exact hyR (e ▸ R.mul_mem hy (R.pow_mem hinv _))

theorem nm_zpow_mem_iff (h : nm_Hyp R p) (k : ℤ) : (p : K) ^ k ∈ R ↔ 0 ≤ k := by
  constructor
  · intro hk
    by_contra hneg
    push_neg at hneg
    apply h.pinv
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    subst hn
    have e : (p : K) ^ (-((n : ℤ) + 1)) = ((p : K)⁻¹) ^ (n + 1) := by
      rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, inv_pow]
    exact nm_root h (Nat.succ_pos n) (e ▸ hk)
  · intro hk
    lift k to ℕ using hk
    rw [zpow_natCast]
    exact R.pow_mem (natCast_mem R p) k

variable (R p)

def nm_P (x : K) (a : ℤ) (b : ℕ) : Prop := x ^ b * (p : K) ^ (-a) ∈ R

def rationalLowerBounds (x : K) : Set ℝ := {q | ∃ (a : ℤ) (b : ℕ), 0 < b ∧ q = (a : ℝ) / b ∧ nm_P R p x a b}

def nm_v (x : K) : ℝ := sSup (rationalLowerBounds R p x)

variable {R p}

theorem nm_T_nonempty (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : (rationalLowerBounds R p x).Nonempty := by
  obtain ⟨n, hn⟩ := (h.rk x⁻¹ (inv_ne_zero hx)).1
  refine ⟨_, -(n : ℤ), 1, one_pos, rfl, ?_⟩
  unfold nm_P
  rw [pow_one, neg_neg, zpow_natCast, mul_comm]
  rwa [div_inv_eq_mul] at hn

theorem nm_T_bdd (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : BddAbove (rationalLowerBounds R p x) := by
  have hp0 := nm_p_ne h
  obtain ⟨n, hn⟩ := (h.rk x hx).1
  refine ⟨n, ?_⟩
  rintro q ⟨a, b, hb, rfl, hP⟩
  have hxb : x ^ b ≠ 0 := pow_ne_zero _ hx
  have e : (p : K) ^ ((n : ℤ) * b - a) = ((p : K) ^ n / x) ^ b * (x ^ b * (p : K) ^ (-a)) := by
    rw [sub_eq_add_neg, zpow_add₀ hp0, ← Nat.cast_mul, zpow_natCast, div_pow, ← pow_mul, div_eq_mul_inv,
      mul_assoc, inv_mul_cancel_left₀ hxb]
  have hmem : (p : K) ^ ((n : ℤ) * b - a) ∈ R := e ▸ R.mul_mem (R.pow_mem hn b) hP
  have h0 := (nm_zpow_mem_iff h _).1 hmem
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  have : (a : ℤ) ≤ (n : ℤ) * b := by linarith
  exact_mod_cast this

theorem nm_le_v (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) {a : ℤ} {b : ℕ} (hb : 0 < b) (hP : nm_P R p x a b) :
    (a : ℝ) / b ≤ nm_v R p x := by
  unfold nm_v
  exact le_csSup (nm_T_bdd h hx) ⟨a, b, hb, rfl, hP⟩

theorem nm_dich (h : nm_Hyp R p) (x : K) (a : ℤ) (b : ℕ) : nm_P R p x a b ∨ nm_P R p x⁻¹ (-a) b := by
  rcases h.val (x ^ b * (p : K) ^ (-a)) with h1 | h1
  · exact Or.inl h1
  · right
    unfold nm_P
    convert h1 using 1
    rw [mul_inv, inv_pow, neg_neg, zpow_neg, inv_inv]

theorem nm_P_mul (h : nm_Hyp R p) {x y : K} {a a' : ℤ} {b b' : ℕ} (hx : nm_P R p x a b) (hy : nm_P R p y a' b') :
    nm_P R p (x * y) (a * b' + a' * b) (b * b') := by
  unfold nm_P at *
  have e : (x * y) ^ (b * b') * (p : K) ^ (-(a * b' + a' * b)) =
      (x ^ b * (p : K) ^ (-a)) ^ b' * (y ^ b' * (p : K) ^ (-a')) ^ b := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← zpow_natCast ((p : K) ^ (-a)) b',
      ← zpow_natCast ((p : K) ^ (-a')) b, ← zpow_mul, ← zpow_mul, mul_comm b' b]
    have : (p : K) ^ (-(a * b' + a' * b)) = (p : K) ^ (-a * b') * (p : K) ^ (-a' * b) := by
      rw [← zpow_add₀ (nm_p_ne h)]; congr 1; ring
    rw [this]
    ring
  rw [e]
  exact R.mul_mem (R.pow_mem hx _) (R.pow_mem hy _)

theorem nm_v_mul_ge (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nm_v R p x + nm_v R p y ≤ nm_v R p (x * y) := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have h1 : ∀ q' ∈ rationalLowerBounds R p y, nm_v R p x ≤ nm_v R p (x * y) - q' := by
    rintro q' ⟨a', b', hb', rfl, hP'⟩
    apply csSup_le (nm_T_nonempty h hx)
    rintro q ⟨a, b, hb, rfl, hP⟩
    have h2 := nm_le_v h hxy (Nat.mul_pos hb hb') (nm_P_mul h hP hP')
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hbR' : (b' : ℝ) ≠ 0 := by exact_mod_cast hb'.ne'
    have e : (((a * b' + a' * b : ℤ) : ℝ)) / ((b * b' : ℕ) : ℝ) = (a : ℝ) / b + (a' : ℝ) / b' := by
      push_cast
      field_simp
    rw [e] at h2
    linarith
  have h3 : nm_v R p y ≤ nm_v R p (x * y) - nm_v R p x := by
    apply csSup_le (nm_T_nonempty h hy)
    intro q' hq'
    have := h1 q' hq'
    linarith
  linarith

theorem nm_v_one (h : nm_Hyp R p) : nm_v R p (1 : K) = 0 := by
  apply le_antisymm
  · apply csSup_le (nm_T_nonempty h one_ne_zero)
    rintro q ⟨a, b, hb, rfl, hP⟩
    unfold nm_P at hP
    rw [one_pow, one_mul] at hP
    have := (nm_zpow_mem_iff h _).1 hP
    have ha : (a : ℝ) ≤ 0 := by
      have : a ≤ 0 := by linarith
      exact_mod_cast this
    exact div_nonpos_of_nonpos_of_nonneg ha (Nat.cast_nonneg _)
  · have := nm_le_v h (one_ne_zero (α := K)) (a := 0) (b := 1) Nat.one_pos (by
      unfold nm_P
      simp only [pow_one, neg_zero, zpow_zero, mul_one]
      exact R.one_mem)
    simpa using this

theorem nm_v_inv (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : nm_v R p x⁻¹ = -nm_v R p x := by
  have hx' := inv_ne_zero hx
  have h1 : nm_v R p x + nm_v R p x⁻¹ ≤ 0 := by
    have := nm_v_mul_ge h hx hx'
    rwa [mul_inv_cancel₀ hx, nm_v_one h] at this
  have h2 : 0 ≤ nm_v R p x + nm_v R p x⁻¹ := by
    by_contra hneg
    have hlt : nm_v R p x < -nm_v R p x⁻¹ := by linarith
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rcases nm_dich h x q.num q.den with h3 | h3
    · have := nm_le_v h hx q.den_pos h3
      rw [← hq] at this
      linarith
    · have := nm_le_v h hx' q.den_pos h3
      have e : (((-q.num : ℤ)) : ℝ) / (q.den : ℝ) = -(q : ℝ) := by
        rw [hq]; push_cast; ring
      rw [e] at this
      linarith
  linarith

theorem nm_v_mul (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nm_v R p (x * y) = nm_v R p x + nm_v R p y := by
  apply le_antisymm _ (nm_v_mul_ge h hx hy)
  have h1 := nm_v_mul_ge h (mul_ne_zero hx hy) (inv_ne_zero hy)
  rw [mul_assoc, mul_inv_cancel₀ hy, mul_one, nm_v_inv h hy] at h1
  linarith

theorem nm_v_nonneg (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) (hxR : x ∈ R) : 0 ≤ nm_v R p x := by
  have := nm_le_v h hx (a := 0) (b := 1) Nat.one_pos (by
    unfold nm_P
    simp only [pow_one, neg_zero, zpow_zero, mul_one]
    exact hxR)
  simpa using this

theorem nm_v_neg (h : nm_Hyp R p) {x : K} (hxR : x ∉ R) : nm_v R p x < 0 := by
  have hx : x ≠ 0 := fun h0 => hxR (h0 ▸ R.zero_mem)
  obtain ⟨n, hn⟩ := (h.rk x⁻¹ (inv_ne_zero hx)).2 (by rwa [inv_inv])
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_div] at hn
      exact h.pinv hn
    · exact h0
  have h1 := nm_le_v h (inv_ne_zero hx) (a := 1) (b := n) hn0 (by
    unfold nm_P
    rw [zpow_neg_one, ← div_eq_mul_inv]
    exact hn)
  rw [nm_v_inv h hx] at h1
  have : (0 : ℝ) < ((1 : ℤ) : ℝ) / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    positivity
  linarith

theorem nm_v_nonneg_iff (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : 0 ≤ nm_v R p x ↔ x ∈ R :=
  ⟨fun h0 => by
    by_contra hxR
    exact absurd (nm_v_neg h hxR) (not_lt.2 h0), nm_v_nonneg h hx⟩

theorem nm_v_p (h : nm_Hyp R p) : nm_v R p (p : K) = 1 := by
  apply le_antisymm
  · apply csSup_le (nm_T_nonempty h (nm_p_ne h))
    rintro q ⟨a, b, hb, rfl, hP⟩
    unfold nm_P at hP
    rw [← zpow_natCast, ← zpow_add₀ (nm_p_ne h)] at hP
    have := (nm_zpow_mem_iff h _).1 hP
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    rw [div_le_one hb']
    have : a ≤ b := by linarith
    exact_mod_cast this
  · have := nm_le_v h (nm_p_ne h) (a := 1) (b := 1) Nat.one_pos (by
      unfold nm_P
      rw [pow_one, zpow_neg_one, mul_inv_cancel₀ (nm_p_ne h)]
      exact R.one_mem)
    simpa using this

theorem nm_v_add (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (nm_v R p x) (nm_v R p y) ≤ nm_v R p (x + y) := by
  have key : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → x / y ∈ R → nm_v R p y ≤ nm_v R p (x + y) := by
    intro x y _ hy hxy hR
    have e : x + y = y * (1 + x / y) := by field_simp; ring
    have h1 : 1 + x / y ≠ 0 := by
      intro h0
      apply hxy
      rw [e, h0, mul_zero]
    rw [e, nm_v_mul h hy h1]
    have := nm_v_nonneg h h1 (R.add_mem R.one_mem hR)
    linarith
  rcases h.val (x / y) with h1 | h1
  · exact le_trans (min_le_right _ _) (key hx hy hxy h1)
  · rw [inv_div] at h1
    rw [add_comm] at hxy ⊢
    exact le_trans (min_le_left _ _) (key hy hx hxy h1)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open scoped Classical

variable {K : Type*} [Field K] {R : Subring K} {p : ℕ}

variable (R p) in

def nm_N (x : K) : ℝ := if x = 0 then 0 else (p : ℝ) ^ (-nm_v R p x)

theorem nm_N_zero : nm_N R p (0 : K) = 0 := by
  simp [nm_N]

theorem nm_N_of_ne {x : K} (hx : x ≠ 0) : nm_N R p x = (p : ℝ) ^ (-nm_v R p x) := by
  simp [nm_N, hx]

theorem nm_pR (h : nm_Hyp R p) : (1 : ℝ) < p := by
  exact_mod_cast h.one_lt

theorem nm_N_nonneg (h : nm_Hyp R p) (x : K) : 0 ≤ nm_N R p x := by
  unfold nm_N
  split_ifs
  · exact le_rfl
  · exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).le

theorem nm_N_mul (h : nm_Hyp R p) (x y : K) : nm_N R p (x * y) = nm_N R p x * nm_N R p y := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  by_cases hy : y = 0
  · simp [nm_N, hy]
  rw [nm_N_of_ne (mul_ne_zero hx hy), nm_N_of_ne hx, nm_N_of_ne hy, nm_v_mul h hx hy, neg_add,
    Real.rpow_add (zero_lt_one.trans (nm_pR h))]

theorem nm_N_eq_zero (h : nm_Hyp R p) (x : K) : nm_N R p x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  · rw [nm_N_of_ne hx]
    simp only [hx, iff_false]
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).ne'

theorem nm_N_add (h : nm_Hyp R p) (x y : K) : nm_N R p (x + y) ≤ max (nm_N R p x) (nm_N R p y) := by
  by_cases hx : x = 0
  · simp only [hx, zero_add, nm_N_zero]
    exact le_max_right _ _
  by_cases hy : y = 0
  · simp only [hy, add_zero, nm_N_zero]
    exact le_max_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, nm_N_zero]
    exact le_max_of_le_left (nm_N_nonneg h x)
  rw [nm_N_of_ne hxy, nm_N_of_ne hx, nm_N_of_ne hy]
  have hp1 : (1 : ℝ) ≤ p := (nm_pR h).le
  have hm := nm_v_add h hx hy hxy
  rcases le_total (nm_v R p x) (nm_v R p y) with hle | hle
  · rw [min_eq_left hle] at hm
    exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
  · rw [min_eq_right hle] at hm
    exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))

theorem nm_N_p (h : nm_Hyp R p) : nm_N R p (p : K) = (p : ℝ)⁻¹ := by
  rw [nm_N_of_ne (nm_p_ne h), nm_v_p h, Real.rpow_neg_one]

theorem nm_N_le_one (h : nm_Hyp R p) (x : K) : nm_N R p x ≤ 1 ↔ x ∈ R := by
  by_cases hx : x = 0
  · subst hx
    simp only [nm_N_zero, zero_le_one, true_iff]
    exact R.zero_mem
  rw [nm_N_of_ne hx, ← nm_v_nonneg_iff h hx]
  have e : (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
  rw [e, Real.rpow_le_rpow_left_iff (nm_pR h), neg_nonpos]

def nm_abs (h : nm_Hyp R p) : AbsoluteValue K ℝ where
  toFun := nm_N R p
  map_mul' := nm_N_mul h
  nonneg' := nm_N_nonneg h
  eq_zero' := nm_N_eq_zero h
  add_le' x y := le_trans (nm_N_add h x y) (max_le_add_of_nonneg (nm_N_nonneg h x) (nm_N_nonneg h y))

theorem nm_extG {K : Type} [Field K] (N : AbsoluteValue K ℝ) (hna : ∀ x y, N (x + y) ≤ max (N x) (N y)) (c : K)
    (hc : 1 < N c) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra K K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ∀ x, ‖algebraMap K K' x‖ = N x := by
  let nK : NormedField K := N.toNormedField
  have hnorm : ∀ x : K, ‖x‖ = N x := fun _ => rfl
  have hnatK : ∀ n : ℕ, N (n : K) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact le_trans (hna _ _) (max_le ih (by simp))
  have hcast : ∀ n : ℕ, ((n : K) : UniformSpace.Completion K) = (n : UniformSpace.Completion K) := fun n =>
    map_natCast (UniformSpace.Completion.coeRingHom (α := K)) n
  have hnatC : ∀ n : ℕ, ‖(n : UniformSpace.Completion K)‖ ≤ 1 := by
    intro n
    rw [← hcast, UniformSpace.Completion.norm_coe]
    exact hnatK n
  have uC : IsUltrametricDist (UniformSpace.Completion K) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hnatC
  let nnC : NontriviallyNormedField (UniformSpace.Completion K) :=
    { (inferInstance : NormedField (UniformSpace.Completion K)) with
      non_trivial := ⟨(c : UniformSpace.Completion K), by rw [UniformSpace.Completion.norm_coe]; exact hc⟩ }
  let nL : NormedField (AlgebraicClosure (UniformSpace.Completion K)) :=
    spectralNorm.normedField (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
  have hext : ∀ z : UniformSpace.Completion K,
      ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K)) z‖ = ‖z‖ :=
    fun z => spectralNorm_extends z
  let aL : Algebra K (AlgebraicClosure (UniformSpace.Completion K)) :=
    ((algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))).comp
      (UniformSpace.Completion.coeRingHom (α := K))).toAlgebra
  refine ⟨AlgebraicClosure (UniformSpace.Completion K), nL, aL, ?_, inferInstance, ?_⟩
  · apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
    intro n
    have := hext (n : UniformSpace.Completion K)
    rw [map_natCast] at this
    rw [this]
    exact hnatC n
  · intro x
    show ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
      (x : UniformSpace.Completion K)‖ = N x
    rw [hext, UniformSpace.Completion.norm_coe]
    rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

theorem nm_pinv_of_eO (Y : Pend X) (he : 0 < X.eO) : (p : Y.Kc)⁻¹ ∉ Y.Oc := by
  intro hmem
  have hinj := algebraMap_inj Y he
  have hpO : (p : X.G.O) ≠ 0 := fun h0 =>
    pow_ne_zero _ X.unif.ne_zero (X.eO_spec.eq_zero_iff.mp h0)
  have hpK : (p : X.G.Kf) ≠ 0 := by
    have := (map_ne_zero_iff _ hinj).mpr hpO
    rwa [map_natCast] at this
  have h1 : algebraMap X.G.Kf Y.Kc ((p : X.G.Kf)⁻¹) ∈ Y.Oc := by
    rwa [map_inv₀, map_natCast]
  obtain ⟨a, ha⟩ := (mem_intK (X := X)).mp ((Y.Oc_K _).mp h1)

  have h1eq : (p : X.G.O) * a = 1 := hinj (by
    rw [map_mul, ha, map_natCast, mul_inv_cancel₀ hpK, map_one])
  have hpu : IsUnit (p : X.G.O) := IsUnit.of_mul_eq_one _ h1eq
  exact X.unif.not_isUnit
    ((isUnit_pow_iff (Nat.pos_iff_ne_zero.mp he)).mp (X.eO_spec.isUnit_iff.mp hpu))

theorem nm_pinv_of_place (Y : Pend X) (v : X.Pl) : (p : Y.Kc)⁻¹ ∉ Y.Oc :=
  nm_pinv_of_eO Y (eO_pos X v)

theorem nm_hyp (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) : nm_Hyp Y.Oc p :=
  ⟨hp.out.one_lt, Y.Oc_val, Y.Oc_rank1, h⟩

theorem nm_ext (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra Y.Kc K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ‖(p : K')‖ = (p : ℝ)⁻¹ ∧ (∀ x : Y.Kc, ‖algebraMap Y.Kc K' x‖ ≤ 1 ↔ x ∈ Y.Oc) ∧
      ∃ vp : K', vp ^ (p ^ 2 - 1) = (p : K') := by
  have hH := nm_hyp Y h
  have hc : 1 < nm_abs hH ((p : Y.Kc)⁻¹) := by
    rw [map_inv₀]
    show 1 < (nm_N Y.Oc p (p : Y.Kc))⁻¹
    rw [nm_N_p hH, inv_inv]
    exact nm_pR hH
  obtain ⟨K', i1, i2, hu, hac, hn⟩ :=
    nm_extG (nm_abs hH) (fun x y => nm_N_add hH x y) ((p : Y.Kc)⁻¹) hc
  refine ⟨K', i1, i2, hu, hac, ?_, ?_, ?_⟩
  · have := hn (p : Y.Kc)
    rw [map_natCast] at this
    exact this.trans (nm_N_p hH)
  · intro x
    rw [hn x]
    exact nm_N_le_one hH x
  · have h2 : 2 ≤ p := hp.out.two_le
    have hpos : 0 < p ^ 2 - 1 := by
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    exact IsAlgClosed.exists_pow_nat_eq (p : K') hpos

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

theorem nm_restNorm (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) : ea_RestNorm Y := by
  obtain ⟨K', nf, ac, um, -, hpn, hball, vp, hvp⟩ := nm_ext Y h
  letI : Algebra (K0 p) K' := ((algebraMap Y.Kc K').comp (algebraMap (K0 p) Y.Kc)).toAlgebra
  haveI : IsScalarTower (K0 p) Y.Kc K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨ea_NormExt.mk K' vp hvp hpn hball⟩

theorem nm_restNorm_of_place (Y : Pend X) (v : X.Pl) : ea_RestNorm Y := nm_restNorm Y (nm_pinv_of_place Y v)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem ea_restSU (hG : RestGc p) : ea_RestSU X Y :=
  ea_restSU_of X Y (ea_restSExpV_of X (restBeta p) (th_restGcV_of X hG))

theorem first_theorem_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : EntryBoundOfHypotheses X Y D :=
  fun hA v j hj =>
    ea_A1U D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brClass X) (ea_brNum X) hA v j hj

theorem second_lemma_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : PlacewiseLowerBoundEvenShift X Y D :=
  fun hA v j hj =>
    ea_A2U D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brClass X) (ea_brNum X) hA v j hj

theorem hecke_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : RestBU X Y D :=
  fun hA v j hj i hi =>
    ea_BU D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brScale X) (ea_brClass X) (ea_brNum X) hA v j hj i hi

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
