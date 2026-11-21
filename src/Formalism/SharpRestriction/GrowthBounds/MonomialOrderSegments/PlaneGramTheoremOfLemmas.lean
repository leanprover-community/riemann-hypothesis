import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.RenamePullLCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ProjKeepsLetter
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SlopeOfBinomCombGen
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.TestBoundOfRhoAndNormSets
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SegDefs
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SumOnLetterApplyInl
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CollapseExponent
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyBlock
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.GlobalTheory

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

theorem mem_Tset (j : Fin D.J) (m : Fin D.r) (z : D.OL) :
    z ∈ D.Tset j m ↔ (∃ b, D.seg b = j ∧ z = Sum.inl b) ∨ (∃ m', m < m' ∧ z = Sum.inr (j, m')) := by
  simp only [Tset, LLj, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨b, hb, rfl⟩ | ⟨m', hm', rfl⟩)
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨m', hm', rfl⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨m', hm', rfl⟩)
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨m', hm', rfl⟩

theorem Tset_mono (j : Fin D.J) {m m' : Fin D.r} (h : m ≤ m') : D.Tset j m' ⊆ D.Tset j m := by
  intro z hz
  rw [mem_Tset] at hz ⊢
  rcases hz with hz | ⟨m'', hm'', rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨m'', lt_of_le_of_lt h hm'', rfl⟩

theorem Tset_disjoint {j j' : Fin D.J} (h : j ≠ j') (m m' : Fin D.r) :
    Disjoint (D.Tset j m) (D.Tset j' m') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_Tset] at hz hz'
  rcases hz with ⟨b, hb, rfl⟩ | ⟨m1, -, rfl⟩
  · rcases hz' with ⟨b', hb', e⟩ | ⟨m2, -, e⟩
    · have : b = b' := Sum.inl.inj e
      subst this
      exact h (hb.symm.trans hb')
    · cases e
  · rcases hz' with ⟨b', -, e⟩ | ⟨m2, -, e⟩
    · cases e
    · have := Sum.inr.inj e
      exact h (congrArg Prod.fst this)

theorem Tset_pair (x y : Fin D.J × Fin D.r) :
    D.Tset x.1 x.2 ⊆ D.Tset y.1 y.2 ∨ D.Tset y.1 y.2 ⊆ D.Tset x.1 x.2 ∨
      Disjoint (D.Tset x.1 x.2) (D.Tset y.1 y.2) := by
  obtain ⟨j, m⟩ := x
  obtain ⟨j', m'⟩ := y
  by_cases h : j = j'
  · subst h
    rcases le_total m m' with h | h
    · exact Or.inr (Or.inl (D.Tset_mono j h))
    · exact Or.inl (D.Tset_mono j h)
  · exact Or.inr (Or.inr (D.Tset_disjoint h m m'))

def linkIdx : Finset (Fin D.J × Fin D.r) := univ.filter fun x => x.2.val + 2 ≤ D.r

theorem card_linkIdx_le : D.linkIdx.card ≤ D.J * (D.r - 1) := by
  classical
  have h1 : D.linkIdx ⊆ (univ : Finset (Fin D.J)) ×ˢ (univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r) := by
    intro x hx
    simp only [linkIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [hx]
  have h2 : (univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r).card ≤ D.r - 1 := by
    have := Finset.card_le_card_of_injOn (s := univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r)
      (t := Finset.range (D.r - 1)) (fun m => m.val)
      (by
        intro m hm
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm
        simp only [Finset.coe_range, Set.mem_Iio]
        omega)
      (by intro a _ b _ hab; exact Fin.ext hab)
    simpa using this
  calc D.linkIdx.card ≤ _ := Finset.card_le_card h1
    _ = D.J * (univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ D.J * (D.r - 1) := Nat.mul_le_mul_left _ h2

theorem eC_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.eC p C0 := by
  unfold eC
  have := lg_ge_one hp hr (2 * D.totDeg)
  positivity

theorem Dm_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dm p C0 := by
  unfold Dm
  have := D.eC_nonneg' hp hr h1
  exact Finset.sum_nonneg fun j _ => by positivity

theorem Dl_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dl p C0 := by
  unfold Dl
  have := D.eC_nonneg' hp hr h1
  have h2 : (0 : ℝ) ≤ (D.r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ D.r := by exact_mod_cast hr
    linarith
  positivity

theorem kapD_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) : 0 ≤ D.kapD p := by
  unfold kapD
  refine le_trans ?_ (kap_ge_card hp hr D.dO)
  positivity

theorem card_linkIdx_mul_le {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) :
    (D.linkIdx.card : ℝ) * ((D.r : ℝ) ^ 2 * lg p D.r (2 * ∑ i, D.dO i)) ≤ D.Dl p C0 := by
  have he : (D.r : ℝ) ^ 2 * lg p D.r (2 * ∑ i, D.dO i) = D.eC p C0 := rfl
  rw [he]
  unfold Dl
  have h2 : (D.linkIdx.card : ℝ) ≤ (D.J : ℝ) * ((D.r : ℝ) - 1) := by
    have := D.card_linkIdx_le
    have h3 : ((D.linkIdx.card : ℕ) : ℝ) ≤ ((D.J * (D.r - 1) : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_one] at h3
    exact h3
  exact mul_le_mul_of_nonneg_right h2 (D.eC_nonneg' hp hr h1)

end TwistData

section StepB

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem stepB_of (h1 : 1 ≤ C0) (hV2 : V2 K) (hP : PROJ K v p C0) : StepB K v p C0 := by
  classical
  intro hD D hV hc F hF hF0
  obtain ⟨hr, hJ, hc1, -, -, hthl, hga, hgaε⟩ := hV
  haveI : NeZero D.r := ⟨by omega⟩
  have hp : 2 ≤ p := two_le_p hD
  have hr1 : 1 ≤ D.r := hr
  obtain ⟨⟨α0, hα0, hge0, hle0⟩, hbF⟩ := exists_of_vBB_zero v F hF0
  obtain ⟨hFP, -, hFl⟩ := hF
  obtain ⟨Pr, p1, p2, p3, p4, -, -⟩ := prodProj (r := D.r) D.osg D.dO hP hD D.linkIdx
    (fun x => D.Tset x.1 x.2) (fun x => ⌈D.thl x.1 x.2⌉) (fun x _ y _ => D.Tset_pair x y)
  have hα0d : ∀ i, ldeg α0 i = D.dO i := (mem_PolK_iff _ _).mp hFP α0 hα0
  have hmon : (monomial α0 (1 : K)) ∈ PolK K D.r D.dO := by
    rw [mem_PolK_iff]
    intro β hβ
    have := support_monomial_subset hβ
    rw [Finset.mem_singleton] at this
    rw [this]; exact hα0d
  have hDm := D.Dm_nonneg' hp hr1 h1
  have hDl := D.Dl_nonneg' hp hr1 h1
  have hkap := D.kapD_nonneg' hp hr1
  have hcc : 4 * (D.Dm p C0 + D.Dl p C0 + 3 * D.kapD p) < D.c := hc

  have hY1 : Pr (monomial α0 1) ∈ PolK K D.r D.dO := p1 _ hmon
  have hY2 : ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r →
      vala D.osg (D.Tset j m) (D.thl j m) (Pr (monomial α0 1)) := fun j m hm =>
    (vala_iff_Aset _ _ _ _).mpr (p2 _ hmon (j, m) (by simp [TwistData.linkIdx, hm]))
  have hY3 : fock F (Pr (monomial α0 1)) = F.coeff α0 * 1 * (fact α0 : K) := by
    rw [p3 F hFP (fun x hx => ?_) _ hmon, fock_monomial_right]
    have hx' : x.2.val + 2 ≤ D.r := by simpa [TwistData.linkIdx] using hx
    exact (vala_iff_Aset _ _ _ _).mp (hFl x.1 x.2 hx')
  have hY4 : bge v (vN v (fact α0) / 2 - D.Dl p C0) (Pr (monomial α0 1)) := by
    have h := p4 _ hmon _ (bge_monomial v α0 (vge_one v))
    refine bge_mono v ?_ h
    have := D.card_linkIdx_mul_le hp hr1 h1
    linarith
  have hY5 : vle v (vN v (fact α0) / 2) (fock F (Pr (monomial α0 1))) := by
    rw [hY3, mul_one]
    have := vle_mul v hle0 (vle_vN hD (fact_ne_zero α0))
    exact vle_mono v (by linarith) this

  obtain ⟨T, lam, hlam, hT⟩ := hgaε (-1) (Or.inr rfl)
  have hC : CostOK (CostV (K := K) (r := D.r) D.osg Set.univ) :=
    costV_ok _ _ (fun S _ θ F G => vala_add) (fun S _ θ a F => vala_smul a)
  have hch : ∀ (x : D.OL × Fin D.r) (k : ℕ),
      CostV D.osg Set.univ k (fun α : D.OL × Fin D.r →₀ ℕ => ((α x).choose k : K)) :=
    fun x k S _ θ F h => vala_dg_choose hV2 x k h
  obtain ⟨g, hg0, hgc, hgC⟩ := approx_of_trunc (v := v) hC hch T lam hlam (fun α => D.ga α ^ (-1 : ℤ)) hT

  have hsplit : D.gaAct (dg g (Pr (monomial α0 1))) =
      Pr (monomial α0 1) + dg (fun α => D.ga α * g α - 1) (Pr (monomial α0 1)) := by
    rw [gaAct_eq_dg]
    ext α
    rw [coeff_add, coeff_dg, coeff_dg, coeff_dg]
    ring
  have herr : ∀ α, vge v (D.c : ℝ) (D.ga α * g α - 1) := by
    intro α
    have hne : D.ga α ≠ 0 := by
      intro h0
      have := hga α
      rw [h0, AddValuation.map_zero] at this
      exact absurd this (by simp)
    have e : D.ga α * g α - 1 = -(D.ga α * (D.ga α ^ (-1 : ℤ) - g α)) := by
      rw [zpow_neg_one]; field_simp; ring
    rw [e]
    have h2 := vge_mul v (vge_unit v (hga α)).1 ((vge_natCast_bound v D.c _).mpr (hgc α))
    rw [zero_add] at h2
    exact vge_neg v h2
  have hpair : vle v (vN v (fact α0) / 2) (fock F (D.gaAct (dg g (Pr (monomial α0 1))))) := by
    rw [hsplit, fock_add_right]
    refine vle_add_of_lt v hY5 (vge_fock v hbF (bge_dg v herr hY4)) ?_
    linarith

  have ha0 : vN v (fact α0) / 2 ≤ D.n0 v := by
    have := fact_upper hD hα0d
    have h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
    rw [h4]; linarith
  have hx0 : 0 ≤ D.n0 v + D.Dl p C0 - vN v (fact α0) / 2 := by linarith
  have hG2P : dg g (Pr (monomial α0 1)) ∈ PolK K D.r D.dO := by
    rw [mem_PolK_iff]
    intro β hβ
    exact (mem_PolK_iff _ _).mp hY1 β (support_dg_subset g _ hβ)
  have hG2b : bge v (0 + (vN v (fact α0) / 2 - D.Dl p C0)) (dg g (Pr (monomial α0 1))) :=
    bge_dg v (fun α => (vge_zero_iff v _).mpr (hg0 α)) hY4
  refine ⟨((p : K) ^ ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊) • dg g (Pr (monomial α0 1)),
    ⟨Submodule.smul_mem _ _ hG2P, ?_⟩, ?_, ?_⟩
  · rw [← cge_zero_iff_Integral]
    have h5 := cge_smul v (vge_p_pow hD ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊)
      (cge_of_bge hD hG2P hG2b)
    refine cge_mono v ?_ h5
    have h6 := Nat.le_ceil (D.n0 v + D.Dl p C0 - vN v (fact α0) / 2)
    have h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
    linarith
  · intro j m hm
    have h7 := hgC (D.Tset j m) (Set.mem_univ _) _ _ (hY2 j m hm)
    have e : D.thl j m - ((6 * D.c : ℕ) : ℝ) = D.thl j m - 6 * D.c := by push_cast; ring
    rw [e] at h7
    exact vala_smul _ h7
  · have e1 : fock F (D.gaAct (((p : K) ^ ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊) •
        dg g (Pr (monomial α0 1)))) =
        (p : K) ^ ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊ *
          fock F (D.gaAct (dg g (Pr (monomial α0 1)))) := by
      simp only [gaAct_eq_dg, map_smul, fock_smul_right]
    rw [e1]
    refine vle_mono v ?_ (vle_pow_p hD _ hpair)
    have h8 := Nat.ceil_lt_add_one hx0
    linarith

end StepB

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

theorem lin_eq_sum {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) (Z : MvPolynomial σ K) :
    T Z = ∑ ζ ∈ Z.support, Z.coeff ζ • T (monomial ζ 1) := by
  conv_lhs => rw [Z.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [show monomial ζ (Z.coeff ζ) = Z.coeff ζ • monomial ζ (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul]

theorem exists_of_mem_support_lin {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K)
    (Z : MvPolynomial σ K) {ζ' : τ →₀ ℕ} (h : ζ' ∈ (T Z).support) :
    ∃ ζ ∈ Z.support, ζ' ∈ (T (monomial ζ 1)).support := by
  rw [lin_eq_sum T Z] at h
  by_contra hc
  push_neg at hc
  rw [mem_support_iff, coeff_sum] at h
  apply h
  refine Finset.sum_eq_zero fun ζ hζ => ?_
  have hz := hc ζ hζ
  rw [mem_support_iff, not_not] at hz
  rw [coeff_smul, hz, smul_zero]

namespace TwistData

variable (D : TwistData K)

theorem ph_lin_sum (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.ph p Z = ∑ ζ ∈ Z.support, Z.coeff ζ • D.ph p (monomial ζ 1) :=
  lin_eq_sum (D.ph p).toLinearMap Z

def iotaL : D.OL → D.ML := Sum.elim D.mb D.mlab

theorem iotaL_injective : Function.Injective D.iotaL := by
  rintro (a | a) (b | b) h <;> simp_all [iotaL, mb, mlab]

theorem localizationToLaurent_injective : Function.Injective (Prod.map D.iotaL (id : Fin D.r → Fin D.r)) :=
  D.iotaL_injective.prodMap Function.injective_id

theorem msg_comp_iotaL : D.msg ∘ D.iotaL = D.osg := by
  funext x
  rcases x with b | t <;> rfl

theorem preimage_TLset (j : Fin D.J) (m : Fin D.r) :
    (D.TLset j m).preimage D.iotaL D.iotaL_injective.injOn = D.Tset j m := by
  ext x
  rw [Finset.mem_preimage]
  rcases x with b | t
  · simp [iotaL, TLset, Tset, mb, mlab]
  · simp [iotaL, TLset, Tset, mb, mlab]

theorem ph_rename_iotaL (p : ℕ) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.ph p (rename (Prod.map D.iotaL id) G) = G := by
  have hc : (D.ph p).comp (rename (Prod.map D.iotaL id)) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨b | t, a⟩ <;> simp [ph, iotaL, mb, mlab]
  simpa using DFunLike.congr_fun hc G

theorem mapDomain_mb (α : D.EA) (b : D.Lb) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mb b, a) = α (Sum.inl b, a) :=
  Finsupp.mapDomain_apply D.localizationToLaurent_injective α (Sum.inl b, a)

theorem mapDomain_mlab (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mlab t, a) = α (Sum.inr t, a) :=
  Finsupp.mapDomain_apply D.localizationToLaurent_injective α (Sum.inr t, a)

theorem mapDomain_mw (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mw t, a) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨⟨i, a'⟩, h⟩
  rcases i with b | t' <;> simp [iotaL, mb, mlab, mw] at h

theorem mapDomain_mtp (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mtp t, a) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨⟨i, a'⟩, h⟩
  rcases i with b | t' <;> simp [iotaL, mb, mlab, mtp] at h

theorem notSegL_mb {j : Fin D.J} {b : D.Lb} (h : D.seg b ≠ j) : ¬ D.SegL j (D.mb b) := by
  rintro (⟨b', h1, e⟩ | ⟨m, e⟩ | ⟨m, e⟩)
  · simp only [mb, Sum.inl.injEq] at e
    exact h (e ▸ h1)
  · simp [mb, mlab] at e
  · simp [mb, mtp] at e

theorem notSegL_mlab {j j' : Fin D.J} (m : Fin D.r) (h : j' ≠ j) : ¬ D.SegL j (D.mlab (j', m)) := by
  rintro (⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)
  · simp [mb, mlab] at e
  · simp only [mlab, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at e
    exact h e.1
  · simp [mlab, mtp] at e

theorem notSegL_mtp {j j' : Fin D.J} (m : Fin D.r) (h : j' ≠ j) : ¬ D.SegL j (D.mtp (j', m)) := by
  rintro (⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)
  · simp [mb, mtp] at e
  · simp [mlab, mtp] at e
  · simp only [mtp, Sum.inr.injEq, Prod.mk.injEq] at e
    exact h e.1

theorem notSegL_mw (j : Fin D.J) (t : D.Tau) : ¬ D.SegL j (D.mw t) := by
  rintro (⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)
  · simp [mb, mw] at e
  · simp [mlab, mw] at e
  · simp [mtp, mw] at e

theorem notSegL_of_mem_TLset {j j' : Fin D.J} (h : j' ≠ j) (m : Fin D.r) {i : D.ML}
    (hi : i ∈ D.TLset j' m) : ¬ D.SegL j i := by
  simp only [TLset, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with ⟨b, hb, rfl⟩ | ⟨m', _, rfl⟩
  · simp [LLj] at hb
    exact D.notSegL_mb (by rw [hb]; exact h)
  · exact D.notSegL_mlab m' h

theorem notSegL_of_mem_YPset {j j' : Fin D.J} (h : j' ≠ j) (m : Fin D.r) {i : D.ML}
    (hi : i ∈ D.YPset j' m) : ¬ D.SegL j i := by
  simp only [YPset, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with ⟨b, hb, rfl⟩ | ⟨m', _, rfl⟩
  · simp [LLj] at hb
    exact D.notSegL_mb (by rw [hb]; exact h)
  · exact D.notSegL_mtp m' h

theorem ldeg_congr' {ζ ζ' : D.EM} {i : D.ML} (h : ∀ a, ζ' (i, a) = ζ (i, a)) : ldeg ζ' i = ldeg ζ i := by
  unfold ldeg; exact Finset.sum_congr rfl fun a _ => h a

theorem PreE.of_agree {j j' : Fin D.J} (h : j' ≠ j) {ζ ζ' : D.EM} (hζ : D.PreE j' ζ)
    (hag : ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a)) : D.PreE j' ζ' := by
  obtain ⟨h1, h2, h3⟩ := hζ
  refine ⟨fun b hb => ?_, fun m => ?_, fun m a => ?_⟩
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mb (by rw [hb]; exact h)))]
    exact h1 b hb
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mlab m h))]
    exact h2 m
  · rw [hag _ (D.notSegL_mtp m h)]
    exact h3 m a

theorem PostE.of_agree {j j' : Fin D.J} (h : j' ≠ j) {ζ ζ' : D.EM} (hζ : D.PostE j' ζ)
    (hag : ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a)) : D.PostE j' ζ' := by
  obtain ⟨h1, h2, h3, h4⟩ := hζ
  refine ⟨fun b hb => ?_, fun m => ?_, fun m => ?_, fun m hm a => ?_⟩
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mb (by rw [hb]; exact h)))]
    exact h1 b hb
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mlab m h)), D.ldeg_congr' (hag _ (D.notSegL_mtp m h))]
    exact h2 m
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mtp m h))]
    exact h3 m
  · rw [hag _ (D.notSegL_mtp m h)]
    exact h4 m hm a

def Inv (v : AddValuation K (WithTop ℚ)) (p : ℕ) (θ : Fin D.J → Fin D.r → ℝ)
    (Gt : MvPolynomial (D.OL × Fin D.r) K) (s : Finset (Fin D.J))
    (Z : MvPolynomial (D.ML × Fin D.r) K) : Prop :=
  Integral v Z ∧ D.ph p Z = Gt ∧
  (∀ ζ ∈ Z.support, (∀ t a, ζ (D.mw t, a) = 0) ∧ (∀ j ∈ s, D.PostE j ζ) ∧ (∀ j, j ∉ s → D.PreE j ζ)) ∧
  (∀ j ∈ s, ∀ m : Fin D.r, m.val + 2 ≤ D.r → vala D.msg (D.YPset j m) (θ j m) Z) ∧
  (∀ j, j ∉ s → ∀ m : Fin D.r, m.val + 2 ≤ D.r → vala D.msg (D.TLset j m) (θ j m) Z)

theorem inv_start (v : AddValuation K (WithTop ℚ)) (p : ℕ) (θ : Fin D.J → Fin D.r → ℝ)
    (Gt : MvPolynomial (D.OL × Fin D.r) K) (hGt : Gt ∈ PolO v D.r D.dO)
    (hval : ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → vala D.osg (D.Tset j m) (θ j m) Gt) :
    D.Inv v p θ Gt ∅ (rename (Prod.map D.iotaL id) Gt) := by
  refine ⟨?_, D.ph_rename_iotaL p Gt, ?_, fun j hj => by simp at hj, ?_⟩
  · intro α
    by_cases hα : ∃ u, Finsupp.mapDomain (Prod.map D.iotaL id) u = α
    · obtain ⟨u, rfl⟩ := hα
      rw [coeff_rename_mapDomain _ D.localizationToLaurent_injective]
      exact hGt.2 u
    · rw [coeff_rename_eq_zero _ _ _ (fun u hu => absurd ⟨u, hu⟩ hα), AddValuation.map_zero]
      exact le_top
  · intro ζ hζ
    have hex : ∃ u ∈ Gt.support, Finsupp.mapDomain (Prod.map D.iotaL id) u = ζ := by
      by_contra hc
      push_neg at hc
      rw [mem_support_iff] at hζ
      apply hζ
      apply coeff_rename_eq_zero
      intro u hu
      by_contra hne
      exact hc u (mem_support_iff.mpr hne) hu
    obtain ⟨u, hu, rfl⟩ := hex
    have hdeg := (mem_PolK_iff _ _).mp hGt.1 u hu
    refine ⟨fun t a => D.mapDomain_mw u t a, fun j hj => by simp at hj,
      fun j _ => ⟨fun b _ => ?_, fun m => ?_, fun m a => D.mapDomain_mtp u _ a⟩⟩
    · have h1 := hdeg (Sum.inl b)
      unfold ldeg at h1 ⊢
      simp only [mapDomain_mb]
      exact h1
    · have h1 := hdeg (Sum.inr (j, m))
      unfold ldeg at h1 ⊢
      simp only [mapDomain_mlab]
      exact h1
  · intro j _ m hm
    rw [vala_rename_iff D.iotaL D.iotaL_injective, msg_comp_iotaL, preimage_TLset]
    exact hval j m hm

theorem inv_step [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} (hSeg : SegStep K v p) (hD : DVRHyp v p)
    (hr : 0 < D.r) (hJ : 0 < D.J) (θ : Fin D.J → Fin D.r → ℝ) (Gt : MvPolynomial (D.OL × Fin D.r) K)
    (s : Finset (Fin D.J)) (j : Fin D.J) (hj : j ∉ s) (Z : MvPolynomial (D.ML × Fin D.r) K)
    (hZ : D.Inv v p θ Gt s Z) : ∃ Z', D.Inv v p θ Gt (insert j s) Z' := by
  obtain ⟨hInt, hph, hsupp, hYP, hTL⟩ := hZ
  obtain ⟨Th, tI, tph, tsupp, tval, tS⟩ := hSeg hD D hr hJ j
  have hpre : ∀ ζ ∈ Z.support, D.PreE j ζ := fun ζ hζ => (hsupp ζ hζ).2.2 j hj
  have hne : ∀ j', j' ∈ s → j' ≠ j := fun j' hj' he => hj (he ▸ hj')
  refine ⟨Th Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro α
    rw [lin_eq_sum Th Z, coeff_sum]
    apply AddValuation.map_le_sum
    intro ζ hζ
    rw [coeff_smul, smul_eq_mul, AddValuation.map_mul]
    exact add_nonneg (hInt ζ) (tI ζ (hpre ζ hζ) α)
  · rw [lin_eq_sum Th Z, map_sum, ← hph, D.ph_lin_sum p Z]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    rw [map_smul, tph ζ (hpre ζ hζ)]
  · intro ζ' hζ'
    obtain ⟨ζ, hζ, hζ'1⟩ := exists_of_mem_support_lin Th Z hζ'
    obtain ⟨hpost, hag⟩ := tsupp ζ (hpre ζ hζ) ζ' hζ'1
    obtain ⟨hw, hs, hns⟩ := hsupp ζ hζ
    refine ⟨fun t a => ?_, fun j' hj' => ?_, fun j' hj' => ?_⟩
    · rw [hag _ (D.notSegL_mw j t) a]
      exact hw t a
    · rcases Finset.mem_insert.mp hj' with h | hj's
      · rw [h]
        exact hpost
      · exact PostE.of_agree D (hne j' hj's) (hs j' hj's) hag
    · have hj's : j' ∉ s := fun h => hj' (Finset.mem_insert_of_mem h)
      have hne' : j' ≠ j := fun he => hj' (he ▸ Finset.mem_insert_self j s)
      exact PreE.of_agree D hne' (hns j' hj's) hag
  · intro j' hj' m hm
    rcases Finset.mem_insert.mp hj' with h | hj's
    · subst h
      exact tval Z hInt hpre m _ hm (hTL _ hj m hm)
    · exact vala_of_le (tS _ (fun i hi => D.notSegL_of_mem_YPset (hne j' hj's) m hi) Z) (hYP j' hj's m hm)
  · intro j' hj' m hm
    have hj's : j' ∉ s := fun h => hj' (Finset.mem_insert_of_mem h)
    have hne' : j' ≠ j := fun he => hj' (he ▸ Finset.mem_insert_self j s)
    exact vala_of_le (tS _ (fun i hi => D.notSegL_of_mem_TLset hne' m hi) Z) (hTL j' hj's m hm)

theorem inv_all [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} (hSeg : SegStep K v p) (hD : DVRHyp v p)
    (hr : 0 < D.r) (hJ : 0 < D.J) (θ : Fin D.J → Fin D.r → ℝ) (Gt : MvPolynomial (D.OL × Fin D.r) K)
    (hGt : Gt ∈ PolO v D.r D.dO)
    (hval : ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → vala D.osg (D.Tset j m) (θ j m) Gt)
    (s : Finset (Fin D.J)) : ∃ Z, D.Inv v p θ Gt s Z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨_, D.inv_start v p θ Gt hGt hval⟩
  | insert j s hj ih =>
    obtain ⟨Z, hZ⟩ := ih
    exact D.inv_step hSeg hD hr hJ θ Gt s j hj Z hZ

def splitE (p : ℕ) (ζ : D.EM) : D.EM :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun b => ζ (D.mb b, x.2))
    (Sum.elim (fun t => ζ (D.mlab t, x.2) % D.P p t)
      (Sum.elim (fun t => ζ (D.mw t, x.2) + ζ (D.mlab t, x.2) / D.P p t)
        (fun t => ζ (D.mtp t, x.2)))) x.1

theorem splitE_mb (p : ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.splitE p ζ (D.mb b, a) = ζ (D.mb b, a) := by simp [splitE, mb]

theorem splitE_mlab (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.splitE p ζ (D.mlab t, a) = ζ (D.mlab t, a) % D.P p t := by simp [splitE, mlab]

theorem splitE_mw (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.splitE p ζ (D.mw t, a) = ζ (D.mw t, a) + ζ (D.mlab t, a) / D.P p t := by
  simp [splitE, mw]

theorem splitE_mtp (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.splitE p ζ (D.mtp t, a) = ζ (D.mtp t, a) := by simp [splitE, mtp]

theorem phE_splitE (p : ℕ) (ζ : D.EM) : D.phE p (D.splitE p ζ) = D.phE p ζ := by
  ext ⟨i, a⟩
  rcases i with b | t
  · rw [phE_apply_inl, phE_apply_inl, splitE_mb]
  · rw [phE_apply_inr, phE_apply_inr, splitE_mlab, splitE_mw, splitE_mtp, mul_add]
    have := Nat.mod_add_div (ζ (D.mlab t, a)) (D.P p t)
    linarith

def Sp (p : ℕ) : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun ζ => monomial (D.splitE p ζ) 1

theorem Sp_monomial (p : ℕ) (ζ : D.EM) : D.Sp p (monomial ζ (1 : K)) = monomial (D.splitE p ζ) 1 := by
  rw [Sp, lsup_monomial, one_smul]

theorem ph_Sp (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) : D.ph p (D.Sp p Z) = D.ph p Z := by
  rw [Sp, lsup_apply, map_sum, ph_eq_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [map_smul, ph_monomial, phE_splitE, smul_monomial, smul_eq_mul, mul_one]

theorem integral_Sp (v : AddValuation K (WithTop ℚ)) (p : ℕ) {Z : MvPolynomial (D.ML × Fin D.r) K}
    (hZ : Integral v Z) : Integral v (D.Sp p Z) := by
  classical
  intro α
  rw [Sp, lsup_apply, coeff_sum]
  apply AddValuation.map_le_sum
  intro ζ _
  rw [coeff_smul, coeff_monomial]
  split_ifs
  · rw [smul_eq_mul, mul_one]
    exact hZ ζ
  · rw [smul_zero, AddValuation.map_zero]
    exact le_top

theorem goodE_splitE {p : ℕ} (hp : 0 < p) {ζ : D.EM} (hw : ∀ t a, ζ (D.mw t, a) = 0)
    (hpost : ∀ j, D.PostE j ζ) : D.GoodE p (D.splitE p ζ) := by
  have hP : ∀ t, 0 < D.P p t := fun t => by
    unfold P
    exact pow_pos hp _
  refine ⟨fun t a => ?_, fun j m hm a => ?_, fun b => ?_, fun t => ?_, fun t => ?_⟩
  · rw [splitE_mlab]
    exact Nat.mod_lt _ (hP t)
  · rw [splitE_mtp]
    exact (hpost j).2.2.2 m hm a
  · rw [D.ldeg_congr' (fun a => D.splitE_mb p ζ b a)]
    exact (hpost (D.seg b)).1 b rfl
  · obtain ⟨j, m⟩ := t
    have e1 : ldeg (D.splitE p ζ) (D.mlab (j, m)) + D.P p (j, m) * ldeg (D.splitE p ζ) (D.mw (j, m))
        = ldeg ζ (D.mlab (j, m)) := by
      unfold ldeg
      simp only [splitE_mlab, splitE_mw, hw, zero_add]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => Nat.mod_add_div _ _
    rw [e1, D.ldeg_congr' (fun a => D.splitE_mtp p ζ (j, m) a)]
    exact (hpost j).2.1 m
  · obtain ⟨j, m⟩ := t
    rw [D.ldeg_congr' (fun a => D.splitE_mtp p ζ (j, m) a)]
    exact (hpost j).2.2.1 m

def labB : D.ML → Bool := Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun _ => false))

theorem splitE_eq (p : ℕ) (α : D.EM) :
    D.splitE p α = eIn (fun i => D.labB i = true) α + D.splitE p (eOut (fun i => D.labB i = true) α) := by
  ext ⟨i, a⟩
  rw [Finsupp.add_apply]
  rcases i with b | t | t | t
  · show D.splitE p α (D.mb b, a) = eIn _ α (D.mb b, a) + D.splitE p (eOut _ α) (D.mb b, a)
    rw [splitE_mb, splitE_mb, eIn_apply, eOut_apply]
    simp [labB, mb]
  · show D.splitE p α (D.mlab t, a) = eIn _ α (D.mlab t, a) + D.splitE p (eOut _ α) (D.mlab t, a)
    rw [splitE_mlab, splitE_mlab, eIn_apply, eOut_apply]
    simp [labB, mlab]
  · show D.splitE p α (D.mw t, a) = eIn _ α (D.mw t, a) + D.splitE p (eOut _ α) (D.mw t, a)
    rw [splitE_mw, splitE_mw, eIn_apply, eOut_apply, eOut_apply]
    simp [labB, mw, mlab]
  · show D.splitE p α (D.mtp t, a) = eIn _ α (D.mtp t, a) + D.splitE p (eOut _ α) (D.mtp t, a)
    rw [splitE_mtp, splitE_mtp, eIn_apply, eOut_apply]
    simp [labB, mtp]

theorem not_labB_of_mem_Yset {j : Fin D.J} {m : Fin D.r} {i : D.ML} (hi : i ∈ D.Yset j m) :
    ¬ D.labB i = true := by
  simp only [Yset, wSet, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with (⟨m', _, rfl⟩ | ⟨b, _, rfl⟩) | ⟨m', _, rfl⟩ <;> simp [labB, mw, mb, mtp]

theorem vala_Sp (p : ℕ) (j : Fin D.J) (m : Fin D.r) {θ : ℝ} {Z : MvPolynomial (D.ML × Fin D.r) K}
    (hZ : vala D.msg (D.Yset j m) θ Z) : vala D.msg (D.Yset j m) θ (D.Sp p Z) := by
  have key : D.Sp p Z = ∑ μ ∈ Z.support.image (eOut (fun i => D.labB i = true)),
      coefOut (fun i => D.labB i = true) μ Z * monomial (D.splitE p μ) 1 := by
    simp only [coefOut, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm, Sp, lsup_apply]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ hα), monomial_mul, mul_one,
      ← splitE_eq, smul_monomial, smul_eq_mul, mul_one]
  have hle : valS D.msg (D.Yset j m) Z ≤ valS D.msg (D.Yset j m) (D.Sp p Z) := by
    rw [key]
    refine Finset.sum_induction _ (fun F => valS D.msg (D.Yset j m) Z ≤ valS D.msg (D.Yset j m) F)
      (fun F G hF hG => le_trans (le_min hF hG) (valS_add_le _ _ _ _)) ?_ ?_
    · simp [valS]
    · intro μ hμ
      have h1 := valS_coefOut_le (K := K) (r := D.r) (fun i => D.labB i = true) D.msg (D.Yset j m)
        (fun i hi => D.not_labB_of_mem_Yset hi) μ Z
      have h2 : 0 ≤ valS D.msg (D.Yset j m) (monomial (D.splitE p μ) (1 : K)) := by
        apply valS_monomial_nonneg_of_vec
        intro i a h
        rcases i with b | t
        · exfalso
          apply h
          obtain ⟨α, _, rfl⟩ := Finset.mem_image.mp hμ
          show D.splitE p (eOut _ α) (D.mb b, a) = 0
          rw [splitE_mb, eOut_apply]
          simp [labB, mb]
        · rfl
      calc valS D.msg (D.Yset j m) Z = valS D.msg (D.Yset j m) Z + 0 := (add_zero _).symm
        _ ≤ _ := add_le_add h1 h2
        _ ≤ _ := valS_mul_le _ _ _ _
  exact le_trans hZ (toR_mono hle)

theorem YPset_subset_Yset (j : Fin D.J) (m : Fin D.r) : D.YPset j m ⊆ D.Yset j m := by
  intro i hi
  simp only [YPset, Yset, Finset.mem_union] at hi ⊢
  tauto

theorem msg_of_mem_Yset {j : Fin D.J} {m : Fin D.r} {i : D.ML} (hi : i ∈ D.Yset j m)
    (hn : i ∉ D.YPset j m) : D.msg i = true := by
  simp only [Yset, YPset, Finset.mem_union] at hi hn
  rcases hi with (hw | hb) | ht
  · simp only [wSet, Finset.mem_image] at hw
    obtain ⟨m', _, rfl⟩ := hw
    rfl
  · exact absurd (Or.inl hb) hn
  · exact absurd (Or.inr ht) hn

end TwistData

theorem stepC_of [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} (hV2 : V2 K)
    (hSeg : SegStep K v p) : StepC K v p := by
  intro hD D hr hJ θ Gt hGt hval
  haveI : NeZero D.r := ⟨by omega⟩
  obtain ⟨Z, hi, hph, hsup, hY, -⟩ := D.inv_all hSeg hD hr hJ θ Gt hGt hval Finset.univ
  have hp : 0 < p := hD.prime.pos
  refine ⟨D.Sp p Z, D.integral_Sp v p hi, ?_, by rw [D.ph_Sp, hph], ?_⟩
  · intro ζ' hζ'
    obtain ⟨ζ, hζ, h2⟩ := exists_of_mem_support_lin (D.Sp p) Z hζ'
    rw [D.Sp_monomial] at h2
    have h3 := support_monomial_subset h2
    rw [Finset.mem_singleton] at h3
    rw [h3]
    exact D.goodE_splitE hp (hsup ζ hζ).1 fun j => (hsup ζ hζ).2.1 j (Finset.mem_univ j)
  · intro j m hm
    refine D.vala_Sp p j m ?_
    exact vala_superset_vec hV2 (D.YPset_subset_Yset j m) (fun i hi hn => D.msg_of_mem_Yset hi hn)
      (hY j (Finset.mem_univ j) m hm)

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

def embU (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (x : D.OL × Fin D.r) (ζ : D.EM) : ℕ :=
  Sum.elim (fun b => ζ (D.mb b, x.2)) (fun t => ρ t x.2 + D.P p t * ζ (D.mw t, x.2)) x.1

def embE (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => D.embU p ρ x ζ

theorem substituted_exponent_eq_embedded (p : ℕ) (ζ : D.EM) : D.collapseExponent p ζ = D.embE p (D.labF ζ) ζ := rfl

def gaR (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ρ : D.Tau → Fin D.r → ℕ) (ε : ℤ)
    (ζ : D.EM) : K :=
  D.ga (D.embE p ρ ζ) ^ ε * ∏ t, gam t (ρ t) (D.wF ζ t) ^ ε

theorem gaR_one (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) :
    D.gaR p gam (D.labF ζ) 1 ζ = D.gaP p gam ζ := by
  simp only [gaR, gaP, zpow_one, substituted_exponent_eq_embedded]

theorem gaR_neg_one (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) :
    D.gaR p gam (D.labF ζ) (-1) ζ = (D.gaP p gam ζ)⁻¹ := by
  simp only [gaR, gaP, zpow_neg_one, substituted_exponent_eq_embedded, Finset.prod_inv_distrib, mul_inv]

end TwistData

section

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

abbrev CostM (D : TwistData K) : ℕ → (D.EM → K) → Prop := CostV (K := K) (r := D.r) D.msg Set.univ

theorem costM_ok (D : TwistData K) : CostOK (CostM D) :=
  costV_ok _ _ (fun _ _ _ _ _ h1 h2 => vala_add h1 h2) (fun _ _ _ a _ h => vala_smul a h)

theorem costM_choose (hV2 : V2 K) (D : TwistData K) (hr : 0 < D.r) (x : D.ML × Fin D.r) (k : ℕ) :
    CostM D k (fun α => ((α x).choose k : K)) := by
  haveI : NeZero D.r := ⟨hr.ne'⟩
  intro S _ θ F h
  exact vala_dg_choose hV2 x k h

theorem exists_approx_gaR (hV2 : V2 K) (D : TwistData K) (hV : D.Valid v p)
    (cst : D.Tau → (Fin D.r → ℕ) → ℕ → K) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K)
    (hDig : D.DigOK v p cst gam) (ρ : D.Tau → Fin D.r → ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ g : D.EM → K, (∀ ζ, 0 ≤ v (g ζ)) ∧ CostM D (12 * D.c) g ∧
      ((∀ t a, ρ t a < D.P p t) → ∀ ζ, ((D.c : ℕ) : WithTop ℚ) ≤ v (D.gaR p gam ρ ε ζ - g ζ)) := by
  have hC := costM_ok D
  have hch := costM_choose hV2 D hV.1
  by_cases hρ : ∀ t a, ρ t a < D.P p t
  · obtain ⟨hga0, hga⟩ := hV.2.2.2.2.2.2
    obtain ⟨T, lam, hlam, hcong⟩ := hga ε hε
    obtain ⟨g1, a1, a2, a3⟩ := approx_of_trunc_gen (v := v) hC (D.embU p ρ) (by
        rintro ⟨i, a⟩ k
        rcases i with b | t
        · exact hch (D.mb b, a) k
        · exact cost_choose_affine hC (fun ζ => ζ (D.mw t, a)) (hch (D.mw t, a)) (ρ t a) (D.P p t) k)
      T lam hlam (fun ζ => D.ga (D.embE p ρ ζ) ^ ε) (fun ζ => hcong (D.embE p ρ ζ))
    obtain ⟨T', lam', hlam', hcong'⟩ := hDig.2 ρ hρ ε hε
    obtain ⟨g2, b1, b2, b3⟩ := approx_of_trunc_gen (v := v) hC
      (fun (x : D.Tau × Fin D.r) (ζ : D.EM) => ζ (D.mw x.1, x.2)) (fun x k => hch (D.mw x.1, x.2) k)
      T' lam' hlam' (fun ζ => (∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε)
      (fun ζ => hcong' (fun x => ζ (D.mw x.1, x.2)))
    have u2 : ∀ ζ : D.EM, v ((∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε) = 0 := fun ζ =>
      v_unit_zpow v (Finset.prod_induction _ (fun x => v x = 0) (fun a b ha hb => v_unit_mul v ha hb)
        v.map_one fun t _ => ((hDig.1 t (ρ t) (hρ t)).2 _).1) ε
    refine ⟨fun ζ => g1 ζ * g2 ζ, fun ζ => v_mul_nonneg (a1 ζ) (b1 ζ), ?_, fun _ ζ => ?_⟩
    · have := hC.mul _ _ _ _ a3 b3
      have e : 6 * D.c + 6 * D.c = 12 * D.c := by ring
      rwa [e] at this
    · have e : D.gaR p gam ρ ε ζ - g1 ζ * g2 ζ =
          (D.ga (D.embE p ρ ζ) ^ ε - g1 ζ) * (∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε +
            g1 ζ * ((∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε - g2 ζ) := by
        have e2 : ∏ t, gam t (ρ t) (D.wF ζ t) ^ ε = (∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε :=
          Finset.prod_zpow _ _ _
        simp only [TwistData.gaR]
        rw [e2]; ring
      rw [e]
      exact v_add_ge (v_mul_ge_left (a2 ζ) (u2 ζ).ge) (v_mul_ge_right (a1 ζ) (b2 ζ))
  · refine ⟨fun _ => 1, fun _ => by simp, ?_, fun h => absurd h hρ⟩
    exact hC.mono 0 _ _ (Nat.zero_le _) hC.one

theorem eOut_of_mem_image {L : Type} [DecidableEq L] {r : ℕ} (out : L → Prop) [DecidablePred out]
    (F : MvPolynomial (L × Fin r) K) {μ : L × Fin r →₀ ℕ} (hμ : μ ∈ F.support.image (eOut out)) :
    eOut out μ = μ := by
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hμ
  exact eOut_eOut out α

theorem vala_dg_labels (D : TwistData K) (gg : (D.Tau → Fin D.r → ℕ) → D.EM → K) (n : ℕ)
    (hgg : ∀ ρ, CostM D n (gg ρ)) (S : Finset D.ML) (hS : ∀ t, D.mlab t ∉ S) (θ : ℝ)
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZ : vala D.msg S θ Z) :
    vala D.msg S (θ - n) (dg (fun ζ => gg (D.labF ζ) ζ) Z) := by
  set out : D.ML → Prop := fun i => ∃ t, i = D.mlab t with hout
  letI : DecidablePred out := Classical.decPred _
  have hoS : ∀ i ∈ S, ¬ out i := by
    rintro i hi ⟨t, rfl⟩; exact hS t hi
  conv => rw [sum_coefOut out Z, map_sum]
  refine vala_sum _ _ fun μ hμ => ?_
  have e : dg (fun ζ => gg (D.labF ζ) ζ) (monomial μ 1 * coefOut out μ Z) =
      dg (gg (D.labF μ)) (monomial μ 1 * coefOut out μ Z) := by
    refine dg_congr fun α hα => ?_
    have hlab : D.labF α = D.labF μ := by
      rw [mem_support_iff, coeff_monomial_mul'] at hα
      by_cases hle : μ ≤ α
      · rw [if_pos hle, one_mul] at hα
        have h0 := eOut_eq_zero_of_mem_support_coefOut out (mem_support_iff.mpr hα)
        funext t a
        have h1 : (α - μ) (D.mlab t, a) = 0 := by
          have := DFunLike.congr_fun h0 (D.mlab t, a)
          rw [eOut_apply, if_pos ⟨t, rfl⟩] at this
          simpa using this
        have h2 : μ (D.mlab t, a) ≤ α (D.mlab t, a) := hle _
        rw [Finsupp.tsub_apply] at h1
        simp only [TwistData.labF]
        omega
      · rw [if_neg hle] at hα; exact absurd rfl hα
    rw [hlab]
  rw [e]
  refine hgg _ S (Set.mem_univ _) θ _ ?_
  refine vala_mul_left_nonneg (valS_monomial_nonneg_of_free _ _ ?_) (vala_coefOut out hoS _ hZ)
  intro i hi a
  rw [← eOut_of_mem_image out Z hμ, eOut_apply, if_neg (hoS i hi)]

theorem stepG_of (hV2 : V2 K) : StepG K v p := by
  intro _hD D hV cst gam hDig
  have Hp := fun ρ => exists_approx_gaR hV2 D hV cst gam hDig ρ 1 (Or.inl rfl)
  have Hm := fun ρ => exists_approx_gaR hV2 D hV cst gam hDig ρ (-1) (Or.inr rfl)
  choose gp hp1 hp2 hp3 using Hp
  choose gm hm1 hm2 hm3 using Hm
  refine ⟨fun ζ => gp (D.labF ζ) ζ, fun ζ => gm (D.labF ζ) ζ, fun ζ => hp1 _ ζ, fun ζ => hm1 _ ζ, ?_, ?_⟩
  · intro ζ hζ
    constructor
    · have := hp3 (D.labF ζ) hζ ζ
      rw [D.gaR_one, AddValuation.map_sub_swap] at this
      exact this
    · have := hm3 (D.labF ζ) hζ ζ
      rw [D.gaR_neg_one, AddValuation.map_sub_swap] at this
      exact this
  · intro S hS θ Z hZ
    have e : θ - 12 * (D.c : ℝ) = θ - ((12 * D.c : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    exact ⟨vala_dg_labels D gp _ hp2 S hS θ Z hZ, vala_dg_labels D gm _ hm2 S hS θ Z hZ⟩

end

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section

variable {K : Type} [Field K]

theorem linMap_eq_sum {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) (Y : MvPolynomial σ K) :
    T Y = ∑ ζ ∈ Y.support, Y.coeff ζ • T (monomial ζ 1) := by
  conv_lhs => rw [Y.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]

end

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

theorem Good.dg {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (f : D.EM → K) :
    D.Good p (Formalism.MainNotions.PlaneGram.dg f Z) := fun ζ hζ => hZ ζ (support_dg_subset f Z hζ)

theorem mlab_notMem_Yset (j : Fin D.J) (m : Fin D.r) (t : D.Tau) : D.mlab t ∉ D.Yset j m := by
  rw [mem_Yset]
  rintro (⟨m', h⟩ | ⟨b, -, h⟩ | ⟨m', -, h⟩) <;> simp [mb, mw, mlab, mtp] at h

end TwistData

section Main

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem cge_Pj_monomial (hD : DVRHyp v p) (D : TwistData K) (hr : 1 ≤ D.r)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (ζ : D.EM) (hζ : D.GoodE p ζ) :
    cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (monomial ζ 1)) := by
  intro ζ'
  by_cases h : ζ' ∈ (Pj (monomial ζ 1)).support
  · have hb : D.SameBlockAlt ζ ζ' := hP1 ζ ζ' h
    have h1 := D.blk_fact hD hr hζ hb
    exact vge_mono v (by linarith) (hP2 ζ hζ ζ')
  · rw [notMem_support_iff.mp h]; exact vge_zero v _

theorem good_Pj (D : TwistData K)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    {Y : MvPolynomial (D.ML × Fin D.r) K} (hY : D.Good p Y) : D.Good p (Pj Y) := by
  rw [linMap_eq_sum Pj Y]
  refine TwistData.Good.sum D _ _ fun ζ hζ => TwistData.Good.smul D ?_ _
  intro ζ' hζ'
  exact TwistData.GoodE.good_exponent_same_block D (hY ζ hζ) (hP1 ζ ζ' hζ')

theorem omega_clauses (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hPj : (∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a))) ∧
      (∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1))) ∧
      (∀ Z (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) (Pj Z)) ∧
      (∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1)) ∧
      (∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ) Z, vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) θ (Pj Z)))
    (gp gm : D.EM → K) (hgp : ∀ ζ, 0 ≤ v (gp ζ)) (hgm : ∀ ζ, 0 ≤ v (gm ζ))
    (hcost : ∀ S : Finset D.ML, (∀ t, D.mlab t ∉ S) → ∀ (θ : ℝ) (Z : MvPolynomial (D.ML × Fin D.r) K),
        vala D.msg S θ Z → vala D.msg S (θ - 12 * D.c) (dg gp Z) ∧ vala D.msg S (θ - 12 * D.c) (dg gm Z)) :
    ((⌈D.Dm p C0 + D.kapD p / 2⌉₊ : ℕ) : ℝ) ≤ D.Dm p C0 + D.kapD p / 2 + 1 ∧
    (∀ Z, Integral v Z → D.Good p Z →
      Integral v (((p : K) ^ ⌈D.Dm p C0 + D.kapD p / 2⌉₊) • dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → D.Good p (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (i : Fin (D.nch j)),
      vala D.msg (D.chainSet j i) (D.th j i - D.sl j i - 12 * D.c) (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
      vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) (θ - 24 * D.c) (dg gm (Pj (dg gp Z)))) := by
  obtain ⟨hP1, hP2, hP3, -, hP5⟩ := hPj
  have hp : 2 ≤ p := two_le_p hD
  have hr : 1 ≤ D.r := hV.1
  have hJ : 1 ≤ D.J := hV.2.1
  have hkap := D.kapD_ge_one hp hr hJ
  have hDm := D.Dm_nonneg hp hr h1
  have hpos : 0 ≤ D.Dm p C0 + D.kapD p / 2 := by linarith
  refine ⟨(Nat.ceil_lt_add_one hpos).le, ?_, ?_, ?_, ?_⟩
  · intro Z hZi hZg
    rw [← cge_zero_iff_Integral]
    have hY : cge v 0 (dg gp Z) := by
      have := cge_dg v (a := 0) (b := 0) (f := gp) (fun ζ => (vge_zero_iff v _).mpr (hgp ζ))
        ((cge_zero_iff_Integral v Z).mpr hZi)
      simpa using this
    have hYg : D.Good p (dg gp Z) := TwistData.Good.dg D hZg gp
    have hPY : cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (dg gp Z)) := by
      rw [linMap_eq_sum Pj (dg gp Z)]
      refine cge_sum v _ _ fun ζ hζ => ?_
      have := cge_smul v (hY ζ) (cge_Pj_monomial hD D hr Pj hP1 hP2 ζ (hYg ζ hζ))
      simpa using this
    have hG : cge v (-(D.Dm p C0 + D.kapD p / 2)) (dg gm (Pj (dg gp Z))) := by
      have := cge_dg v (a := 0) (f := gm) (fun ζ => (vge_zero_iff v _).mpr (hgm ζ)) hPY
      simpa using this
    have := cge_smul v (vge_p_pow hD ⌈D.Dm p C0 + D.kapD p / 2⌉₊) hG
    refine cge_mono v ?_ this
    have := Nat.le_ceil (D.Dm p C0 + D.kapD p / 2)
    linarith
  · intro Z hZg
    exact TwistData.Good.dg D (good_Pj D Pj hP1 (TwistData.Good.dg D hZg gp)) gm
  · intro Z _ j i
    exact (hcost (D.chainSet j i) (D.mlab_notMem_chainSet j i) _ _ (hP3 (dg gp Z) j i)).2
  · intro Z _ j m θ _ hZ
    have a1 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) θ Z hZ).1
    have a2 := hP5 j m _ _ a1
    have a3 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) _ _ a2).2
    exact vala_mono (by linarith) a3

end Main

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

theorem eIn_apply_mb (ζ : D.EM) (b : D.Lb) (a : Fin D.r) : eIn D.outP ζ (D.mb b, a) = ζ (D.mb b, a) := by
  rw [eIn_apply]
  simp [outP, outB, mb]

theorem eIn_apply_mw (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mw t, a) = ζ (D.mw t, a) := by
  rw [eIn_apply]
  simp [outP, outB, mw]

theorem eIn_apply_mlab (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mlab t, a) = 0 := by
  rw [eIn_apply]
  simp [outP, outB, mlab]

theorem eIn_apply_mtp (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mtp t, a) = 0 := by
  rw [eIn_apply]
  simp [outP, outB, mtp]

theorem class_iff (p : ℕ) {ζ : D.EM} (hζ : D.LabLowE p ζ) (α : D.EA) :
    (D.InClass p (D.labF ζ) α ∧ D.liftE p α = eIn D.outP ζ) ↔ α = D.collapseExponent p ζ := by
  constructor
  · rintro ⟨hcl, hlift⟩
    ext ⟨i, a⟩
    rcases i with b | t
    · have h2 := congrArg (fun f => f (D.mb b, a)) hlift
      beta_reduce at h2
      rw [eIn_apply_mb] at h2
      have h1 : D.liftE p α (D.mb b, a) = α (Sum.inl b, a) := by simp [liftE, mb]
      rw [h1] at h2
      rw [h2]
      simp [collapseExponent, mb]
    · have h2 := congrArg (fun f => f (D.mw t, a)) hlift
      beta_reduce at h2
      rw [eIn_apply_mw] at h2
      have h1 : D.liftE p α (D.mw t, a) = α (Sum.inr t, a) / D.P p t := by simp [liftE, mw]
      rw [h1] at h2
      have h3 : α (Sum.inr t, a) % D.P p t = ζ (D.mlab t, a) := hcl t a
      have h4 : D.collapseExponent p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) := by
        simp [collapseExponent, mlab, mw]
      rw [h4, ← Nat.mod_add_div (α (Sum.inr t, a)) (D.P p t), h3, h2]
  · rintro rfl
    refine ⟨fun t a => ?_, ?_⟩
    · have hP : 0 < D.P p t := (Nat.zero_le _).trans_lt (hζ t a)
      show D.collapseExponent p ζ (Sum.inr t, a) % D.P p t = ζ (D.mlab t, a)
      have h4 : D.collapseExponent p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) := by
        simp [collapseExponent, mlab, mw]
      rw [h4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hζ t a)]
    · ext ⟨i, a⟩
      rcases i with b | t | t | t
      · change _ = eIn D.outP ζ (D.mb b, a)
        rw [eIn_apply_mb]
        simp [liftE, collapseExponent, mb]
      · change _ = eIn D.outP ζ (D.mlab t, a)
        rw [eIn_apply_mlab]
        simp [liftE]
      · change _ = eIn D.outP ζ (D.mw t, a)
        rw [eIn_apply_mw]
        have hP : 0 < D.P p t := (Nat.zero_le _).trans_lt (hζ t a)
        have h4 : D.collapseExponent p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) := by
          simp [collapseExponent, mlab, mw]
        have h1 : D.liftE p (D.collapseExponent p ζ) (Sum.inr (Sum.inr (Sum.inl t)), a) =
            D.collapseExponent p ζ (Sum.inr t, a) / D.P p t := by simp [liftE]
        rw [h1, h4, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (hζ t a), zero_add]
      · change _ = eIn D.outP ζ (D.mtp t, a)
        rw [eIn_apply_mtp]
        simp [liftE]

theorem coeff_digitPart_eIn (p : ℕ) {ζ : D.EM} (hζ : D.LabLowE p ζ) (G : MvPolynomial (D.OL × Fin D.r) K) :
    (D.digitPart p (D.labF ζ) G).coeff (eIn D.outP ζ) = G.coeff (D.collapseExponent p ζ) := by
  classical
  unfold digitPart
  rw [MvPolynomial.coeff_sum]
  have h : ∀ α ∈ G.support, (if D.InClass p (D.labF ζ) α then monomial (D.liftE p α) (G.coeff α) else 0 :
      MvPolynomial (D.ML × Fin D.r) K).coeff (eIn D.outP ζ) = if α = D.collapseExponent p ζ then G.coeff α else 0 := by
    intro α _
    split_ifs with h1 h2 h2
    · rw [MvPolynomial.coeff_monomial, if_pos ((D.class_iff p hζ α).2 h2).2]
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro h3
      exact h2 ((D.class_iff p hζ α).1 ⟨h1, h3⟩)
    · exact absurd ((D.class_iff p hζ α).2 h2).1 h1
    · simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with h0
  · rfl
  · exact (by simpa using h0 : G.coeff (D.collapseExponent p ζ) = 0).symm

theorem prod_choose_add {σ : Type} [Fintype σ] (β M : σ →₀ ℕ) :
    ((β + M).prod fun x k => (k.choose (M x) : K)) = ((∏ x, (β x + M x).choose (M x) : ℕ) : K) := by
  simp only [Finsupp.prod, Finsupp.coe_add, Pi.add_apply, Nat.cast_prod]
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => ?_
  have h0 : β x = 0 ∧ M x = 0 := by simpa [Finsupp.mem_support_iff] using hx
  simp [h0.1, h0.2]

def GM (F : MvPolynomial (D.OL × Fin D.r) K) (M : D.EA) : MvPolynomial (D.OL × Fin D.r) K :=
  dg (fun α => (D.ga α)⁻¹) (ddiv M (D.gaAct F))

theorem coeff_GM (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) :
    (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ) =
      (D.ga (D.collapseExponent p ζ))⁻¹ * ((D.ga (D.phE p ζ) * F.coeff (D.phE p ζ)) *
        ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K)) := by
  have hga : ∀ β, (D.gaAct F).coeff β = D.ga β * F.coeff β := by
    intro β
    unfold gaAct
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [show F.coeff β = 0 by simpa using h, mul_zero]
  unfold GM
  rw [coeff_dg, coeff_ddiv, prod_choose_add, hga]
  rfl

variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem v_gaP (hV : D.Valid v p) {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam) {ζ : D.EM}
    (hζ : D.LabLowE p ζ) : v (D.gaP p gam ζ) = 0 := by
  unfold gaP
  rw [AddValuation.map_mul, hV.2.2.2.2.2.2.1 (D.collapseExponent p ζ), zero_add]
  exact Finset.prod_induction _ (fun x => v x = 0)
    (fun a b ha hb => by rw [AddValuation.map_mul, ha, hb, add_zero]) (AddValuation.map_one v)
    (fun t _ => ((hdig.1 t (D.labF ζ t) (fun a => hζ t a)).2 (D.wF ζ t)).1)

theorem ne_zero_of_v_eq_zero {x : K} (h : v x = 0) : x ≠ 0 := by
  intro hx
  subst hx
  simp at h

theorem Lam_monomial_blk (hV : D.Valid v p) {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam)
    (F : MvPolynomial (D.OL × Fin D.r) K) {ζ : D.EM} (hζ : D.LabLowE p ζ) :
    D.abelian₂ p F (monomial ζ 1) =
      D.kapC cst ζ * (D.gaP p gam ζ * (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ) * (fact ζ : K)) := by
  have h0 : D.ga (D.collapseExponent p ζ) ≠ 0 := ne_zero_of_v_eq_zero (hV.2.2.2.2.2.2.1 _)
  have h1 := D.fact_eq_kapC hdig hζ
  have h2 : (fact (D.phE p ζ) : K) = ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K) *
      (fact (D.collapseExponent p ζ) : K) * (fact (D.tpE ζ) : K) := by
    rw [phE, fact_add_eq]; push_cast; ring
  rw [Lam_monomial, coeff_GM, h2, gaP]
  set B := ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K)
  set g := ∏ t, gam t (D.labF ζ t) (D.wF ζ t)
  have h3 : D.kapC cst ζ * (D.ga (D.collapseExponent p ζ) * g * ((D.ga (D.collapseExponent p ζ))⁻¹ *
      (D.ga (D.phE p ζ) * F.coeff (D.phE p ζ) * B)) * (fact ζ : K)) =
      (D.ga (D.phE p ζ) * F.coeff (D.phE p ζ) * B) * (D.kapC cst ζ * g * (fact ζ : K)) := by
    field_simp
  rw [h3, ← h1]; ring

theorem vge_coeff_GM (hD : DVRHyp v p) (hV : D.Valid v p) {F : MvPolynomial (D.OL × Fin D.r) K}
    (hF : F ∈ PolK K D.r D.dO) (hF0 : bge v 0 F) (ζ : D.EM) :
    vge v (-D.n0 v) ((D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ)) := by
  rw [coeff_GM]
  have a1 := (vge_unit v (hV.2.2.2.2.2.2.1 (D.collapseExponent p ζ))).2.1
  have a2 := (vge_unit v (hV.2.2.2.2.2.2.1 (D.phE p ζ))).1
  have a3 : vge v (-D.n0 v) (F.coeff (D.phE p ζ)) := by
    have := cge_of_bge hD hF hF0 (D.phE p ζ)
    rw [zero_sub] at this; exact this
  have a4 := vge_natCast v (∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x))
  have := vge_mul v a1 (vge_mul v (vge_mul v a2 a3) a4)
  exact vge_mono v (by linarith) this

theorem vge_Lam_monomial (hD : DVRHyp v p) (hV : D.Valid v p) {F : MvPolynomial (D.OL × Fin D.r) K}
    (hF0 : bge v 0 F) {ζ : D.EM} (hζ : D.GoodE p ζ) :
    vge v (D.n0 v - D.kapD p / 2) (D.abelian₂ p F (monomial ζ 1)) := by
  rw [Lam_monomial]
  have a1 := hF0 (D.phE p ζ)
  have a2 := (vge_unit v (hV.2.2.2.2.2.2.1 (D.phE p ζ))).1
  have a3 := vge_vN hD (fact_ne_zero (D.phE p ζ))
  have a4 := D.fact_phE_lower hD hV.1 hζ
  have := vge_mul v (vge_mul v a1 (vge_mul v a2 (vge_one v))) a3
  exact vge_mono v (by linarith) this

private theorem lam_eq_sum_coeff_mul_ga_mul_fact (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K)
    (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F Z = ∑ α ∈ F.support, F.coeff α * (D.ga α * (D.ph p Z).coeff α) * (fact α : K) := by
  unfold abelian₂ fock
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 2
  unfold gaAct
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [show (D.ph p Z).coeff α = 0 by simpa using h, mul_zero]

private theorem lam_sum_right (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (∑ i ∈ s, f i) = ∑ i ∈ s, D.abelian₂ p F (f i) := by
  simp only [lam_eq_sum_coeff_mul_ga_mul_fact, map_sum, MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem lam_smul_right (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (c : K)
    (Z : MvPolynomial (D.ML × Fin D.r) K) : D.abelian₂ p F (c • Z) = c * D.abelian₂ p F Z := by
  simp only [lam_eq_sum_coeff_mul_ga_mul_fact, map_smul, MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

theorem Lam_monomial_c (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) (c : K) :
    D.abelian₂ p F (monomial ζ c) = c * D.abelian₂ p F (monomial ζ 1) := by
  rw [show (monomial ζ c : MvPolynomial (D.ML × Fin D.r) K) = c • monomial ζ 1 by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], lam_smul_right]

theorem Lam_dg (F : MvPolynomial (D.OL × Fin D.r) K) (g : D.EM → K) (W : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (dg g W) = ∑ ζ ∈ W.support, g ζ * W.coeff ζ * D.abelian₂ p F (monomial ζ 1) := by
  rw [dg_eq_lsup, lsup_apply, lam_sum_right]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [lam_smul_right, Lam_monomial_c]
  ring

theorem ldeg_tpE (ζ : D.EM) (t : D.Tau) : ldeg (D.tpE ζ) (Sum.inr t) = ldeg ζ (D.mtp t) := by
  unfold ldeg
  rfl

theorem msg_of_eOut_ne_zero (ζ : D.EM) (i : D.ML) (a : Fin D.r) (h : eOut D.outP ζ (i, a) ≠ 0) :
    D.msg i = true := by
  rw [eOut_apply] at h
  split_ifs at h with hi
  · rcases i with b | t | t | t
    · simp [outP, outB] at hi
    · rfl
    · simp [outP, outB] at hi
    · rfl
  · exact absurd rfl h

theorem value_monomial {C0 : ℝ} (hD : DVRHyp v p) (h1 : 1 ≤ C0) (hV : D.Valid v p) (hH : D.HypH p 13)
    (hE : StepE K v p) {F : MvPolynomial (D.OL × Fin D.r) K} (hF : D.InXX p F) (hF0 : bge v 0 F)
    {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K} {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K}
    (hdig : D.DigOK v p cst gam)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → D.SameBlockAlt ζ ζ')
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (hP4 : ∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1))
    (gm : D.EM → K)
    (hgm : ∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹))
    {ζ : D.EM} (hζ : D.GoodE p ζ) :
    vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (D.abelian₂ p F (dg gm (Pj (monomial ζ 1))) - D.abelian₂ p F (dg gm (monomial ζ 1))) := by
  classical
  have hDm := D.Dm_nonneg (two_le_p hD) hV.1 h1
  obtain ⟨Q0, E', hQ, hQ0, hE'⟩ := hE hD D hV hH F hF hF0 (D.tpE ζ) (fun b a => by simp [tpE])
    (fun t => by rw [ldeg_tpE]; exact hζ.2.2.2.2 t) (D.labF ζ)
  set μ := eOut D.outP ζ with hμ
  set A := hcomp (fun i => ldeg ζ i) (monomial μ 1 * Q0) with hA
  set κ := D.kapC cst ζ with hκ
  set e : D.EM → K := fun ζ' =>
    gm ζ' * D.gaP p gam ζ' * (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ') - A.coeff ζ' with he

  have key : ∀ W : MvPolynomial (D.ML × Fin D.r) K, (∀ ζ' ∈ W.support, D.SameBlockAlt ζ ζ') →
      D.abelian₂ p F (dg gm W) = κ * fock A W + ∑ ζ' ∈ W.support, κ * (W.coeff ζ' * e ζ' * (fact ζ' : K)) := by
    intro W hW
    rw [Lam_dg, fock_eq_sum_right, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ζ' hζ' => ?_
    have hb := hW ζ' hζ'
    rw [D.Lam_monomial_blk hV hdig F (hζ.good_exponent_same_block D hb).1, D.tangent_exponent_same_block hb, D.kappa_constant_same_block cst hb, he]
    ring

  have herr : ∀ ζ', D.SameBlockAlt ζ ζ' → vge v (D.c - D.n0 v) (e ζ') := by
    intro ζ' hb
    have hl := (hζ.good_exponent_same_block D hb).1
    have c1 : A.coeff ζ' = Q0.coeff (eIn D.outP ζ') := by
      rw [hA, coeff_hcomp, if_pos hb.1]
      conv_lhs => rw [← eOut_add_eIn D.outP ζ', D.output_exponent_same_block hb]
      rw [coeff_monomial_mul, one_mul]
    have c2 : (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ') =
        Q0.coeff (eIn D.outP ζ') + E'.coeff (eIn D.outP ζ') := by
      rw [← D.coeff_digitPart_eIn p hl, D.label_function_same_block hb, ← coeff_add, ← hQ]; rfl
    have hu := D.v_gaP hV hdig hl
    have hu0 := ne_zero_of_v_eq_zero hu
    have c3 : e ζ' = (gm ζ' - (D.gaP p gam ζ')⁻¹) * D.gaP p gam ζ' *
        (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ') + E'.coeff (eIn D.outP ζ') := by
      rw [he]; simp only; rw [c1, sub_mul, inv_mul_cancel₀ hu0]
      have := c2
      linear_combination this
    rw [c3]
    have b1 : vge v (D.c : ℝ) (gm ζ' - (D.gaP p gam ζ')⁻¹) := (vge_natCast_bound v _ _).mpr (hgm ζ' hl)
    have b2 := (vge_unit v hu).1
    have b3 : vge v (-D.n0 v) ((D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ')) := by
      rw [← D.tangent_exponent_same_block hb]; exact D.vge_coeff_GM hD hV hF.1 hF0 ζ'
    refine vge_add v ?_ (hE' _)
    exact vge_mono v (by linarith) (vge_mul v (vge_mul v b1 b2) b3)

  have hterm : ∀ ζ', D.SameBlockAlt ζ ζ' → ∀ w : K,
      vge v (vN v (fact ζ) / 2 - D.Dm p C0 - vN v (fact ζ') / 2) w →
      vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0) (κ * (w * e ζ' * (fact ζ' : K))) := by
    intro ζ' hb w hw
    have hg' := hζ.good_exponent_same_block D hb
    have k1 := D.vge_kapC hD hdig hg'.1
    rw [D.kappa_constant_same_block cst hb] at k1
    have k2 := D.vge_kapC hD hdig hζ.1
    have w1 := D.wt_lower hD hV.1 hg'
    have w2 := D.wt_lower hD hV.1 hζ
    have f1 := vge_vN hD (fact_ne_zero ζ')
    have t1 := vge_mul v (vge_mul v hw (herr ζ' hb)) f1
    rcases le_total (vN v (fact ζ')) (vN v (fact ζ)) with hle | hle
    · exact vge_mono v (by linarith) (vge_mul v k1 t1)
    · exact vge_mono v (by linarith) (vge_mul v k2 t1)
  have hs1 : ∀ ζ' ∈ (Pj (monomial ζ 1)).support, D.SameBlockAlt ζ ζ' := fun ζ' h => hP1 ζ ζ' h
  have hs2 : ∀ ζ' ∈ (monomial ζ (1 : K)).support, D.SameBlockAlt ζ ζ' := by
    intro ζ' h
    have := support_monomial_subset h
    rw [Finset.mem_singleton] at this
    rw [this]; exact TwistData.SameBlockAlt.refl D ζ
  have hAv : ∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A :=
    fun j i => vala_hcomp _ (vala_mul_left_nonneg
      (valS_monomial_nonneg_of_vec μ 1 (D.msg_of_eOut_ne_zero ζ)) (hQ0 j i))
  rw [key _ hs1, key _ hs2, hP4 A ζ (hcomp_mem_PolK _ _) hAv, add_sub_add_left_eq_sub]
  refine vge_sub v (vge_sum v _ _ fun ζ' h => hterm ζ' (hs1 ζ' h) _ (hP2 ζ hζ ζ'))
    (vge_sum v _ _ fun ζ' h => hterm ζ' (hs2 ζ' h) _ ?_)
  have := support_monomial_subset h
  rw [Finset.mem_singleton] at this
  rw [this, coeff_monomial, if_pos rfl]
  exact vge_mono v (by linarith) (vge_one v)

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem omega_value (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p) (hH : D.HypH p 13)
    (hE : StepE K v p) {F : MvPolynomial (D.OL × Fin D.r) K} (hF : D.InXX p F) (hF0 : bge v 0 F)
    {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K} {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K}
    (hdig : D.DigOK v p cst gam)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → D.SameBlockAlt ζ ζ')
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (hP4 : ∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1))
    (gp gm : D.EM → K) (hgp0 : ∀ ζ, 0 ≤ v (gp ζ))
    (happ : ∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gp ζ - D.gaP p gam ζ) ∧
        ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZi : Integral v Z) (hZg : D.Good p Z) :
    vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (D.abelian₂ p F (dg gm (Pj (dg gp Z))) - D.abelian₂ p F Z) := by
  have key : ∀ W, D.abelian₂ p F W = fock F (dg D.ga (D.ph p W)) := fun W => by
    simp only [TwistData.abelian₂, gaAct_eq_dg]
  have hLsum : ∀ (s : Finset D.EM) (f : D.EM → MvPolynomial (D.ML × Fin D.r) K),
      D.abelian₂ p F (∑ i ∈ s, f i) = ∑ i ∈ s, D.abelian₂ p F (f i) := by
    intro s f
    simp only [key, map_sum, fock_sum_right]
  have hLsmul : ∀ (c : K) (W : MvPolynomial (D.ML × Fin D.r) K), D.abelian₂ p F (c • W) = c * D.abelian₂ p F W := by
    intro c W
    simp only [key, map_smul, fock_smul_right]
  have hmon : ∀ (g : D.EM → K) (ζ : D.EM), dg g (monomial ζ (1 : K)) = g ζ • monomial ζ (1 : K) := by
    intro g ζ
    rw [dg_monomial, MvPolynomial.smul_monomial, smul_eq_mul]
  have hZ : Z = ∑ ζ ∈ Z.support, Z.coeff ζ • monomial ζ (1 : K) := by
    conv_lhs => rw [Z.as_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hp2 : 2 ≤ p := by have := hD.five_le; omega
  have hr1 : 1 ≤ D.r := hV.1
  have hkap : 0 ≤ D.kapD p := by
    unfold TwistData.kapD kap
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (lg_nonneg' hp2 hr1 _)
  have hDm : 0 ≤ D.Dm p C0 := TwistData.Dm_nonneg (D := D) hp2 hr1 h1
  rw [hZ, map_sum (dg gp), map_sum Pj, map_sum (dg gm), hLsum, hLsum, ← Finset.sum_sub_distrib]
  simp only [map_smul, hLsmul]
  apply vge_sum'
  intro ζ hζ
  rw [← mul_sub]
  have hgood : D.GoodE p ζ := hZg ζ hζ
  have hlow : D.LabLowE p ζ := hgood.1
  have h1' : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) =
      gp ζ * D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) := by
    rw [hmon, map_smul, map_smul, hLsmul]
  have h2' : D.abelian₂ p F (dg gm (monomial ζ (1 : K))) = gm ζ * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [hmon, hLsmul]
  have hexp : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) - D.abelian₂ p F (monomial ζ (1 : K)) =
      gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K)))) +
        (gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [h1', h2']
    ring
  rw [hexp]
  have hval := TwistData.value_monomial (D := D) hD h1 hV hH hE hF hF0 hdig Pj hP1 hP2 hP4 gm
    (fun ζ h => (happ ζ h).2) hgood
  have hZζ : vge v 0 (Z.coeff ζ) := (vge_zero_iff v _).mpr (hZi ζ)
  have hgp' : vge v 0 (gp ζ) := (vge_zero_iff v _).mpr (hgp0 ζ)
  have t1 : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K))))) := by
    have := vge_mul' v hgp' hval
    simpa using this
  have hgaP : v (D.gaP p gam ζ) = 0 := TwistData.v_gaP (D := D) hV hdig hlow
  have hg0 : D.gaP p gam ζ ≠ 0 := by
    intro h
    rw [h] at hgaP
    simp at hgaP
  have hgaP' : vge v 0 (D.gaP p gam ζ) := (vge_zero_iff v _).mpr (le_of_eq hgaP.symm)
  have hc1 : vge v (D.c : ℝ) (gp ζ - D.gaP p gam ζ) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gp ζ - D.gaP p gam ζ)).mpr (by exact_mod_cast (happ ζ hlow).1)
    simpa using this
  have hc2 : vge v (D.c : ℝ) (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gm ζ - (D.gaP p gam ζ)⁻¹)).mpr (by exact_mod_cast (happ ζ hlow).2)
    simpa using this
  have hgm' : vge v 0 (gm ζ) := by
    have h3 : gm ζ = (gm ζ - (D.gaP p gam ζ)⁻¹) + (D.gaP p gam ζ)⁻¹ := by ring
    rw [h3]
    refine vge_add' v (vge_mono' v (by positivity) hc2) ?_
    rw [vge_zero_iff v, AddValuation.map_inv, hgaP, neg_zero]
  have hsplit : gp ζ * gm ζ - 1 =
      (gp ζ - D.gaP p gam ζ) * gm ζ + D.gaP p gam ζ * (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    rw [mul_sub (D.gaP p gam ζ), mul_inv_cancel₀ hg0]
    ring
  have t2 : vge v (D.c : ℝ) (gp ζ * gm ζ - 1) := by
    rw [hsplit]
    refine vge_add' v ?_ ?_
    · simpa using vge_mul' v hc1 hgm'
    · simpa using vge_mul' v hgaP' hc2
  have hΛ := TwistData.vge_Lam_monomial (D := D) hD hV hF0 hgood
  have t3 := vge_mul' v t2 hΛ
  have t3' : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      ((gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K))) := vge_mono' v (by linarith) t3
  simpa using vge_mul' v hZζ (vge_add' v t1 t3')

theorem stepDEF_of (h1 : 1 ≤ C0) (hDIG : DIG K v p) (hG : StepG K v p) (hP : StepP K v p C0)
    (hE : StepE K v p) : StepDEF K v p C0 := by
  intro hD D hV hH _ F hF hF0
  have hF0' := (exists_of_vBB_zero v F hF0).2
  obtain ⟨Pj, hP1, hP2, hP3, hP4, hP5⟩ := hP hD D hV
  obtain ⟨cst, gam, hdig⟩ := D.digOK_exists hDIG hD hV.2.2.1
  obtain ⟨gp, gm, hgp, hgm, happ, hcost⟩ := hG hD D hV cst gam hdig
  obtain ⟨hN, hI, hGd, hch, hY⟩ :=
    omega_clauses hD h1 D hV Pj ⟨hP1, hP2, hP3, hP4, hP5⟩ gp gm hgp hgm hcost
  refine ⟨(dg gm).comp (Pj.comp (dg gp)), ⌈D.Dm p C0 + D.kapD p / 2⌉₊, hN, hI, hGd, hch, hY, ?_⟩
  intro Z hZi hZg
  exact omega_value hD h1 D hV hH hE hF hF0' hdig Pj hP1 hP2 hP4 gp gm hgp happ Z hZi hZg

end Formalism.MainNotions.PlaneGram
end
end

section
namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem plane_gram_theorem_of_five_lemmas (h1 : 1 ≤ C0) (hV2 : V2 K) (hSPAN : SPAN K v p) (hPROJ : PROJ K v p C0)
    (hDIG : DIG K v p) (hDER : DER K v p) : LiftBoundUniform K v p C0 :=
  plane_gram_theorem_of_combined_lemmas h1 (stepBC_of (stepB_of h1 hV2 hPROJ) (stepC_of hV2 (segStep_of hSPAN)))
    (stepDEF_of h1 hDIG (stepG_of hV2) (stepP_of v p C0 h1 hPROJ) (stepE_of v p hV2 hDER))


end Formalism.MainNotions.PlaneGram
end
