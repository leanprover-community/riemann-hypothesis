import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemSpanOfSemilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourMulRootLt

section
noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem pos_iff_side_mem_max {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0)
    (e : ↥D.LL0 →+* FractionRing (D.ntw.O0 (c.twI w)))
    (he : e = if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) :
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y = e (x : ↥D.LL0) := by
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (e (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) e (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = e (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have e1 := h.embedding_baseField_condition w x y 1 one_ne_zero (by rw [← he, map_one, mul_one, hy])
  simp only [map_one, mul_one] at e1
  rw [hleft, GlobalTheory.TwistGoodCompare.pos_iff_not_isUnit c w _ _ e1, not_iff_not]
  exact ⟨GlobalTheory.TwistGoodCompare.isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩

theorem resChar_eq_of_pos {D : D7} (w : D.what₂.places.Pl) {p : ℕ} (hp : p.Prime)
    (h : 0 < D.what₂.places.val w ((p : ℕ) : D.what₂.LL)) : D.what₂.places.resChar w = p := by
  by_contra hne
  have hq := D.what₂.places.resChar_prime w
  have hq0 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar w]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have hnat : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (D.what₂.places.val w).map_le_add ih (by simp)
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa using hnat m
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hnat m
  have h1 : (a : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) + (b : D.what₂.LL) * ((p : ℕ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) hab
  have h2 : 0 < D.what₂.places.val w 1 := by
    rw [← h1]
    refine (D.what₂.places.val w).map_lt_add ?_ ?_
    · rw [AddValuation.map_mul]; exact hq0.trans_le (le_add_of_nonneg_left (hint a))
    · rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b))
  simp at h2

theorem twCoverPair_of_tie (D : D7) (c : NChoice D) (h : NChTie D c) : TwCoverPair D := by
  rintro p hp w hw ⟨w', -, hw'⟩
  refine ⟨c.twI w', ?_, ?_⟩
  · rw [c.twI_l]
    refine resChar_eq_of_pos w' hp ?_
    simpa using (hw' _).1 hw
  · cases hs : c.sd w'
    · exact Or.inr fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_neg (by simp)]))
    · exact Or.inl fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_pos rfl]))

end GlobalTheory.Mem.Top

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.LayOfCore

variable {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B}

theorem ties (c : V4.Core K X f T) : Formalism.BasicNotions.Ties X.toD7 :=
  ⟨c.real.cdScale, c.real.dsig_all, c.row.bu_def, twCoverPair_of_tie _ _ c.nch_tie, X.B.coeffGaloisSubfield_isGalois, c.row.ft_occ⟩

theorem dgam (c : V4.Core K X f T) : DGamDef X.toD7 := fun u μ =>
  ⟨fun u' μ' i hi x => by
    rw [c.col.one u μ, ← c.col.one u' μ']
    exact (X.toD7.chTw u' μ').dvd_DGam i hi x, c.col.one u μ⟩

noncomputable def lay (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : Lay X.toD7 :=
  { c.O with
    ties := ties c
    rrDef := c.row.rrDef
    th_io := c.th_io
    vram := c.gy.vram
    fills_all := c.gy.fills
    idx := c.row.idx
    kap_def := c.row.kap_def
    lam_def := c.row.lam_def
    kapR_def := c.row.kapR_def
    piG_lev := c.col.piG_lev
    piT_lev := c.col.piT_lev
    seen := c.col.seen
    tauOf := c.col.tauOf
    dgam := dgam c
    nch_tie := c.nch_tie
    rationalRoots_def := c.row.rationalRoots_def
    duStar_def := (sizes_eq_count K X c.isOver hv c.dsig_eq).1
    Dstar_def := (sizes_eq_count K X c.isOver hv c.dsig_eq).2
    gauge_def := c.gauge_def }

theorem layObj_lay (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : layObj (lay c hv) = c.O := rfl

theorem isOver (c : V4.Core K X f T) : Over X.toD7 K.P K.Lv := by
  obtain ⟨sp, hT, hY, hA, hV, hz, h, -⟩ := c.isOver
  exact ⟨sp, hT, hY, hA, hV, hz, X, h, rfl⟩

theorem untw (c : V4.Core K X f T) (w : X.toD7.what₂.places.Pl) (hw : X.toD7.what₂.muAt w = X.toD7.what₂.mu0) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ X.toD7.R.m) : X.toD7.what₂.Aj j w = 0 := by
  have a := c.row.untw w hw j h1 h2
  have b := c.row.untw (X.toD7.what₂.places.conj w) ((X.toD7.what₂.muAt_conj w).trans hw) j h1 h2
  unfold Rows.Data.Aj
  rw [hw, a.1, a.2, b.1]
  rfl

theorem fin (c : V4.Core K X f T) : {w | X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0}.Finite :=
  (TwFin.tw_fin X.B f T).2.2.2.subset fun w hw => c.mu.sub w (by_contra fun h => hw (c.mu.off w h))

theorem ledOK (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : LedOK K.s K.C K.cD K.ch (lay c hv) K.a K.b := by
  intro L hs hW hV
  refine ⟨fun w hw j hj => ?_, fun I hI he hk hf => ⟨c.gy.led L hs hW hV I hI he hk hf, fun u w hg => ?_, fun u w hg _ =>
    NP_full X.toD7 L I c.O.Gy K.C.GK c.O.cmp c.gy.vram u w hg⟩⟩
  · refine c.fval L hs hW hV w (fun h => (TwFin.tw_fin X.B f T).2.1 w ?_) j hj
    rw [← c.mu.tw w, ← c.mu.on w h]
    exact (congrArg c.xi hw).trans c.mu.mu0
  · have hC : K.C.cX.Ce = 1 := by
      have := K.std.1
      unfold FC.Fixed at this
      tauto
    rw [(c.gatNum u w hg).2, he, hC, hs]

theorem tupUsed (c : V4.Core K X f T) : DQ.TupUsedAt X.toD7 := by
  intro μ
  have hμ : c.xi μ ∈ T.set f := c.mu.range ▸ Set.mem_range_self μ
  rcases hμ with (h | h | h) | ⟨w, h⟩
  · exact .inl (c.mu.inj (h.trans c.mu.mu0.symm))
  · exact .inr (.inl (c.mu.inj (h.trans c.mu.star.symm)))
  · exact .inr (.inr (.inl (c.mu.inj (h.trans c.mu.star'.symm))))
  · by_cases hw : w ∈ c.Wt
    · exact .inr (.inr (.inr ⟨w, (c.mu.inj (h.symm.trans (c.mu.tw w).symm)).trans (c.mu.on w hw).symm⟩))
    · unfold TwDat.xiTw at h
      rw [c.mu.supp w hw, mul_one] at h
      split_ifs at h
      · exact .inr (.inr (.inl (c.mu.inj (h.symm.trans c.mu.star'.symm))))
      · exact .inr (.inl (c.mu.inj (h.symm.trans c.mu.star.symm)))

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem lay_of_core : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T),
    StandardLattice.VolumeEqMass₂ X.toD7 → ∃ Y : Lay X.toD7, layObj Y = c.O ∧ Over X.toD7 K.P K.Lv ∧ RecOK K.s K.C K.cD X.toD7 ∧
      LedOK K.s K.C K.cD K.ch Y K.a K.b ∧ DQ.TupUsedAt X.toD7 :=
  ev_imp TamePow.tame_of_pow fun _ hK X _ _ c hv =>
    ⟨lay c hv, layObj_lay c hv, isOver c,
      ⟨c.del, c.etaF, untw c, fin c, (Full.dgam_pos_and_full X.toD7).1, (Full.dgam_pos_and_full X.toD7).2,
        hK X c.isOver c.chiT, c.col.mink, c.col.atT⟩, ledOK c hv, tupUsed c⟩

end GlobalTheory.Mem.Top.LayOfCore
end
