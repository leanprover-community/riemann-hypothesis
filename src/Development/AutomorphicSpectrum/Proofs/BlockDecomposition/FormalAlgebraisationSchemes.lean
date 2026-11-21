import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLiftingOfSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoOfIsClosedImmersionOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec

section
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre GlobalTheory.ProjSpace

namespace GlobalTheory.CompanionTheory.ConsecAmple

variable {R : Type} [CommRing R] {X Y Z P : Scheme.{0}}

theorem veryAmpleBy_box {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Spec (CommRingCat.of R)}
    {g : Y ⟶ Spec (CommRingCat.of R)} (sq : IsPullback p q f g) {H : LB X} {K : LB Y} {m n : ℕ}
    {s : Fin (m + 1) → LB.Sec H} {t : Fin (n + 1) → LB.Sec K} (hf : VeryAmpleBy f H s) (hg : VeryAmpleBy g K t)
    (e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1)) :
    VeryAmpleBy (p ≫ f) (box p q H K) fun a => boxSec p q (s (e a).1) (t (e a).2) := by
  obtain ⟨hs, hs'⟩ := hf
  obtain ⟨ht, ht'⟩ := hg
  refine ⟨?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show q y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩
    rw [nonzeroLocus_boxSec, e.apply_symm_apply]
    exact ⟨hi, hj⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' (e a).1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := ht' (e a).2
  have loc := nonzeroLocus_boxSec p q (s (e a).1) (t (e a).2)
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  have o₁ : r₁ (e a).1 = 1 := ratio_self _ _ (hr₁ _)
  have o₂ : r₂ (e a).2 = 1 := ratio_self _ _ (hr₂ _)
  refine ⟨?_, fun b => ap p l₁ (r₁ (e b).1) * ap q l₂ (r₂ (e b).2), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg₂ (· * ·) (ap_ratio p (hr₁ (e b).1 k.1) _ _) (ap_ratio q (hr₂ (e b).2 k.2) _ _)).trans
      (mul_mul_mul_comm _ _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm (i, (e a).2)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₂, map_one, _root_.mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change ap q l₂ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e a).1, i)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₁, map_one, _root_.one_mul]

theorem veryAmpleBy_secPull {f : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y} {M : ℕ} {s : Fin (M + 1) → LB.Sec L}
    (h : VeryAmpleBy f L s) (j : Z ⟶ Y) [IsClosedImmersion j] :
    VeryAmpleBy (j ≫ f) (L.pull j) fun i => GlobalTheory.Cartier.secPull (s i) j := by
  obtain ⟨hs, hc⟩ := (veryAmpleBy_iff f s).1 h
  refine (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_secPull hs j, ?_⟩
  rw [toProj_secPull hs j]
  infer_instance

theorem gm_ap (p : P ⟶ X) {U : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ U) (r : Z ⟶ P) (z : Z) (hz : r z ∈ W)
    (u : Γ(X, U)ˣ) : gm r z W (Units.map (ap p h).toMonoidHom u) = gm (r ≫ p) z U u := by
  have e : Units.map (ap p h).toMonoidHom u = res h (pullU p U u) := Units.ext rfl
  rw [e]
  exact (gm_res r z h hz _).trans (gm_pull r p z U (h hz) u)

theorem gm_box (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (K : LB Y) (r : Z ⟶ P) (z : Z) (a b : H.ι × K.ι)
    (h : r z ∈ (box p q H K).U a ⊓ (box p q H K).U b) :
    gm r z ((box p q H K).U a ⊓ (box p q H K).U b) ((box p q H K).g a b) =
      gm (r ≫ p) z (H.U a.1 ⊓ H.U b.1) (H.g a.1 b.1) * gm (r ≫ q) z (K.U a.2 ⊓ K.U b.2) (K.g a.2 b.2) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_ap p _ r z h _) (gm_ap q _ r z h _))

theorem mem_box_of_graph (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (B : LB Y) (ψ : X ⟶ Y) (j : X ⟶ P) (hp : j ≫ p = 𝟙 X)
    (hq : j ≫ q = ψ) (c : (B.pull ψ).ι × H.ι) (y : X) (hy : y ∈ (tw (B.pull ψ) H 1).U c) :
    j y ∈ (box p q H B).U (c.2, c.1 PUnit.unit) := by
  have h₁ : p (j y) = y := by rw [← Scheme.Hom.comp_apply, hp]; rfl
  have h₂ : q (j y) = ψ y := by rw [← Scheme.Hom.comp_apply, hq]
  have h₃ : ψ y ∈ B.U (c.1 PUnit.unit) := mem_pull.1 hy.1
  have h₄ : y ∈ H.U c.2 := hy.2
  exact ⟨show p (j y) ∈ H.U c.2 by rw [h₁]; exact h₄, show q (j y) ∈ _ by rw [h₂]; exact h₃⟩

def chartPullBox (p : P ⟶ X) (q : P ⟶ Y) (H : LB X) (B : LB Y) (ψ : X ⟶ Y) (j : X ⟶ P) (hp : j ≫ p = 𝟙 X)
    (hq : j ≫ q = ψ) : ChartPull (tw (B.pull ψ) H 1) (box p q H B) j where
  idx c := (c.2, c.1 PUnit.unit)
  le c y hy := mem_box_of_graph p q H B ψ j hp hq c y hy
  g y c c' hc hc' := by
    refine (GlobalTheory.LBAlg.gm_tw (B.pull ψ) H 1 (𝟙 X) y c c' ⟨hc, hc'⟩).trans (Eq.trans ?_
      (gm_box p q H B j y _ _ ⟨mem_box_of_graph p q H B ψ j hp hq c y hc,
        mem_box_of_graph p q H B ψ j hp hq c' y hc'⟩).symm)
    rw [gm_pull_g B ψ (𝟙 X) y c.1 c'.1 hc.1 hc'.1, hp, hq, Category.id_comp, zpow_one, mul_comm]

theorem exists_veryAmpleBy_tw {f : X ⟶ Spec (CommRingCat.of R)} {K M : LB X} (hK : K.IsLB) (hM : M.IsLB) {m n : ℕ}
    {a : Fin (m + 1) → LB.Sec K} (ha : VeryAmpleBy f K a) {c : Fin (n + 1) → LB.Sec M}
    (hc : ⨆ i, nonzeroLocus (c i) = ⊤) :
    ∃ (m' : ℕ) (s : Fin (m' + 1) → LB.Sec (tw M K 1)), VeryAmpleBy f (tw M K 1) s := by
  have hψ : toProj f c hc ≫ PSpace.str R n = f := toProj_str f c hc
  have sq := IsPullback.of_hasPullback f (PSpace.str R n)
  let j : X ⟶ pullback f (PSpace.str R n) := pullback.lift (𝟙 X) (toProj f c hc) (by rw [hψ, Category.id_comp])
  have hp : j ≫ pullback.fst f (PSpace.str R n) = 𝟙 X := pullback.lift_fst _ _ _
  have hq : j ≫ pullback.snd f (PSpace.str R n) = toProj f c hc := pullback.lift_snd _ _ _
  have := isProper_str R n
  have : IsSeparated (pullback.fst f (PSpace.str R n)) := inferInstance
  have : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ pullback.fst f (PSpace.str R n)) := by rw [hp]; infer_instance
    exact IsClosedImmersion.of_comp j (pullback.fst f (PSpace.str R n))
  have hcoord : VeryAmpleBy (PSpace.str R n) (O1 R n) (coord R n) :=
    (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_coord R n, by rw [toProj_coord]; infer_instance⟩
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) := (finCongr (by ring)).trans finProdFinEquiv.symm
  have h₁ := veryAmpleBy_secPull (veryAmpleBy_box sq ha hcoord e) j
  have e₁ : j ≫ pullback.fst f (PSpace.str R n) ≫ f = f := by rw [← Category.assoc, hp, Category.id_comp]
  rw [e₁] at h₁
  have hB := isLB_box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) hK (O1_isLB R n)
  have hO := LB.isLB_pull (O1_isLB R n) (toProj f c hc)
  have i₁ : LBIso ((box (pullback.fst f (PSpace.str R n)) (pullback.snd f (PSpace.str R n)) K (O1 R n)).pull j)
      (tw ((O1 R n).pull (toProj f c hc)) K 1) :=
    LBIso.chartPull (chartPullPull _ j) (chartPullBox _ _ K (O1 R n) _ j hp hq) (GlobalTheory.LBAlg.lbIso_self hB)
  have i₂ := GlobalTheory.LBAlg.lbIso_tw_congr (t := 1) hK (lbIso_pullback_O1_toProj f c hc)
  obtain ⟨t, ht⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (LB.isLB_pull hB j) (isLB_tw hM hK 1)
    (LBIso.trans (LB.isLB_pull hB j) (isLB_tw hO hK 1) (isLB_tw hM hK 1) i₁ i₂) h₁
  exact ⟨_, t, ht⟩

theorem gm_pw (H : LB X) (n : ℤ) (r : Z ⟶ X) (z : Z) (i j : H.ι) :
    gm r z ((pw H n).U i ⊓ (pw H n).U j) ((pw H n).g i j) = gm r z (H.U i ⊓ H.U j) (H.g i j) ^ n :=
  map_zpow _ _ _

theorem pw_pw (L : LB X) (a b : ℤ) : pw (pw L a) b = pw L (a * b) := by
  change (⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩
  simp only [zpow_mul]

theorem lbIso_tw_tw_pw {L : LB X} (hL : L.IsLB) (N t : ℤ) :
    LBIso (tw (tw L (pw L N) t) (pw (pw L N) t) 1) (pw L (1 + 2 * N * t)) := by
  have l₁ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.1 :=
    fun p x hx => ⟨hx.1, hx.2.1.1⟩
  have l₂ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1.2 :=
    fun p x hx => ⟨hx.1, hx.2.1.2⟩
  have l₃ : ∀ p : L.ι × ((L.ι × L.ι) × L.ι), L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.2 :=
    fun p x hx => ⟨hx.1, hx.2.2⟩
  have v : ∀ (x : X) (p : L.ι × ((L.ι × L.ι) × L.ι)), x ∈ L.U p.1 ⊓ ((L.U p.2.1.1 ⊓ L.U p.2.1.2) ⊓ L.U p.2.2) →
      gm (𝟙 X) x _ (res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) *
          res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) =
        gm (𝟙 X) x _ (L.g p.1 p.2.1.1) * gm (𝟙 X) x _ (L.g p.1 p.2.1.2) ^ (N * t) *
          gm (𝟙 X) x _ (L.g p.1 p.2.2) ^ (N * t) :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res _ x _ hx _) ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _)))))
      ((map_zpow _ _ _).trans (congrArg (· ^ (N * t)) (gm_res _ x _ hx _))))
  have key : ∀ (x : X) {a b i j : L.ι}, x ∈ L.U a → x ∈ L.U b → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (L.g a i) = gm (𝟙 X) x _ (L.g a b) * gm (𝟙 X) x _ (L.g b j) * (gm (𝟙 X) x _ (L.g i j))⁻¹ := by
    intro x a b i j ha hb hi hj
    rw [gm_cocycle hL (𝟙 X) x ha hb hj, ← gm_cocycle hL (𝟙 X) x ha hi hj, mul_inv_cancel_right]
  refine GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (L.g p.1 p.2.1.1) * res (l₂ p) (L.g p.1 p.2.1.2) ^ (N * t) *
    res (l₃ p) (L.g p.1 p.2.2) ^ (N * t)) fun x p q h₁ h₂ h₃ h₄ => ?_
  have eA : gm (𝟙 X) x _ ((tw (tw L (pw L N) t) (pw (pw L N) t) 1).g p.2 q.2) =
      gm (𝟙 X) x (L.U p.2.1.1 ⊓ L.U q.2.1.1) (L.g p.2.1.1 q.2.1.1) *
        gm (𝟙 X) x (L.U p.2.1.2 ⊓ L.U q.2.1.2) (L.g p.2.1.2 q.2.1.2) ^ (N * t) *
        gm (𝟙 X) x (L.U p.2.2 ⊓ L.U q.2.2) (L.g p.2.2 q.2.2) ^ (N * t) := by
    refine (GlobalTheory.LBAlg.gm_tw (tw L (pw L N) t) (pw (pw L N) t) 1 (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩).trans ?_
    rw [GlobalTheory.LBAlg.gm_tw L (pw L N) t (𝟙 X) x p.2.1 q.2.1 ⟨h₂.1, h₄.1⟩]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) ?_
    · exact (congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.1.2 q.2.1.2)).trans (zpow_mul _ _ _).symm
    · exact ((zpow_one _).trans (gm_pw (pw L N) t (𝟙 X) x p.2.2 q.2.2)).trans
        ((congrArg (· ^ t) (gm_pw L N (𝟙 X) x p.2.2 q.2.2)).trans (zpow_mul _ _ _).symm)
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw L _ (𝟙 X) x p.1 q.1).symm
    (congrArg (·⁻¹) eA.symm)) (v x q ⟨h₃, h₄⟩).symm))
  have k₁ := key x (a := p.1) (b := q.1) (i := p.2.1.1) (j := q.2.1.1) h₁ h₃ h₂.1.1 h₄.1.1
  have k₂ := key x (a := p.1) (b := q.1) (i := p.2.1.2) (j := q.2.1.2) h₁ h₃ h₂.1.2 h₄.1.2
  have k₃ := key x (a := p.1) (b := q.1) (i := p.2.2) (j := q.2.2) h₁ h₃ h₂.2 h₄.2
  rw [k₁, k₂, k₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem exists_consecutive_veryAmple : ∀ (A : Type) [CommRing A] [IsNoetherianRing A]
    (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∃ (m : ℕ)
    (s : Fin (m + 1) → LB.Sec (pw L (d : ℤ))) (m' : ℕ) (s' : Fin (m' + 1) → LB.Sec (pw L ((d + 1 : ℕ) : ℤ))),
    VeryAmpleBy X.hom (pw L (d : ℤ)) s ∧ VeryAmpleBy X.hom (pw L ((d + 1 : ℕ) : ℤ)) s' := by
  intro A _ _ X L hL hA
  obtain ⟨N, hN, m, s, hH, hs⟩ := veryAmpleBy_of_relAmple hL hA (𝟙 X.left) (Category.id_comp _) hL
    (LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _)) (GlobalTheory.LBAlg.lbIso_self hL))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.TwistGen.twist_generated A X.left X.hom (pw L N) m s hH hs L hL
  obtain ⟨T, hT, hTt⟩ : ∃ T : ℕ, 1 ≤ T ∧ t₀ ≤ (T : ℤ) := ⟨(max t₀ 1).toNat, by omega, by omega⟩
  obtain ⟨n', u, hu⟩ := ht₀ T hTt
  obtain ⟨k, a, ha⟩ := veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs T hT
  have hK := isLB_pw hH T
  have hM := isLB_tw hL hH T
  obtain ⟨m', s', hs'⟩ := exists_veryAmpleBy_tw hK hM ha hu
  obtain ⟨t', ht'⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw hM hK 1) (isLB_pw hL _)
    (lbIso_tw_tw_pw hL N T) hs'
  have A₁ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T : ℕ) : ℤ))),
      VeryAmpleBy X.hom (pw L ((2 * N * T : ℕ) : ℤ)) a := by
    have e₁ : pw L ((2 * N * T : ℕ) : ℤ) = pw (pw L N) ((2 * T : ℕ) : ℤ) := by
      rw [pw_pw]
      congr 1
      push_cast
      ring
    rw [e₁]
    exact veryAmpleBy_pw A X.left X.hom (pw L N) m s hH hs (2 * T) (by omega)
  have A₂ : ∃ (k : ℕ) (a : Fin (k + 1) → LB.Sec (pw L ((2 * N * T + 1 : ℕ) : ℤ))),
      VeryAmpleBy X.hom (pw L ((2 * N * T + 1 : ℕ) : ℤ)) a := by
    have e₂ : ((2 * N * T + 1 : ℕ) : ℤ) = 1 + 2 * (N : ℤ) * (T : ℤ) := by
      push_cast
      ring
    rw [e₂]
    exact ⟨m', t', ht'⟩
  obtain ⟨k₁, a₁, h₁⟩ := A₁
  obtain ⟨k₂, a₂, h₂⟩ := A₂
  exact ⟨2 * N * T, Nat.mul_pos (Nat.mul_pos two_pos hN) hT, k₁, a₁, k₂, a₂, h₁, h₂⟩

end GlobalTheory.CompanionTheory.ConsecAmple
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatively_ample_consecutive_very_ample : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw L (d : ℤ))) (m' : ℕ) (s' : Fin (m' + 1) → LB.Sec (pw L ((d + 1 : ℕ) : ℤ))), VeryAmpleBy X.hom (pw L (d : ℤ)) s ∧ VeryAmpleBy X.hom (pw L ((d + 1 : ℕ) : ℤ)) s' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem mem_basicOpen_prod {X : Scheme.{0}} {U : X.Opens} {ι : Type} (s : Finset ι) (g : ι → Γ(X, U)) {y : X}
    (hy : y ∈ U) : y ∈ X.basicOpen (∏ l ∈ s, g l) ↔ ∀ l ∈ s, y ∈ X.basicOpen (g l) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Scheme.basicOpen_one, Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    exact hy
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Scheme.basicOpen_mul, Finset.forall_mem_insert, ← ih]
    rfl

theorem mem_nonzeroLocus_secMono {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D)
    (a : τ → LB.Sec (pw L d)) (w : Fin k → τ) (hk : 1 ≤ k) (y : X) :
    y ∈ nonzeroLocus (secMono h a w) ↔ ∀ l, y ∈ nonzeroLocus (a (w l)) := by
  constructor
  · intro hy l
    obtain ⟨c, hc⟩ := exists_chart_of_mem_nonzeroLocus hy
    have h1 := (mem_nonzeroLocus_iff_basicOpen (secMono h a w) hc).1 hy
    exact (mem_nonzeroLocus_iff_basicOpen (a (w l)) hc).2
      ((mem_basicOpen_prod Finset.univ (fun l => chartFn (a (w l)) c) hc).1 h1 l (Finset.mem_univ l))
  · intro hy
    obtain ⟨c, hc⟩ := exists_chart_of_mem_nonzeroLocus (hy ⟨0, hk⟩)
    refine (mem_nonzeroLocus_iff_basicOpen (secMono h a w) hc).2 ?_
    exact (mem_basicOpen_prod Finset.univ (fun l => chartFn (a (w l)) c) hc).2 fun l _ =>
      (mem_nonzeroLocus_iff_basicOpen (a (w l)) hc).1 (hy l)

theorem prod_update_eq_mul {B τ : Type} [CommMonoid B] {k : ℕ} (φ : τ → B) (w : Fin k → τ) (l : Fin k) (c : τ)
    (ρ : B) (h : φ c = ρ * φ (w l)) :
    ∏ l', φ (Function.update w l c l') = ρ * ∏ l', φ (w l') := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase Finset.univ (fun l' => φ (w l')) (Finset.mem_univ l), Function.update_self, h, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun l' hl' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl')]

theorem secRatio_secMono_update {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D)
    (a : τ → LB.Sec (pw L d)) (w : Fin k → τ) (l : Fin k) (c : τ)
    (hl : nonzeroLocus (secMono h a w) ≤ nonzeroLocus (a (w l))) :
    secRatio (secMono h a w) (secMono h a (Function.update w l c)) = resG X hl (secRatio (a (w l)) (a c)) := by
  refine (eq_secRatio _ _ fun κ => ?_).symm
  have key := secRatio_on (a (w l)) (a c) κ
    (W := nonzeroLocus (secMono h a w) ⊓ (pw L D).U κ) (inf_le_left.trans hl) inf_le_right
  have := prod_update_eq_mul (fun t => resG X (inf_le_right : nonzeroLocus (secMono h a w) ⊓ (pw L D).U κ ≤ L.U κ)
    (chartFn (a t) κ)) w l c _ key
  change resG X _ (∏ l', chartFn (a (Function.update w l c l')) κ) = _ * resG X _ (∏ l', chartFn (a (w l')) κ)
  rw [map_prod, map_prod, resG_resG]
  exact this

theorem mem_of_basicOpen {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (F : Γ(X, U))
    (hV : V = X.basicOpen F) (hle : V ≤ U) (S : Subring Γ(X, V)) (h1 : ∀ x, resG X hle x ∈ S)
    (g : Γ(X, V)) (hg : g ∈ S) (hgF : g * resG X hle F = 1) (z : Γ(X, V)) : z ∈ S := by
  subst hV
  have := hU.isLocalization_basicOpen F
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers F) z
  have hx' : z * resG X hle F ^ n = resG X hle x := by
    have e : ∀ t, algebraMap Γ(X, U) Γ(X, X.basicOpen F) t = resG X hle t := fun _ => rfl
    simpa only [e, map_pow] using hx
  have : z = resG X hle x * g ^ n := by
    rw [← hx', mul_assoc, ← mul_pow, mul_comm (resG X hle F), hgF, one_pow, mul_one]
  rw [this]
  exact S.mul_mem (h1 x) (S.pow_mem hg n)

theorem veryAmpleBy_secMono : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (d D : ℤ) (k : ℕ) (h : d * k = D) (p : ℕ) (a : Fin (p + 1) → LB.Sec (pw L d)), L.IsLB → 1 ≤ k → VeryAmpleBy f (pw L d) a → ∀ (m : ℕ) (e : Fin (m + 1) ≃ (Fin k → Fin (p + 1))), VeryAmpleBy f (pw L D) (fun j => secMono h a (e j)) := by
  intro R _ X f L d D k h p a hL hk hva m e
  obtain ⟨hcov, hch⟩ := hva
  refine ⟨?_, fun j => ?_⟩
  · refine top_unique ?_
    rw [← hcov]
    refine iSup_le fun i => ?_
    rw [← nonzeroLocus_secMono_const h a i hk]
    refine le_trans ?_ (le_iSup _ (e.symm fun _ => i))
    simp only [Equiv.apply_symm_apply, le_refl]
  · beta_reduce
    let w : Fin k → Fin (p + 1) := e j
    let l₀ : Fin k := ⟨0, hk⟩
    obtain ⟨hU, r, hr, hsurj⟩ := hch (w l₀)
    obtain rfl : r = fun t => secRatio (a (w l₀)) (a t) := funext fun t => eq_secRatio _ _ (hr t)
    have hN : ∀ l, nonzeroLocus (secMono h a w) ≤ nonzeroLocus (a (w l)) := fun l y hy =>
      (mem_nonzeroLocus_secMono h a w hk y).1 hy l
    have hV : nonzeroLocus (secMono h a w) = X.basicOpen (∏ l, secRatio (a (w l₀)) (a (w l))) := by
      ext y
      constructor
      · intro hy
        refine (mem_basicOpen_prod Finset.univ _ (hN l₀ hy)).2 fun l _ => ?_
        rw [basicOpen_secRatio]
        exact ⟨hN l₀ hy, hN l hy⟩
      · intro hy
        have hy₀ := X.basicOpen_le _ hy
        refine (mem_nonzeroLocus_secMono h a w hk y).2 fun l => ?_
        have := (mem_basicOpen_prod Finset.univ _ hy₀).1 hy l (Finset.mem_univ l)
        rw [basicOpen_secRatio] at this
        exact this.2
    refine ⟨hV ▸ hU.basicOpen _, fun t => secRatio (secMono h a w) (secMono h a (e t)),
      fun t κ => secRatio_spec _ _ κ, fun z => ?_⟩
    let S := (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (secMono h a w)))
      fun t => secRatio (secMono h a w) (secMono h a (e t))).range
    have hρ : ∀ v, secRatio (secMono h a w) (secMono h a v) ∈ S := fun v =>
      ⟨MvPolynomial.X (e.symm v), by simp⟩
    have hC : ∀ c : R, cst f (nonzeroLocus (secMono h a w)) c ∈ S := fun c =>
      ⟨MvPolynomial.C c, by simp⟩
    have h1 : ∀ x, resG X (hN l₀) x ∈ S := fun x => by
      obtain ⟨P, rfl⟩ := hsurj x
      induction P using MvPolynomial.induction_on with
      | C c =>
        rw [MvPolynomial.eval₂Hom_C]
        exact (rs_cst f (hN l₀) c).symm ▸ hC c
      | add P Q hP hQ =>
        rw [map_add, map_add]
        exact S.add_mem hP hQ
      | mul_X P t hP =>
        rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']
        refine S.mul_mem hP ?_
        rw [← secRatio_secMono_update h a w l₀ t (hN l₀)]
        exact hρ _
    obtain ⟨P, hP⟩ : z ∈ S := mem_of_basicOpen hU _ hV (hN l₀) S h1
      (∏ l, secRatio (secMono h a w) (secMono h a (Function.update w l (w l₀))))
      (S.prod_mem fun l _ => hρ _) (by
        rw [map_prod, ← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun l _ => ?_
        rw [secRatio_secMono_update h a w l (w l₀) (hN l), mul_comm,
          secRatio_mul_secRatio _ _ _ (hN l₀) (hN l), secRatio_self, map_one]) z
    exact ⟨P, hP⟩

end GlobalTheory.CompanionTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.very_ample_tensor_power_sections : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (d D : ℤ) (k : ℕ) (h : d * k = D) (p : ℕ) (a : Fin (p + 1) → LB.Sec (pw L d)), L.IsLB → 1 ≤ k → VeryAmpleBy f (pw L d) a → ∀ (m : ℕ) (e : Fin (m + 1) ≃ (Fin k → Fin (p + 1))), VeryAmpleBy f (pw L D) (fun j => secMono h a (e j)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

namespace GlobalTheory.CompanionTheory.VeryAmpleUnion

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def ChartBy (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (a : LB.Sec H) {m : ℕ}
    (s : Fin (m + 1) → LB.Sec H) : Prop :=
  IsAffineOpen (nonzeroLocus a) ∧
    ∃ r : Fin (m + 1) → Γ(X, nonzeroLocus a),
      (∀ j k, rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus a ⊓ H.U k ≤ nonzeroLocus a) (r j) *
          rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (a.f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus a)) r)

theorem ChartBy.of_sub {f : X ⟶ Spec (CommRingCat.of R)} {H : LB X} {a : LB.Sec H} {m n : ℕ}
    {w : Fin (n + 1) → LB.Sec H} {z : Fin (m + 1) → LB.Sec H} (ι : Fin (n + 1) → Fin (m + 1))
    (hι : ∀ l, z (ι l) = w l) (h : ChartBy f H a w) : ChartBy f H a z := by
  obtain ⟨ha, r, hr, hs⟩ := h
  refine ⟨ha, fun j => secRatio a (z j), fun j k => secRatio_spec a (z j) k, fun g => ?_⟩
  obtain ⟨p, rfl⟩ := hs g
  refine ⟨MvPolynomial.rename ι p, ?_⟩
  have hrr : (fun j => secRatio a (z j)) ∘ ι = r := by
    funext l
    refine (eq_secRatio a (z (ι l)) ?_).symm
    intro k
    rw [hι l]
    exact hr l k
  simp only [MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_rename, hrr]

theorem veryAmpleBy_union : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X), H.IsLB → ∀ (m₁ m₂ m : ℕ) (x : Fin (m₁ + 1) → LB.Sec H) (y : Fin (m₂ + 1) → LB.Sec H) (e : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1)), VeryAmpleBy f H x → VeryAmpleBy f H y → VeryAmpleBy f H (fun j => Sum.elim x y (e j)) := by
  intro R _ X f H _ m₁ m₂ m x y e hx hy
  have key : ∀ (z : Fin (m + 1) → LB.Sec H), (∀ j, z j = Sum.elim x y (e j)) →
      (⨆ j, nonzeroLocus (z j) = ⊤) ∧ ∀ j, ChartBy f H (z j) z := by
    intro z hz
    have hl : ∀ i, z (e.symm (Sum.inl i)) = x i := fun i => by simp [hz]
    have hr : ∀ i, z (e.symm (Sum.inr i)) = y i := fun i => by simp [hz]
    refine ⟨eq_top_iff.2 ?_, fun j => ?_⟩
    · rw [← hx.1]
      exact iSup_le fun i => le_iSup_of_le (e.symm (Sum.inl i)) (by rw [hl])
    · rcases he : e j with i | i
      · have hj : z j = x i := by rw [hz, he]; rfl
        rw [hj]
        exact ChartBy.of_sub (fun l => e.symm (Sum.inl l)) hl (hx.2 i)
      · have hj : z j = y i := by rw [hz, he]; rfl
        rw [hj]
        exact ChartBy.of_sub (fun l => e.symm (Sum.inr l)) hr (hy.2 i)
  exact key _ fun _ => rfl

end GlobalTheory.CompanionTheory.VeryAmpleUnion
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.very_ample_union_sections : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X), H.IsLB → ∀ (m₁ m₂ m : ℕ) (x : Fin (m₁ + 1) → LB.Sec H) (y : Fin (m₂ + 1) → LB.Sec H) (e : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1)), VeryAmpleBy f H x → VeryAmpleBy f H y → VeryAmpleBy f H (fun j => Sum.elim x y (e j)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem rel_of_secMaps {X X' : Scheme.{0}} {H : LB X} {H' : LB X'} {β : X' ⟶ X}
    {w : LB.Iso H' (H.pull β)} {s : H.Sec} {s' : H'.Sec} (h : SecMaps w s' (Cartier.secPull s β)) :
    GlobalTheory.Degen.FormalEmb.Rel β w s s' := by
  intro z k k' hk hk'
  have hm : z ∈ (H.pull β).U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have hm' : z ∈ (H.pull β).U (fun _ => k) := hm.1
  have e := congrArg (gs (𝟙 X') z _) (h ((fun _ => k), k'))
  have e1 : gs (𝟙 X') z _ (resG X' (inf_le_left : (H.pull β).U (fun _ => k) ⊓ H'.U k' ≤ _)
      ((Cartier.secPull s β).f (fun _ => k))) = gs β z _ (s.f k) := by
    refine (gs_res _ z _ hm _).trans ((gs_res _ z _ hm' _).trans ?_)
    rw [gs_pull (𝟙 X') β z _ hk, Category.id_comp]
  rw [e1] at e
  refine e.trans ?_
  rw [gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm]
  rfl

theorem veryAmpleBy_comp_spec {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : Function.Surjective g) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of B)) {H : LB X} {m : ℕ}
    {s : Fin (m + 1) → LB.Sec H} (h : VeryAmpleBy f H s) :
    VeryAmpleBy (f ≫ Spec.map (CommRingCat.ofHom g)) H s := by
  refine ⟨h.1, fun i => ?_⟩
  obtain ⟨ha, r, hr, hs⟩ := h.2 i
  refine ⟨ha, r, hr, fun p => ?_⟩
  obtain ⟨q, rfl⟩ := hs p
  obtain ⟨q', rfl⟩ := MvPolynomial.map_surjective g hg q
  refine ⟨q', ?_⟩
  rw [GlobalTheory.Degen.FormalEmb.cst_comp_spec, MvPolynomial.eval₂Hom_map_hom]

theorem isPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (P : Over (Spec (CommRingCat.of R))) (e : ℕ) :
    IsPullback (thickMap R I e P) (pullback.snd P.hom (thick R I e))
      (pullback.snd P.hom (thick R I (e + 1))) (thickTrans R I e) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback P.hom (thick R I (e + 1)))
  have h1 : thickMap R I e P ≫ pullback.fst P.hom (thick R I (e + 1)) = pullback.fst P.hom (thick R I e) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [h1, thickTrans_comp]
  exact IsPullback.of_hasPullback _ _

theorem exists_iso_of_chart {Y : Scheme.{0}} {A L : LB Y} {τ : Type} (t : τ → A.Sec) (s : τ → L.Sec)
    (c : A.ι → τ) (h1 : ∀ a, (t (c a)).f a = 1) (h2 : ∀ a, A.U a ≤ nonzeroLocus (s (c a)))
    (h3 : ∀ a k j, resG Y (inf_le_left : L.U k ⊓ A.U a ≤ L.U k) ((s j).f k) =
      resG Y inf_le_left ((s (c a)).f k) * resG Y inf_le_right ((t j).f a)) :
    ∃ w : LB.Iso A L, w.IsGen ∧ ∀ j, SecMaps w (t j) (s j) := by
  let w : LB.Iso A L := ⟨fun p => (isUnit_resG_sec (s (c p.2)) p.1 (inf_le_right.trans (h2 p.2)) inf_le_left).unit⟩
  refine ⟨w, ?_, fun j => ?_⟩
  · rintro ⟨p, q⟩ ⟨p', q'⟩
    have hp : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ L.U p := inf_le_left.trans inf_le_left
    have hq : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
    have hp' : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ L.U p' := inf_le_right.trans inf_le_left
    have hq' : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
    have key : res (le_inf hp hq) (@id (Γ(Y, L.U p ⊓ A.U q)ˣ) (w.s (p, q))) *
        res (le_inf hq hq') (A.g q q') = res (le_inf hp hp') (L.g p p') *
          res (le_inf hp' hq') (@id (Γ(Y, L.U p' ⊓ A.U q')ˣ) (w.s (p', q'))) := by
      refine Units.ext ?_
      change resG Y (le_inf hp hq) (resG Y inf_le_left ((s (c q)).f p)) * resG Y (le_inf hq hq') (A.g q q').val =
        resG Y (le_inf hp hp') (L.g p p').val * resG Y (le_inf hp' hq') (resG Y inf_le_left ((s (c q')).f p'))
      rw [resG_resG, resG_resG, ← sec_compat _ p p' hp hp']
      have e1 := congrArg (resG Y (le_inf hp hq)) (h3 q p (c q'))
      rw [map_mul, resG_resG, resG_resG, resG_resG] at e1
      have e2 := sec_compat (t (c q')) q q' hq hq'
      rw [h1 q', map_one, mul_one] at e2
      rw [e1, e2]
    change res (le_inf hp hq) (@id (Γ(Y, L.U p ⊓ A.U q)ˣ) (w.s (p, q))) =
      res (le_inf hp hp') (L.g p p') * (res (le_inf hq hq') (A.g q q'))⁻¹ *
        res (le_inf hp' hq') (@id (Γ(Y, L.U p' ⊓ A.U q')ˣ) (w.s (p', q')))
    rw [mul_right_comm, ← key, mul_inv_cancel_right]
  · rintro ⟨k, a⟩
    exact h3 a k j

theorem secQuad_of_secMaps {X : Scheme.{0}} {A B : LB X} (hB : B.IsLB) (w : LB.Iso A B) {a₁ a₂ a₃ a₄ : A.Sec}
    {b₁ b₂ b₃ b₄ : B.Sec} (h₁ : SecMaps w a₁ b₁) (h₂ : SecMaps w a₂ b₂) (h₃ : SecMaps w a₃ b₃)
    (h₄ : SecMaps w a₄ b₄) (h : ∀ c, b₁.f c * b₂.f c = b₃.f c * b₄.f c) (c : A.ι) :
    a₁.f c * a₂.f c = a₃.f c * a₄.f c := by
  refine ext_germ fun x hx => ?_
  obtain ⟨p, hp⟩ := LB.mem_of_cover hB x
  have hm : x ∈ B.U p ⊓ A.U c := ⟨hp, hx⟩
  have g := fun (b : B.Sec) (a : A.Sec) (hh : SecMaps w a b) => by
    have := congrArg (X.presheaf.germ (B.U p ⊓ A.U c) x hm).hom (hh (p, c))
    rwa [map_mul, germ_resG, germ_resG] at this
  have e := congrArg (X.presheaf.germ (B.U p) x hp).hom (h p)
  rw [map_mul, map_mul, g _ _ h₁, g _ _ h₂, g _ _ h₃, g _ _ h₄] at e
  have u : IsUnit ((X.presheaf.germ (B.U p ⊓ A.U c) x hm).hom
      ((@id (Γ(X, B.U p ⊓ A.U c)ˣ) (w.s (p, c)) : Γ(X, B.U p ⊓ A.U c)))) := (Units.isUnit _).map _
  rw [map_mul, map_mul]
  have e' : ((X.presheaf.germ (B.U p ⊓ A.U c) x hm).hom
      ((@id (Γ(X, B.U p ⊓ A.U c)ˣ) (w.s (p, c)) : Γ(X, B.U p ⊓ A.U c)))) ^ 2 *
      ((X.presheaf.germ _ x hx).hom (a₁.f c) * (X.presheaf.germ _ x hx).hom (a₂.f c)) =
      ((X.presheaf.germ (B.U p ⊓ A.U c) x hm).hom
      ((@id (Γ(X, B.U p ⊓ A.U c)ˣ) (w.s (p, c)) : Γ(X, B.U p ⊓ A.U c)))) ^ 2 *
      ((X.presheaf.germ _ x hx).hom (a₃.f c) * (X.presheaf.germ _ x hx).hom (a₄.f c)) := by
    linear_combination e
  exact (u.pow 2).mul_left_cancel e'

theorem resG_app_resG_app {Y C D : Scheme.{0}} (b : Y ⟶ C) (j : C ⟶ D) {U : D.Opens} {V : C.Opens}
    (hV : V ≤ j ⁻¹ᵁ U) {W' : Y.Opens} (hW' : W' ≤ b ⁻¹ᵁ V) {W : Y.Opens} (hW : W ≤ W')
    (hh : W ≤ (b ≫ j) ⁻¹ᵁ U) (x : Γ(D, U)) :
    resG Y hW (resG Y hW' ((b.app V).hom (resG C hV ((j.app U).hom x)))) = ((b ≫ j).appLE U W hh).hom x := by
  rw [app_resG, resG_resG, resG_resG, Scheme.Hom.comp_appLE]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]

theorem resG_secPull_secPull_coord {R : Type} [CommRing R] {M : ℕ} {Y C : Scheme.{0}} (j : C ⟶ PSpace R M)
    (b : Y ⟶ C) (l : Fin (M + 1)) (a : PUnit → PUnit → Fin (M + 1)) {W : Y.Opens}
    (h : W ≤ (((O1 R M).pull j).pull b).U a) (h' : W ≤ (b ≫ j) ⁻¹ᵁ chart R M (a ⟨⟩ ⟨⟩)) :
    resG Y h ((Cartier.secPull (Cartier.secPull (coord R M l) j) b).f a) =
      pullRatio (b ≫ j) W (a ⟨⟩ ⟨⟩) h' l :=
  resG_app_resG_app b j _ _ h h' _

theorem exists_iso_pull_pull {R : Type} [CommRing R] {M : ℕ} {Y C : Scheme.{0}} {L : LB Y}
    (f : Y ⟶ Spec (CommRingCat.of R)) (s : Fin (M + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (j : C ⟶ PSpace R M) (b : Y ⟶ C) (h : b ≫ j = toProj f s hs) :
    ∃ w : LB.Iso (((O1 R M).pull j).pull b) L, w.IsGen ∧
      ∀ l, SecMaps w (Cartier.secPull (Cartier.secPull (coord R M l) j) b) (s l) := by
  have hU : ∀ a : PUnit → PUnit → Fin (M + 1),
      (((O1 R M).pull j).pull b).U a ≤ (b ≫ j) ⁻¹ᵁ chart R M (a ⟨⟩ ⟨⟩) := fun a y hy => by
    have h1 := mem_pull.1 hy
    exact mem_pull.1 h1
  have hc : ∀ i, (b ≫ j) ⁻¹ᵁ chart R M i = nonzeroLocus (s i) := fun i => by
    rw [h, toProj_preimage_chart]
  have hsec : ∀ (i l : Fin (M + 1)) (k : L.ι) {W : Y.Opens} (hW : W ≤ (b ≫ j) ⁻¹ᵁ chart R M i)
      (hk : W ≤ L.U k), resG Y hk ((s l).f k) = pullRatio (b ≫ j) W i hW l * resG Y hk ((s i).f k) := by
    intro i l k W hW hk
    revert hW
    rw [h]
    intro hW
    exact sec_eq_pullRatio_toProj_mul f s hs i l k hW hk
  refine exists_iso_of_chart (A := ((O1 R M).pull j).pull b) _ s (fun a => a ⟨⟩ ⟨⟩) (fun a => ?_) (fun a => ?_) (fun a k l => ?_)
  · exact (resG_self _ _).symm.trans ((resG_secPull_secPull_coord j b _ a le_rfl (hU a)).trans pullRatio_self)
  · exact (hU a).trans (hc _).le
  · have hW : L.U k ⊓ (((O1 R M).pull j).pull b).U a ≤ (b ≫ j) ⁻¹ᵁ chart R M (a ⟨⟩ ⟨⟩) :=
      inf_le_right.trans (hU a)
    exact (hsec _ l k hW inf_le_left).trans ((mul_comm _ _).trans
      (congrArg _ (resG_secPull_secPull_coord j b l a inf_le_right hW).symm))

theorem toProj_comp_of_secMaps {R : Type} [CommRing R] {M : ℕ} {Y Z : Scheme.{0}} {L : LB Y} {B : LB Z}
    (g : Z ⟶ Y) (f : Y ⟶ Spec (CommRingCat.of R)) (f' : Z ⟶ Spec (CommRingCat.of R)) (hf : g ≫ f = f')
    (s : Fin (M + 1) → L.Sec) (t : Fin (M + 1) → B.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) (w : LB.Iso B (L.pull g))
    (h : ∀ l, SecMaps w (t l) (Cartier.secPull (s l) g)) : g ≫ toProj f s hs = toProj f' t ht := by
  subst hf
  rw [← toProj_secPull hs g]
  exact toProj_eq_of_secMaps ht _ h

theorem isHomogeneous_quadric {R : Type} [CommRing R] {σ : Type} (a b c d : σ) :
    (MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d :
      MvPolynomial σ R).IsHomogeneous 2 :=
  ((MvPolynomial.isHomogeneous_X R a).mul (MvPolynomial.isHomogeneous_X R b)).sub
    ((MvPolynomial.isHomogeneous_X R c).mul (MvPolynomial.isHomogeneous_X R d))

theorem quadric_app_iff {R : Type} [CommRing R] {M : ℕ} {T : Scheme.{0}} (φ : T ⟶ PSpace R M)
    (a b c d : Fin (M + 1)) :
    (∀ k : PUnit → Fin (M + 1), (Cartier.secPull (coord R M a) φ).f k * (Cartier.secPull (coord R M b) φ).f k =
        (Cartier.secPull (coord R M c) φ).f k * (Cartier.secPull (coord R M d) φ).f k) ↔
      ∀ i, (φ.app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i)
        (MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d :
          MvPolynomial (Fin (M + 1)) R)) = 0 := by
  have key := fun k : PUnit → Fin (M + 1) =>
    (show MvPolynomial.eval₂Hom (cst (φ ≫ PSpace.str R M) (((O1 R M).pull φ).U k))
        (fun j => (Cartier.secPull (coord R M j) φ).f k)
        (MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d) = _ by
      simp only [map_sub, map_mul, MvPolynomial.eval₂Hom_X']; rfl).symm.trans
    (GlobalTheory.ProjQuot.eval₂Hom_secPull_coord φ k
      (MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d))
  constructor
  · intro h i
    have e := (key (fun _ => i)).symm.trans (sub_eq_zero.2 (h _))
    have h' := congrArg (resG _ (Cartier.pull_U (O1 R M) φ (fun _ => i)).ge) e
    exact ((resG_resG _ _ _).trans (resG_self _ _)).symm.trans (h'.trans (map_zero _))
  · intro h k
    refine sub_eq_zero.1 ((key k).trans ((congrArg _ (h _)).trans (map_zero _)))

theorem quadricIdeal_le_ker {R : Type} [CommRing R] {M : ℕ} {T : Scheme.{0}} (ψ : T ⟶ PSpace R M)
    [QuasiCompact ψ] (F : MvPolynomial (Fin (M + 1)) R) (hF : F.IsHomogeneous 2)
    (h : ∀ i, (ψ.app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i) F) = 0) :
    GlobalTheory.ThickeningDetermines.secIdeal (On_isLB R M (2 : ℕ)) (formSec 2 F hF) ≤ ψ.ker := by
  rw [← sup_eq_right]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i => ⟨chart R M i, isAffineOpen_chart R M i⟩) ?_ fun i => ?_
  · exact top_unique fun y _ => (exists_mem_chart R M y).elim fun i hi => TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  · rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, GlobalTheory.ProjQuot.ideal_secIdeal_formSec, sup_eq_right,
      Scheme.Hom.ker_apply, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    exact h i

theorem app_eq_zero_of_fac {A B C : Scheme.{0}} (q : A ⟶ B) (ι : B ⟶ C) (j : A ⟶ C) (h : q ≫ ι = j)
    (U : C.Opens) (x : Γ(C, U)) (hx : (ι.app U).hom x = 0) : (j.app U).hom x = 0 := by
  subst h
  rw [Scheme.Hom.comp_app]
  change (q.app _).hom ((ι.app U).hom x) = 0
  rw [hx, map_zero]

theorem app_eq_zero_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (hc : IsAdicComplete I R) (X : Over (Spec (CommRingCat.of R))) (hX : IsProper X.hom) {M : ℕ}
    (j : X.left ⟶ PSpace R M) (T : ℕ → Scheme.{0}) (b : ∀ e, T e ⟶ X.left)
    (p : ∀ e, T e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (hb : ∀ e, IsPullback (b e) (p e) X.hom (thick R I e)) (hq : ∀ e, QuasiCompact (b e ≫ j))
    [IsClosedImmersion j]
    (F : MvPolynomial (Fin (M + 1)) R) (hF : F.IsHomogeneous 2)
    (h : ∀ e i, ((b e ≫ j).app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i) F) = 0) (i : Fin (M + 1)) :
    (j.app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i) F) = 0 := by
  let K := GlobalTheory.ThickeningDetermines.secIdeal (On_isLB R M (2 : ℕ)) (formSec 2 F hF)
  have hle : ∀ e, Scheme.Hom.ker K.subschemeι ≤ Scheme.Hom.ker (b e ≫ j) := fun e => by
    rw [K.ker_subschemeι]
    have := hq e
    exact quadricIdeal_le_ker _ F hF (h e)
  have hl : ∀ e, IsClosedImmersion.lift K.subschemeι (b e ≫ j) (hle e) ≫ K.subschemeι = b e ≫ j :=
    fun e => IsClosedImmersion.lift_fac _ _ _
  have hiso : IsIso (pullback.fst j K.subschemeι) :=
    GlobalTheory.CompanionTheory.FormalClosed.isIso_of_isClosedImmersion_of_thickenings R I hc X hX _ _ inferInstance fun e =>
      ⟨(hb e).isoPullback.inv ≫ pullback.lift (b e) _ (hl e).symm, by
        rw [Category.assoc, pullback.lift_fst]
        exact (hb e).isoPullback_inv_fst⟩
  have hfac : (inv (pullback.fst j K.subschemeι) ≫ pullback.snd j K.subschemeι) ≫ K.subschemeι = j := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have hK : (K.subschemeι.app (chart R M i)).hom (MvPolynomial.aeval (ratio R M i) F) = 0 := by
    have m : MvPolynomial.aeval (ratio R M i) F ∈ K.ideal ⟨chart R M i, isAffineOpen_chart R M i⟩ :=
      (GlobalTheory.ProjQuot.ideal_secIdeal_formSec i 2 F hF).ge (Ideal.mem_span_singleton_self _)
    rw [← K.ker_subschemeι_app] at m
    exact RingHom.mem_ker.1 m
  exact app_eq_zero_of_fac _ _ _ hfac _ _ hK

theorem exists_tower_algebraisation : GEClosedProj → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (E : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (E e) ((E (e + 1)).pull (β e))), (∀ e, (E e).IsLB ∧ (w e).IsGen) → ∀ (m : ℕ) (z : ∀ e, Fin (m + 1) → LB.Sec (E e)), (∀ e j, SecMaps (w e) (z e j) (Cartier.secPull (z (e + 1) j) (β e))) → VeryAmpleBy (Y 0).hom (E 0) (z 0) → ∃ (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (ζ : Fin (m + 1) → LB.Sec Q) (b : ∀ e, (Y e).left ⟶ X.left) (ω : ∀ e, LB.Iso (Q.pull (b e)) (E e)), Q.IsLB ∧ IsProper X.hom ∧ VeryAmpleBy X.hom Q ζ ∧ (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (ω e).IsGen) ∧ (∀ e j, SecMaps (ω e) (Cartier.secPull (ζ j) (b e)) (z e j)) ∧ (∀ i₁ i₂ i₃ i₄, (∀ e (c : (E e).ι), (z e i₁).f c * (z e i₂).f c = (z e i₃).f c * (z e i₄).f c) → ∀ c : Q.ι, (ζ i₁).f c * (ζ i₂).f c = (ζ i₃).f c * (ζ i₄).f c) ∧ (∀ S : Set (Fin (m + 1)), (⨆ i ∈ S, nonzeroLocus (z 0 i) = ⊤) → ⨆ i ∈ S, nonzeroLocus (ζ i) = ⊤) := by
  intro hge R _ _ I hc Y β hβ E w hE m z hz hva
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (E e) (z e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w', hw, hr⟩ := GlobalTheory.Degen.FormalEmb.tower I Y β hβ E w hE z
        (fun e j => rel_of_secMaps (hz e j)) e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _) _ _ _ _ j₀ hj _ _ w' m _ _ (hE _).1 (hE _).1
        ((isGen_iff _).2 hw) hr hva
  let π : ∀ e, (Y e).left ⟶ Spec (CommRingCat.of R) := fun e => (Y e).hom ≫ thick R I e
  have hVR : ∀ e, VeryAmpleBy (π e) (E e) (z e) := fun e =>
    veryAmpleBy_comp_spec _ Ideal.Quotient.mk_surjective _ (hVA e)
  have hs : ∀ e, ⨆ i, nonzeroLocus (z e i) = ⊤ := fun e => (hVA e).1
  let φ : ∀ e, (Y e).left ⟶ PSpace R m := fun e => toProj (π e) (z e) (hs e)
  have hφc : ∀ e, IsClosedImmersion (φ e) := fun e => ((veryAmpleBy_iff _ _).1 (hVR e)).2
  have hφs : ∀ e, φ e ≫ PSpace.str R m = π e := fun e => toProj_str _ _ _
  have hπ : ∀ e, β e ≫ π (e + 1) = π e := fun e => by
    simp only [π]
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hφβ : ∀ e, β e ≫ φ (e + 1) = φ e := fun e =>
    toProj_comp_of_secMaps (β e) (π (e + 1)) (π e) (hπ e) _ _ _ _ (w e) (hz e)
  let P : Over (Spec (CommRingCat.of R)) := Over.mk (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R m)
  let i : ∀ e, (Y e).left ⟶ (thickObj R I e P).left := fun e =>
    pullback.lift (f := P.hom) (g := thick R I e) (φ e) (Y e).hom (hφs e)
  have hifst : ∀ e, i e ≫ pullback.fst P.hom (thick R I e) = φ e := fun e => pullback.lift_fst _ _ _
  have hisnd : ∀ e, i e ≫ pullback.snd P.hom (thick R I e) = (Y e).hom := fun e => pullback.lift_snd _ _ _
  have hic : ∀ e, IsClosedImmersion (i e) := fun e => by
    have : IsClosedImmersion (i e ≫ pullback.fst P.hom (thick R I e)) := by
      rw [hifst]; exact hφc e
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick R I e))
  have hipb : ∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P) := fun e => by
    refine IsPullback.of_bot ?_ ?_ (isPullback_thickMap I P e)
    · rw [hisnd, hisnd]; exact hβ e
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hifst]
        exact (hφβ e).trans ((hifst e).symm.trans (congrArg (i e ≫ ·)
          ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm))
      · rw [Category.assoc, Category.assoc, hisnd]
        exact (hβ e).w.trans ((congrArg (· ≫ _) (hisnd e).symm).trans ((Category.assoc _ _ _).trans
          (congrArg (i e ≫ ·) (pullback.lift_snd _ _ _).symm)))
  obtain ⟨C', j, b, hj, hb, hbc⟩ := hge R I hc m (fun e => (Y e).left) i β hic hipb
  let j' : C' ⟶ PSpace R m := j
  have hj' : IsClosedImmersion j' := hj
  have hbφ : ∀ e, b e ≫ j' = φ e := fun e => (hb e).w.trans (hifst e)
  let X : Over (Spec (CommRingCat.of R)) := Over.mk (j' ≫ PSpace.str R m)
  have hX : IsProper X.hom := by
    have := isProper_str R m
    change IsProper (j' ≫ PSpace.str R m)
    infer_instance
  choose ω hωg hωs using fun e => exists_iso_pull_pull (π e) (z e) (hs e) j' (b e) (hbφ e)
  have hpb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e) := fun e => by
    have h := (hb e).paste_vert (IsPullback.of_hasPullback P.hom (thick R I e))
    rw [hisnd] at h
    exact h
  have hQ : ((O1 R m).pull j').IsLB := LB.isLB_pull (O1_isLB R m) j'
  refine ⟨X, (O1 R m).pull j', fun l => Cartier.secPull (coord R m l) j', b, ω, hQ, hX,
    veryAmpleBy_secPull_coord j', hpb, hbc, hωg, hωs, ?_, ?_⟩
  · intro a₁ a₂ a₃ a₄ H c
    have hq : ∀ e i₀, ((b e ≫ j').app (chart R m i₀)).hom (MvPolynomial.aeval (ratio R m i₀)
        (MvPolynomial.X a₁ * MvPolynomial.X a₂ - MvPolynomial.X a₃ * MvPolynomial.X a₄ :
          MvPolynomial (Fin (m + 1)) R)) = 0 := fun e => by
      rw [hbφ e]
      exact (quadric_app_iff (φ e) a₁ a₂ a₃ a₄).1 fun k =>
        secQuad_of_secMaps (hE e).1 (toProjIso (π e) (z e) (hs e)) (secMaps_toProjIso _ _ _ a₁)
          (secMaps_toProjIso _ _ _ a₂) (secMaps_toProjIso _ _ _ a₃) (secMaps_toProjIso _ _ _ a₄) (H e) k
    exact (quadric_app_iff j' a₁ a₂ a₃ a₄).2 (fun i₀ => app_eq_zero_of_thickenings I hc X hX j'
      (fun e => (Y e).left) b (fun e => (Y e).hom) hpb
      (fun e => by rw [hbφ e]; have := hφc e; infer_instance) _ (isHomogeneous_quadric _ _ _ _) hq i₀) c
  · intro S hS
    have : UniversallyClosed X.hom := inferInstance
    refine top_unique fun x _ => ?_
    refine GlobalTheory.CompanionTheory.FormalClosed.mem_of_forall_mem_over_closedFibre (IsAdicComplete.le_jacobson_bot I) X.hom
      (W := ((⨆ i ∈ S, nonzeroLocus (Cartier.secPull (coord R m i) j') : X.left.Opens) : Set X.left))
      (TopologicalSpace.Opens.isOpen _) (fun x hx => ?_) x
    have hx' : X.hom x ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk (I ^ (0 + 1))) : Set R) :=
      fun a ha => hx (by simpa [Ideal.Quotient.eq_zero_iff_mem] using ha)
    rw [← range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective] at hx'
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, thick R I 0 y₀ = X.hom x := hx'
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback x y₀ hy₀.symm
    have hy : b 0 ((hpb 0).isoPullback.inv t) = x := by
      rw [← ht, ← (hpb 0).isoPullback_inv_fst]
      rfl
    have hm : (hpb 0).isoPullback.inv t ∈ ⨆ i ∈ S, nonzeroLocus (z 0 i) := by rw [hS]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hm
    obtain ⟨i₀, hi, hm⟩ := hm
    have e₁ := (hωs 0 i₀).nonzeroLocus_eq (LB.isLB_pull hQ _) (hE 0).1
    rw [Cartier.nonzeroLocus_secPull] at e₁
    rw [← e₁] at hm
    have hm' : b 0 ((hpb 0).isoPullback.inv t) ∈ nonzeroLocus (Cartier.secPull (coord R m i₀) j') := hm
    rw [hy] at hm'
    change x ∈ (⨆ i ∈ S, nonzeroLocus (Cartier.secPull (coord R m i) j') : X.left.Opens)
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨i₀, hi, hm'⟩

end GlobalTheory.CompanionTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_sections_compatible_system : GEClosedProj → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (E : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (E e) ((E (e + 1)).pull (β e))), (∀ e, (E e).IsLB ∧ (w e).IsGen) → ∀ (m : ℕ) (z : ∀ e, Fin (m + 1) → LB.Sec (E e)), (∀ e j, SecMaps (w e) (z e j) (secPull (z (e + 1) j) (β e))) → VeryAmpleBy (Y 0).hom (E 0) (z 0) → ∃ (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (ζ : Fin (m + 1) → LB.Sec Q) (b : ∀ e, (Y e).left ⟶ X.left) (ω : ∀ e, LB.Iso (Q.pull (b e)) (E e)), Q.IsLB ∧ IsProper X.hom ∧ VeryAmpleBy X.hom Q ζ ∧ (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (ω e).IsGen) ∧ (∀ e j, SecMaps (ω e) (secPull (ζ j) (b e)) (z e j)) ∧ (∀ i₁ i₂ i₃ i₄, (∀ e (c : (E e).ι), (z e i₁).f c * (z e i₂).f c = (z e i₃).f c * (z e i₄).f c) → ∀ c : Q.ι, (ζ i₁).f c * (ζ i₂).f c = (ζ i₃).f c * (ζ i₄).f c) ∧ (∀ S : Set (Fin (m + 1)), (⨆ i ∈ S, nonzeroLocus (z 0 i) = ⊤) → ⨆ i ∈ S, nonzeroLocus (ζ i) = ⊤) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.exists_tower_algebraisation
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

abbrev wordSet {k : ℕ} {τ : Type} (w : Fin k → τ) : Multiset τ := Finset.univ.val.map w

theorem wordSet_update_add {k : ℕ} {τ : Type} (f : Fin k → τ) (l : Fin k) (a : τ) :
    wordSet (Function.update f l a) + {f l} = wordSet f + {a} := by
  have key : ∀ g : Fin k → τ, wordSet g = g l ::ₘ ((Finset.univ.erase l).val.map g) := by
    intro g
    rw [← Multiset.map_cons, Finset.erase_val, Multiset.cons_erase (Finset.mem_univ_val l)]
  have e : (Finset.univ.erase l).val.map (Function.update f l a) = (Finset.univ.erase l).val.map f :=
    Multiset.map_congr rfl fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase (show x ∈ Finset.univ.erase l from hx)) _ _
  rw [key, key f, Function.update_self, e, ← Multiset.singleton_add, ← Multiset.singleton_add (f l)]
  abel

theorem wordSet_update_rel {k : ℕ} {τ : Type} (f g : Fin k → τ) (l l' : Fin k) (a : τ) (h : f l = g l') :
    wordSet f + wordSet (Function.update g l' a) = wordSet (Function.update f l a) + wordSet g := by
  refine add_right_cancel (b := ({f l} : Multiset τ)) ?_
  have e₁ := wordSet_update_add f l a
  have e₂ := wordSet_update_add g l' a
  rw [← h] at e₂
  calc wordSet f + wordSet (Function.update g l' a) + {f l}
      = wordSet f + (wordSet (Function.update g l' a) + {f l}) := by abel
    _ = wordSet f + (wordSet g + {a}) := by rw [e₂]
    _ = (wordSet f + {a}) + wordSet g := by abel
    _ = (wordSet (Function.update f l a) + {f l}) + wordSet g := by rw [e₁]
    _ = _ := by abel

section Ring

variable {B τ : Type} [CommRing B] {k : ℕ} {x : (Fin k → τ) → B}

theorem mul_word_update
    (hrel : ∀ w₁ w₂ w₃ w₄ : Fin k → τ, wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄ →
      x w₁ * x w₂ = x w₃ * x w₄)
    {i j : τ} {l₀ : Fin k} {r : B} (hu : IsUnit (x fun _ => i))
    (hr : r * x (fun _ => i) = x (Function.update (fun _ => i) l₀ j))
    (w : Fin k → τ) (l : Fin k) (hw : w l = i) : r * x w = x (Function.update w l j) := by
  refine hu.mul_right_cancel ?_
  have := hrel _ _ _ _ (wordSet_update_rel w (fun _ => i) l l₀ j hw)
  rw [← hr] at this
  rw [← this]
  ring

theorem pow_mul_word_const
    (hrel : ∀ w₁ w₂ w₃ w₄ : Fin k → τ, wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄ →
      x w₁ * x w₂ = x w₃ * x w₄)
    {i j : τ} {l₀ : Fin k} {r : B} (hu : IsUnit (x fun _ => i))
    (hr : r * x (fun _ => i) = x (Function.update (fun _ => i) l₀ j)) :
    r ^ k * x (fun _ => i) = x fun _ => j := by
  have key : ∀ n, n ≤ k → r ^ n * x (fun _ => i) = x (fun l => if l.val < n then j else i) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hlt : n < k := hn
      have := mul_word_update hrel hu hr (fun l => if l.val < n then j else i) ⟨n, hlt⟩ (by simp)
      rw [pow_succ', mul_assoc, ih hlt.le, this]
      congr 1
      funext l
      by_cases h : l = ⟨n, hlt⟩
      · subst h; simp
      · have : l.val ≠ n := fun e => h (Fin.ext e)
        rw [Function.update_of_ne h]
        by_cases h' : l.val < n
        · simp [h', Nat.lt_succ_of_lt h']
        · have : ¬ l.val < n + 1 := by omega
          simp [h', this]
  rw [key k le_rfl]
  congr 1
  funext l
  simp

end Ring

theorem prod_update_mul {M τ : Type} [CommMonoid M] {k : ℕ} (φ : τ → M) (f : Fin k → τ) (l : Fin k) (a : τ) :
    (∏ m, φ (Function.update f l a m)) * φ (f l) = (∏ m, φ (f m)) * φ a := by
  have key : ∀ w : Fin k → τ, ∏ l, φ (w l) = ((wordSet w).map φ).prod := by
    intro w
    rw [Multiset.map_map]
    rfl
  have := congrArg (fun s => (s.map φ).prod) (wordSet_update_add f l a)
  simpa [Multiset.map_add, Multiset.prod_add, key] using this

section Root

variable {X : Scheme.{0}} {Q : LB X} {k : ℕ} (hk : 1 ≤ k) {τ : Type} (u : (Fin k → τ) → LB.Sec Q)

def oneLetter (i j : τ) : Fin k → τ := Function.update (fun _ => i) ⟨0, hk⟩ j

def VeroneseRel : Prop :=
  ∀ w₁ w₂ w₃ w₄ : Fin k → τ, wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄ →
    ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c

def rootChart (i : τ) : X.Opens := nonzeroLocus (u fun _ => i)

def rootRatio (i j : τ) : Γ(X, rootChart u i) := secRatio (u fun _ => i) (u (oneLetter hk i j))

variable {u}

theorem VeroneseRel.resG (h : VeroneseRel u) {W : X.Opens} {c : Q.ι} (hc : W ≤ Q.U c)
    (w₁ w₂ w₃ w₄ : Fin k → τ) (hw : wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₁).f c) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₂).f c) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₃).f c) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₄).f c) := by
  rw [← map_mul, ← map_mul, h _ _ _ _ hw c]

variable (u)

theorem rootRatio_chart {W : X.Opens} {i : τ} (j : τ) {c : Q.ι} (hi : W ≤ rootChart u i) (hc : W ≤ Q.U c) :
    resG X hi (rootRatio hk u i j) * resG X hc ((u fun _ => i).f c) =
      resG X hc ((u (oneLetter hk i j)).f c) :=
  (secRatio_on _ _ c hi hc).symm

theorem rootRatio_self (i : τ) : rootRatio hk u i i = 1 := by
  have : oneLetter hk i i = fun _ => i := Function.update_eq_self (⟨0, hk⟩ : Fin k) (fun _ : Fin k => i)
  rw [rootRatio, this]
  exact secRatio_self _

variable {u}

theorem rootRatio_mul (h : VeroneseRel u) {W : X.Opens} {i j : τ} (l : τ) (hi : W ≤ rootChart u i)
    (hj : W ≤ rootChart u j) :
    resG X hi (rootRatio hk u i j) * resG X hj (rootRatio hk u j l) = resG X hi (rootRatio hk u i l) := by
  refine ext_charts (u fun _ => i) hi fun c => ?_
  have hc : W ⊓ Q.U c ≤ Q.U c := inf_le_right
  have hi' : W ⊓ Q.U c ≤ rootChart u i := inf_le_left.trans hi
  have hj' : W ⊓ Q.U c ≤ rootChart u j := inf_le_left.trans hj
  have ui : IsUnit (resG X hc ((u fun _ => i).f c)) := isUnit_resG_sec _ c hi' hc
  have uj : IsUnit (resG X hc ((u fun _ => j).f c)) := isUnit_resG_sec _ c hj' hc
  refine ui.mul_right_cancel ?_
  rw [map_mul, resG_resG, resG_resG, resG_resG]
  have e3 := mul_word_update (x := fun w => resG X hc ((u w).f c)) (h.resG hc) (i := j) (j := l)
    (l₀ := ⟨0, hk⟩) uj (rootRatio_chart hk u l hj' hc) (oneLetter hk i j) ⟨0, hk⟩
    (by simp [oneLetter])
  have e4 : Function.update (oneLetter hk i j) ⟨0, hk⟩ l = oneLetter hk i l :=
    Function.update_idem _ _ _
  rw [e4] at e3
  rw [rootRatio_chart hk u l hi' hc, mul_right_comm, rootRatio_chart hk u j hi' hc, mul_comm]
  exact e3

theorem rootRatio_pow (h : VeroneseRel u) {W : X.Opens} {i : τ} (j : τ) {c : Q.ι}
    (hi : W ≤ rootChart u i) (hc : W ≤ Q.U c) :
    resG X hi (rootRatio hk u i j) ^ k * resG X hc ((u fun _ => i).f c) =
      resG X hc ((u fun _ => j).f c) :=
  pow_mul_word_const (x := fun w => resG X hc ((u w).f c)) (h.resG hc) (l₀ := ⟨0, hk⟩)
    (isUnit_resG_sec _ c hi hc) (rootRatio_chart hk u j hi hc)

def rootG (h : VeroneseRel u) (i j : τ) : Γ(X, rootChart u i ⊓ rootChart u j)ˣ where
  val := resG X inf_le_left (rootRatio hk u i j)
  inv := resG X inf_le_right (rootRatio hk u j i)
  val_inv := by
    rw [rootRatio_mul hk h i inf_le_left inf_le_right, rootRatio_self, map_one]
  inv_val := by
    rw [rootRatio_mul hk h j inf_le_right inf_le_left, rootRatio_self, map_one]

def rootLB (h : VeroneseRel u) : LB X := ⟨τ, rootChart u, rootG hk h⟩

theorem rootG_self (h : VeroneseRel u) (i : τ) :
    res (le_inf le_rfl le_rfl : rootChart u i ≤ rootChart u i ⊓ rootChart u i) (rootG hk h i i) = 1 :=
  Units.ext (by
    change resG X _ (resG X _ (rootRatio hk u i i)) = 1
    rw [rootRatio_self, map_one, map_one])

theorem rootG_cocycle (h : VeroneseRel u) (i j l : τ) :
    res (inf_le_left : rootChart u i ⊓ rootChart u j ⊓ rootChart u l ≤ rootChart u i ⊓ rootChart u j)
        (rootG hk h i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        rootChart u i ⊓ rootChart u j ⊓ rootChart u l ≤ rootChart u j ⊓ rootChart u l) (rootG hk h j l) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        rootChart u i ⊓ rootChart u j ⊓ rootChart u l ≤ rootChart u i ⊓ rootChart u l) (rootG hk h i l) :=
  Units.ext (by
    change resG X _ (resG X _ (rootRatio hk u i j)) * resG X _ (resG X _ (rootRatio hk u j l)) =
      resG X _ (resG X _ (rootRatio hk u i l))
    simp only [resG_resG]
    exact rootRatio_mul hk h l _ _)

theorem rootLB_isLB (h : VeroneseRel u) (hc : ⨆ i : τ, nonzeroLocus (u fun _ => i) = ⊤) :
    (rootLB hk h).IsLB where
  cover := hc
  g_self := rootG_self hk h
  cocycle := rootG_cocycle hk h

def rootIso (h : VeroneseRel u) : LB.Iso (pw (rootLB hk h) (k : ℤ)) Q where
  s p := (isUnit_resG_sec (u fun _ => (show τ from p.2)) p.1 inf_le_right inf_le_left).unit

theorem rootIso_isGen (h : VeroneseRel u) : (rootIso hk h).IsGen := by
  rintro ⟨c, i⟩ ⟨c', i'⟩
  let A := pw (rootLB hk h) (k : ℤ)
  have hp : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ Q.U c := inf_le_left.trans inf_le_left
  have hq : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ A.U i := inf_le_left.trans inf_le_right
  have hp' : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ Q.U c' := inf_le_right.trans inf_le_left
  have hq' : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ A.U i' := inf_le_right.trans inf_le_right
  have key : res (le_inf hp hq) (@id (Γ(X, Q.U c ⊓ A.U i)ˣ) ((rootIso hk h).s (c, i))) *
      res (le_inf hq hq') (A.g i i') = res (le_inf hp hp') (Q.g c c') *
        res (le_inf hp' hq') (@id (Γ(X, Q.U c' ⊓ A.U i')ˣ) ((rootIso hk h).s (c', i'))) := by
    refine Units.ext ?_
    have eg : resG X (le_inf hq hq') (A.g i i').val =
        resG X (show _ ≤ rootChart u (show τ from i) from hq) (rootRatio hk u i i') ^ k := by
      have : A.g i i' = (rootG hk h i i') ^ k := by
        change (rootG hk h i i') ^ (k : ℤ) = _
        exact zpow_natCast _ _
      rw [this, Units.val_pow_eq_pow_val]
      exact (map_pow (resG X (le_inf hq hq')) _ k).trans (congrArg (· ^ k) (resG_resG _ _ _))
    change resG X (le_inf hp hq) (resG X inf_le_left ((u fun _ => (show τ from i)).f c)) *
        resG X (le_inf hq hq') (A.g i i').val =
      resG X (le_inf hp hp') (Q.g c c').val *
        resG X (le_inf hp' hq') (resG X inf_le_left ((u fun _ => (show τ from i')).f c'))
    rw [resG_resG, resG_resG, ← sec_compat _ c c' hp hp', eg, mul_comm]
    exact rootRatio_pow hk h _ _ _
  change res (le_inf hp hq) (@id (Γ(X, Q.U c ⊓ A.U i)ˣ) ((rootIso hk h).s (c, i))) =
    res (le_inf hp hp') (Q.g c c') * (res (le_inf hq hq') (A.g i i'))⁻¹ *
      res (le_inf hp' hq') (@id (Γ(X, Q.U c' ⊓ A.U i')ˣ) ((rootIso hk h).s (c', i')))
  rw [mul_right_comm, ← key, mul_inv_cancel_right]

section Pull

variable {Y : Scheme.{0}} (b : Y ⟶ X) {L : LB Y} {d D : ℤ} (hD : d * k = D)
  (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D))

include hk in
theorem preimage_rootChart_le (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) (i : τ) :
    b ⁻¹ᵁ rootChart u i ≤ nonzeroLocus (a i) :=
  (nonzeroLocus_secPull _ _).ge.trans
    (((hm _).nonzeroLocus_eq (LB.isLB_pull hQ b) (isLB_pw hL D)).le.trans
      (nonzeroLocus_secMono_const hD a i hk).le)

theorem appLE_rootRatio_chart {W : Y.Opens} {i : τ} (j : τ) {c : Q.ι} (hi : W ≤ b ⁻¹ᵁ rootChart u i)
    (hc : W ≤ b ⁻¹ᵁ Q.U c) :
    (b.appLE _ W hi).hom (rootRatio hk u i j) * (b.appLE _ W hc).hom ((u fun _ => i).f c) =
      (b.appLE _ W hc).hom ((u (oneLetter hk i j)).f c) := by
  have hW : W ≤ b ⁻¹ᵁ (rootChart u i ⊓ Q.U c) := le_inf hi hc
  have e := congrArg (b.appLE (rootChart u i ⊓ Q.U c) W hW).hom
    (rootRatio_chart hk u j (inf_le_left : rootChart u i ⊓ Q.U c ≤ _) inf_le_right)
  rwa [map_mul, appLE_resG, appLE_resG, appLE_resG] at e

theorem appLE_rootRatio_mul (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) {W : Y.Opens} {i : τ} (j : τ)
    (hi : W ≤ b ⁻¹ᵁ rootChart u i) (p : L.ι) (hp : W ≤ L.U p) :
    (b.appLE _ W hi).hom (rootRatio hk u i j) * resG Y hp (chartFn (a i) p) =
      resG Y hp (chartFn (a j) p) := by
  have hnz : W ≤ nonzeroLocus (secPull (u fun _ => i) b) := hi.trans (nonzeroLocus_secPull _ _).ge
  refine ext_charts (secPull (u fun _ => i) b) hnz fun c' => ?_
  have hc' : W ⊓ (Q.pull b).U c' ≤ (Q.pull b).U c' := inf_le_right
  have hp' : W ⊓ (Q.pull b).U c' ≤ L.U p := inf_le_left.trans hp
  have hi' : W ⊓ (Q.pull b).U c' ≤ b ⁻¹ᵁ rootChart u i := inf_le_left.trans hi
  have hcb : W ⊓ (Q.pull b).U c' ≤ b ⁻¹ᵁ Q.U (c' ⟨⟩) := hc'.trans (pull_U Q b c').le
  let α : τ → Γ(Y, W ⊓ (Q.pull b).U c') := fun i => resG Y hp' (chartFn (a i) p)
  let β : (Fin k → τ) → Γ(Y, W ⊓ (Q.pull b).U c') :=
    fun w => (b.appLE (Q.U (c' ⟨⟩)) _ hcb).hom ((u w).f (c' ⟨⟩))
  let ρ : Γ(Y, W ⊓ (Q.pull b).U c') := (b.appLE _ _ hi').hom (rootRatio hk u i j)
  let t : Γ(Y, W ⊓ (Q.pull b).U c') := resG Y (le_inf hp' hc' : _ ≤ (pw L D).U p ⊓ (Q.pull b).U c')
    (@id (Γ(Y, (pw L D).U p ⊓ (Q.pull b).U c')ˣ) (θ.s (p, c'))).val
  have S : ∀ w, ∏ l, α (w l) = t * β w := fun w => by
    have e : resG Y (le_inf hp' hc' : _ ≤ (pw L D).U p ⊓ (Q.pull b).U c')
        (resG Y inf_le_left (∏ l, chartFn (a (w l)) p)) =
        resG Y (le_inf hp' hc' : _ ≤ (pw L D).U p ⊓ (Q.pull b).U c')
          ((@id (Γ(Y, (pw L D).U p ⊓ (Q.pull b).U c')ˣ) (θ.s (p, c'))).val *
            resG Y inf_le_right ((secPull (u w) b).f c')) :=
      congrArg _ (hm w (p, c'))
    rw [map_mul, resG_resG, resG_resG] at e
    refine (map_prod (resG Y hp') _ _).symm.trans (e.trans (congrArg (t * ·) ?_))
    exact (resG_resG _ _ _).trans rfl
  have hρ : ρ * β (fun _ => i) = β (oneLetter hk i j) := appLE_rootRatio_chart hk b j hi' hcb
  have e1 := prod_update_mul α (fun _ : Fin k => i) ⟨0, hk⟩ j
  have hP := S fun _ => i
  have uα : IsUnit (α i) := isUnit_resG_sec (a i) p
    (hi'.trans (preimage_rootChart_le hk b hD a θ hQ hL hm i)) hp'
  have uP : IsUnit (∏ _l : Fin k, α i) := by
    rw [Finset.prod_const]
    exact uα.pow _
  rw [map_mul, resG_appLE, resG_resG, resG_resG]
  change ρ * α i = α j
  refine uP.mul_left_cancel ?_
  calc (∏ _l : Fin k, α i) * (ρ * α i) = t * (ρ * β fun _ => i) * α i := by
        rw [hP]; ring
    _ = (∏ l, α (oneLetter hk i j l)) * α i := by rw [hρ, S]
    _ = _ := e1

def rootPullIso (h : VeroneseRel u) (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) :
    LB.Iso ((rootLB hk h).pull b) (pw L d) where
  s p := (isUnit_resG_sec (a (p.2 ⟨⟩)) p.1
    (inf_le_right.trans ((pull_U (rootLB hk h) b p.2).le.trans
      (preimage_rootChart_le hk b hD a θ hQ hL hm _))) inf_le_left).unit

theorem rootPullIso_isGen (h : VeroneseRel u) (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) :
    (rootPullIso hk b hD a θ h hQ hL hm).IsGen := by
  rintro ⟨l, i⟩ ⟨l', i'⟩
  let P := (rootLB hk h).pull b
  let M := pw L d
  have hp : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ M.U l := inf_le_left.trans inf_le_left
  have hq : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ P.U i := inf_le_left.trans inf_le_right
  have hp' : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ M.U l' := inf_le_right.trans inf_le_left
  have hq' : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ P.U i' := inf_le_right.trans inf_le_right
  have hi : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ b ⁻¹ᵁ rootChart u (i ⟨⟩) :=
    hq.trans (pull_U (rootLB hk h) b i).le
  have key : res (le_inf hp hq)
        (@id (Γ(Y, M.U l ⊓ P.U i)ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l, i))) *
      res (le_inf hq hq') (P.g i i') = res (le_inf hp hp') (M.g l l') *
        res (le_inf hp' hq')
          (@id (Γ(Y, M.U l' ⊓ P.U i')ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l', i'))) := by
    refine Units.ext ?_
    have eg : resG Y (le_inf hq hq') (P.g i i').val =
        (b.appLE _ _ hi).hom (rootRatio hk u (i ⟨⟩) (i' ⟨⟩)) := by
      have e := congrArg (fun v => resG Y (le_inf hq hq') (Units.val v)) (pull_g (rootLB hk h) b i i')
      refine e.trans ?_
      change resG Y _ (resG Y _ ((b.app _).hom (resG X inf_le_left (rootRatio hk u (i ⟨⟩) (i' ⟨⟩))))) = _
      refine (resG_resG _ _ _).trans ?_
      refine (congrArg (resG Y _) (app_resG b _ _)).trans ?_
      refine (resG_resG _ _ _).trans ?_
      rfl
    change resG Y (le_inf hp hq) (resG Y inf_le_left ((a (i ⟨⟩)).f l)) *
        resG Y (le_inf hq hq') (P.g i i').val =
      resG Y (le_inf hp hp') (M.g l l').val *
        resG Y (le_inf hp' hq') (resG Y inf_le_left ((a (i' ⟨⟩)).f l'))
    rw [resG_resG, resG_resG, ← sec_compat _ l l' hp hp', eg, mul_comm]
    exact appLE_rootRatio_mul hk b hD a θ hQ hL hm _ hi l hp
  change res (le_inf hp hq)
      (@id (Γ(Y, M.U l ⊓ P.U i)ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l, i))) =
    res (le_inf hp hp') (M.g l l') * (res (le_inf hq hq') (P.g i i'))⁻¹ *
      res (le_inf hp' hq')
        (@id (Γ(Y, M.U l' ⊓ P.U i')ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l', i')))
  rw [mul_right_comm, ← key, mul_inv_cancel_right]

end Pull

end Root

theorem exists_root_of_veronese : ∀ (X : Scheme.{0}) (Q : LB X), Q.IsLB → ∀ (k : ℕ), 1 ≤ k → ∀ (τ : Type) (u : (Fin k → τ) → LB.Sec Q), (∀ w₁ w₂ w₃ w₄ : Fin k → τ, (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c) → (⨆ i : τ, nonzeroLocus (u (fun _ => i)) = ⊤) → ∃ (A : LB X) (ω : LB.Iso (pw A (k : ℤ)) Q), A.IsLB ∧ ω.IsGen ∧ ∀ (Y : Scheme.{0}) (b : Y ⟶ X) (L : LB Y) (d D : ℤ) (hD : d * k = D) (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D)), L.IsLB → θ.IsGen → (∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) → LBIso (A.pull b) (pw L d) := by
  intro X Q hQ k hk τ u hrel hcov
  have h : VeroneseRel u := hrel
  exact ⟨rootLB hk h, rootIso hk h, rootLB_isLB hk h hcov, rootIso_isGen hk h,
    fun Y b L d D hD a θ hL _ hm => ⟨rootPullIso hk b hD a θ h hQ hL hm,
      rootPullIso_isGen hk b hD a θ h hQ hL hm⟩⟩

end GlobalTheory.CompanionTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_root_from_relations : ∀ (X : Scheme.{0}) (Q : LB X), Q.IsLB → ∀ (k : ℕ), 1 ≤ k → ∀ (τ : Type) (u : (Fin k → τ) → LB.Sec Q), (∀ w₁ w₂ w₃ w₄ : Fin k → τ, (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c) → (⨆ i : τ, nonzeroLocus (u (fun _ => i)) = ⊤) → ∃ (A : LB X) (ω : LB.Iso (pw A (k : ℤ)) Q), A.IsLB ∧ ω.IsGen ∧ ∀ (Y : Scheme.{0}) (b : Y ⟶ X) (L : LB Y) (d D : ℤ) (hD : d * k = D) (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D)), L.IsLB → θ.IsGen → (∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) → LBIso (A.pull b) (pw L d) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

variable {X : Scheme.{0}}

theorem res_res_units {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (resG_resG h₁ h₂ _)

theorem mul_chart_cancel {S : Type} [CommRing S] (u G k' k u' a : S) (h : u = G * k' * u') (h' : k' * k = 1) :
    u * (k * a) = G * (u' * a) := by
  subst h
  linear_combination (G * u' * a) * h'

theorem eq_of_resG_near {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ y ∈ U, ∃ (W : X.Opens) (_ : y ∈ W) (hW : W ≤ U), resG X hW a = resG X hW b) : a = b :=
  ext_germ fun y hy => by
    obtain ⟨W, hyW, hW, e⟩ := h y hy
    rw [← germ_resG hW y hyW a, ← germ_resG hW y hyW b, e]

theorem iso_sec_chart {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) (p p' : B.ι) (q q' : A.ι)
    {W : X.Opens} (h₁ : W ≤ B.U p) (h₁' : W ≤ B.U p') (h₂ : W ≤ A.U q) (h₂' : W ≤ A.U q') :
    resG X (le_inf h₁ h₂) (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) * resG X h₂ (a.f q) =
      resG X (le_inf h₁ h₁') (B.g p p' : Γ(X, B.U p ⊓ B.U p')) *
        (resG X (le_inf h₁' h₂') (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q')) : Γ(X, B.U p' ⊓ A.U q')) *
          resG X h₂' (a.f q')) := by
  have hW : W ≤ (LB.div B A).U (p, q) ⊓ (LB.div B A).U (p', q') :=
    le_inf (le_inf h₁ h₂) (le_inf h₁' h₂')
  have e := congrArg (res hW) (hw (p, q) (p', q'))
  have e₂ : res hW ((LB.div B A).g (p, q) (p', q')) =
      res (le_inf h₁ h₁') (B.g p p') * (res (le_inf h₂ h₂') (A.g q q'))⁻¹ := by
    exact (map_mul (res hW) _ _).trans (congrArg₂ (· * ·) (res_res_units _ _ _)
      ((map_inv (res hW) _).trans (congrArg (·⁻¹) (res_res_units _ _ _))))
  rw [map_mul, e₂, res_res_units, res_res_units] at e
  have e₃ := congrArg (fun u : Γ(X, W)ˣ => (u : Γ(X, W))) e
  simp only [Units.val_mul] at e₃
  rw [sec_compat a q q' h₂ h₂']
  have e₄ : ((res (le_inf h₂ h₂') (A.g q q'))⁻¹ : Γ(X, W)ˣ).val * resG X (le_inf h₂ h₂') (A.g q q' : Γ(X, A.U q ⊓ A.U q')) = 1 :=
    Units.inv_mul (res (le_inf h₂ h₂') (A.g q q'))
  exact mul_chart_cancel _ _ _ _ _ _ e₃ e₄

theorem exists_secMaps {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) :
    ∃ b : B.Sec, SecMaps w a b := by
  have hself : ∀ (p : B.ι) {W : X.Opens} (h : W ≤ B.U p),
      resG X (le_inf h h) (B.g p p : Γ(X, B.U p ⊓ B.U p)) = 1 := by
    intro p W h
    have e := congrArg (fun u : Γ(X, B.U p)ˣ => resG X h (u : Γ(X, B.U p))) (hB.g_self p)
    simp only [val_res, resG_resG, Units.val_one, map_one] at e
    exact e
  have glue : ∀ p : B.ι, ∃ b : Γ(X, B.U p), ∀ q : A.ι, resG X (inf_le_left : B.U p ⊓ A.U q ≤ B.U p) b =
      (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q) := by
    intro p
    obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun q : A.ι => B.U p ⊓ A.U q) (B.U p)
      (fun _ => homOfLE inf_le_left)
      (fun y hy => by
        obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, hq⟩)
      (fun q => (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q))
      (fun q q' => by
        have h₁ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ B.U p := inf_le_left.trans inf_le_left
        have h₂ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
        have h₃ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
        have k := iso_sec_chart hw a p p q q' h₁ h₁ h₂ h₃
        rw [hself p h₁, one_mul] at k
        change resG X inf_le_left _ = resG X inf_le_right _
        rw [map_mul, map_mul]
        repeat rw [resG_resG]
        exact k)
    exact ⟨b, hb⟩
  choose b hb using glue
  refine ⟨⟨b, fun p p' => ?_⟩, fun r => hb r.1 r.2⟩
  refine eq_of_resG_near fun y hy => ?_
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
  have h₀ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p ⊓ B.U p' := inf_le_left
  have h₁ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p := inf_le_left.trans inf_le_left
  have h₁' : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p' := inf_le_left.trans inf_le_right
  have h₂ : B.U p ⊓ B.U p' ⊓ A.U q ≤ A.U q := inf_le_right
  refine ⟨B.U p ⊓ B.U p' ⊓ A.U q, ⟨hy, hq⟩, h₀, ?_⟩
  have e₁ := congrArg (resG X (le_inf h₁ h₂)) (hb p q)
  have e₂ := congrArg (resG X (le_inf h₁' h₂)) (hb p' q)
  rw [map_mul, resG_resG, resG_resG] at e₁ e₂
  have k := iso_sec_chart hw a p p' q q h₁ h₁' h₂ h₂
  change resG X h₀ (resG X inf_le_left (b p)) = resG X h₀ ((B.g p p' : Γ(X, B.U p ⊓ B.U p')) * resG X inf_le_right (b p'))
  rw [map_mul, resG_resG, resG_resG]
  exact e₁.trans (k.trans (congrArg _ e₂.symm))

theorem relAmple_tw_of_roots : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (m : ℕ) (ζ : Fin (m + 1) → LB.Sec Q), Q.IsLB → VeryAmpleBy X.hom Q ζ → ∀ (A C : LB X.left) (n : ℕ), 1 ≤ n → A.IsLB → C.IsLB → LBIso (pw A ((n + 1 : ℕ) : ℤ)) Q → LBIso (pw C (n : ℤ)) Q → RelAmple X (tw C A (-1)) := by
  intro R _ X Q m ζ hQ hva A C n hn hA hC hAQ hCQ
  have hM : (tw C A (-1)).IsLB := isLB_tw hC hA _
  have hD : 1 ≤ n * (n + 1) := Nat.mul_pos hn (Nat.succ_pos n)
  have hP := isLB_pw hM ((n * (n + 1) : ℕ) : ℤ)
  have hcls : GlobalTheory.CechPic.cls _ hP = GlobalTheory.CechPic.cls Q hQ := by
    have hc : GlobalTheory.CechPic.cls _ hM = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
      refine (GlobalTheory.CechPic.cls_div hC (isLB_pw hA _) hM).trans ?_
      rw [GlobalTheory.AmpleStabFinite.cls_pw hA]
      simp
    have e₁ : ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hA _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hAQ)
    have e₂ : (n : ℤ) • GlobalTheory.CechPic.cls C hC = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hC _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hCQ)
    rw [GlobalTheory.AmpleStabFinite.cls_pw hM, hc, smul_sub]
    have f₁ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls C hC = ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₂, smul_smul]; congr 1 <;> (push_cast; ring)
    have f₂ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = (n : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₁, smul_smul]; congr 1 <;> (push_cast; ring)
    rw [f₁, f₂, ← sub_smul]
    simp
  obtain ⟨w, hw⟩ : LBIso Q (pw (tw C A (-1)) ((n * (n + 1) : ℕ) : ℤ)) := (GlobalTheory.CechPic.cls_eq_iff hQ hP).1 hcls.symm
  choose t ht using fun i => exists_secMaps hQ hP hw (ζ i)
  obtain ⟨hs, hci⟩ := (veryAmpleBy_iff X.hom ζ).1 hva
  have ht' := iSup_nonzeroLocus_of_secMaps hs hQ hP ht
  refine GlobalTheory.Unif.relAmple_of_veryAmpleBy hM hD t ((veryAmpleBy_iff X.hom t).2 ⟨ht', ?_⟩)
  rw [toProj_eq_of_secMaps hs ht' ht]
  exact hci

end GlobalTheory.CompanionTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatively_ample_twist_difference : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (m : ℕ) (ζ : Fin (m + 1) → LB.Sec Q), Q.IsLB → VeryAmpleBy X.hom Q ζ → ∀ (A C : LB X.left) (n : ℕ), 1 ≤ n → A.IsLB → C.IsLB → LBIso (pw A ((n + 1 : ℕ) : ℤ)) Q → LBIso (pw C (n : ℤ)) Q → RelAmple X (tw C A (-1)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.relAmple_tw_of_roots
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem lbIso_pull_quot_of_consecutive_pw : ∀ {X Y : Scheme.{0}} (b : Y ⟶ X) (A C : LB X) (N : LB Y) (n : ℤ), A.IsLB → C.IsLB → N.IsLB → LBIso (A.pull b) (pw N n) → LBIso (C.pull b) (pw N (n + 1)) → LBIso N ((tw C A (-1)).pull b) := by
  intro X Y b A C N n hA hC hN h1 h2
  have hAb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hA b
  have hCb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hC b
  have hT := GlobalTheory.AbLaw.isLB_tw hC hA (-1)
  have hTb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hT b
  rw [← GlobalTheory.CechPic.cls_eq_iff hN hTb, GlobalTheory.CechPic.cls_pull hT b hTb]
  have e1 := (GlobalTheory.CechPic.cls_eq_iff hAb (GlobalTheory.AbLaw.isLB_pw hN n)).2 h1
  have e2 := (GlobalTheory.CechPic.cls_eq_iff hCb (GlobalTheory.AbLaw.isLB_pw hN (n + 1))).2 h2
  rw [GlobalTheory.CechPic.cls_pull hA b hAb, GlobalTheory.EffBound.cls_pw hN n] at e1
  rw [GlobalTheory.CechPic.cls_pull hC b hCb, GlobalTheory.EffBound.cls_pw hN (n + 1)] at e2
  have hT' : GlobalTheory.CechPic.cls (GlobalTheory.AbLaw.tw C A (-1)) hT
      = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
    show GlobalTheory.CechPic.cls (C.div (GlobalTheory.AbLaw.pw A (-(-1)))) hT = _
    rw [GlobalTheory.CechPic.cls_div hC (GlobalTheory.AbLaw.isLB_pw hA _) hT, GlobalTheory.EffBound.cls_pw hA]
    simp
  rw [hT', map_sub, e1, e2, add_smul, one_smul, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.FormalAlg
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_twist_iso_difference : ∀ {X Y : Scheme.{0}} (b : Y ⟶ X) (A C : LB X) (N : LB Y) (n : ℤ), A.IsLB → C.IsLB → N.IsLB → LBIso (A.pull b) (pw N n) → LBIso (C.pull b) (pw N (n + 1)) → LBIso N ((tw C A (-1)).pull b) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
open GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem exists_compatible {R : Type} [CommRing R] (I : Ideal R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {N : ∀ e, LB (Y e).left}
    {v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))} {D : ℤ}
    (step : ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D),
      SecMaps (pullPow (v e) D) σ (secPull σ' (β e)))
    {τ : Type} (a₀ : τ → LB.Sec (pw (N 0) D)) :
    ∃ a : ∀ e, τ → LB.Sec (pw (N e) D), a 0 = a₀ ∧
      ∀ e i, SecMaps (pullPow (v e) D) (a e i) (secPull (a (e + 1) i) (β e)) := by
  choose L hL using step
  exact ⟨fun e i => Nat.rec (motive := fun e => LB.Sec (pw (N e) D)) (a₀ i) (fun e x => L e x) e,
    rfl, fun e i => hL e _⟩

theorem tower_sections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (n p q : ℕ) (a : ∀ e, Fin (p + 1) → LB.Sec (pw (N e) (n : ℤ))) (c : ∀ e, Fin (q + 1) → LB.Sec (pw (N e) ((n : ℤ) + 1))), 1 ≤ n ∧ VeryAmpleBy (Y 0).hom (pw (N 0) (n : ℤ)) (a 0) ∧ VeryAmpleBy (Y 0).hom (pw (N 0) ((n : ℤ) + 1)) (c 0) ∧ (∀ e i, SecMaps (pullPow (v e) (n : ℤ)) (a e i) (secPull (a (e + 1) i) (β e))) ∧ (∀ e i, SecMaps (pullPow (v e) ((n : ℤ) + 1)) (c e i) (secPull (c (e + 1) i) (β e))) := by
  intro R _ _ I Y β hβ hP N v hN hA
  obtain ⟨d, hd, m₁, s, m₂, s', hs, hs'⟩ := GlobalTheory.T.relatively_ample_consecutive_very_ample (R ⧸ I ^ (0 + 1)) (Y 0) (N 0) (hN 0).1 hA
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.T.formal_line_bundle_very_ample_system R I Y β hβ hP N v hN d hd m₁ s hs
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.T.formal_line_bundle_very_ample_system R I Y β hβ hP N v hN (d + 1) (by omega) m₂ s' hs'
  set k := max t₁ t₂ with hk
  set t := 1 + (d + 1) * k with ht
  set t' := 1 + d * k with ht'
  have hkt : k ≤ t := by nlinarith
  have hkt' : k ≤ t' := by nlinarith
  have h1 : t₁ ≤ t := (le_max_left _ _).trans hkt
  have h2 : t₂ ≤ t' := (le_max_right _ _).trans hkt'
  have e₁ : ((d * t : ℕ) : ℤ) = (d : ℤ) * (t : ℕ) := by push_cast; ring
  have e₂ : ((d * t : ℕ) : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) * (t' : ℕ) := by
    simp only [ht, ht']; push_cast; ring
  have hc₁ : 0 < Fintype.card (Fin t → Fin (m₁ + 1)) := Fintype.card_pos
  have hc₂ : 0 < Fintype.card (Fin t' → Fin (m₂ + 1)) := Fintype.card_pos
  obtain ⟨p, hp⟩ : ∃ p, Fintype.card (Fin t → Fin (m₁ + 1)) = p + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₁).symm⟩
  obtain ⟨q, hq⟩ : ∃ q, Fintype.card (Fin t' → Fin (m₂ + 1)) = q + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₂).symm⟩
  let E₁ : Fin (p + 1) ≃ (Fin t → Fin (m₁ + 1)) := (Fintype.equivFinOfCardEq hp).symm
  let E₂ : Fin (q + 1) ≃ (Fin t' → Fin (m₂ + 1)) := (Fintype.equivFinOfCardEq hq).symm
  have ht1 : 1 ≤ t := by omega
  have ht1' : 1 ≤ t' := by omega
  have va := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ t e₁.symm m₁ s (hN 0).1 ht1 hs p E₁
  have vc := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ t' e₂.symm m₂ s' (hN 0).1 ht1' hs' q E₂
  obtain ⟨a, ha0, ha⟩ := exists_compatible I (v := v) (ht₁ t h1 _ e₁) (fun j => secMono e₁.symm s (E₁ j))
  obtain ⟨c, hc0, hc⟩ := exists_compatible I (v := v) (ht₂ t' h2 _ e₂) (fun j => secMono e₂.symm s' (E₂ j))
  refine ⟨d * t, p, q, a, c, Nat.mul_pos hd ht1, ?_, ?_, ha, hc⟩
  · rw [ha0]; exact va
  · rw [hc0]; exact vc

theorem schemes_of_closedProj : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro hGE R _ _ I hI Y β hβ hP N hN hv hA
  choose v hvg using hv
  have hNv : ∀ e, (N e).IsLB ∧ (v e).IsGen := fun e => ⟨hN e, hvg e⟩
  obtain ⟨n, p, q, a, c, hn, ha0, hc0, hca, hcc⟩ := tower_sections R I Y β hβ hP N v hNv hA
  set D : ℤ := (n : ℤ) * ((n + 1 : ℕ) : ℤ) with hD
  have h1 : (n : ℤ) * ((n + 1 : ℕ) : ℤ) = D := rfl
  have h2 : ((n : ℤ) + 1) * ((n : ℕ) : ℤ) = D := by rw [hD]; push_cast; ring
  have hcard : ∀ (k r : ℕ), ∃ m, Fintype.card (Fin k → Fin (r + 1)) = m + 1 := fun k r =>
    ⟨_, (Nat.succ_pred_eq_of_pos (Fintype.card_pos (α := Fin k → Fin (r + 1)))).symm⟩
  obtain ⟨m₁, hm₁⟩ := hcard (n + 1) p
  obtain ⟨m₂, hm₂⟩ := hcard n q
  let E₁ : Fin (m₁ + 1) ≃ (Fin (n + 1) → Fin (p + 1)) := (Fintype.equivFinOfCardEq hm₁).symm
  let E₂ : Fin (m₂ + 1) ≃ (Fin n → Fin (q + 1)) := (Fintype.equivFinOfCardEq hm₂).symm
  let m := m₁ + 1 + m₂
  let E : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  let z : ∀ e, Fin (m + 1) → LB.Sec (pw (N e) D) := fun e j =>
    Sum.elim (fun i => secMono h1 (a e) (E₁ i)) (fun i => secMono h2 (c e) (E₂ i)) (E j)
  have hz1 : ∀ e w, z e (E.symm (Sum.inl (E₁.symm w))) = secMono h1 (a e) w := fun e w => by
    simp [z]
  have hz2 : ∀ e w, z e (E.symm (Sum.inr (E₂.symm w))) = secMono h2 (c e) w := fun e w => by
    simp [z]
  have hva : VeryAmpleBy (Y 0).hom (pw (N 0) D) (z 0) := by
    have x1 := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ (n + 1) h1 p (a 0) (hN 0) (by omega) ha0 m₁ E₁
    have x2 := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ n h2 q (c 0) (hN 0) hn hc0 m₂ E₂
    exact GlobalTheory.T.very_ample_union_sections _ (Y 0).hom _ (isLB_pw (hN 0) D) m₁ m₂ m _ _ E x1 x2
  have hzc : ∀ e j, SecMaps (pullPow (v e) D) (z e j) (secPull (z (e + 1) j) (β e)) := fun e j => by
    simp only [z]
    rcases E j with i | i
    · exact secMaps_secMono (v e) h1 (a e) (a (e + 1)) (hca e) _
    · exact secMaps_secMono (v e) h2 (c e) (c (e + 1)) (hcc e) _
  obtain ⟨X, Q, ζ, b, ω, hQ, hX, hXa, hb, hbc, hω, hωz, hquad, hcov⟩ :=
    GlobalTheory.T.formal_sections_compatible_system hGE R I hI Y β hβ (fun e => pw (N e) D) (fun e => pullPow (v e) D)
      (fun e => ⟨isLB_pw (hN e) D, pullPow_isGen _ _ (hvg e)⟩) m z hzc hva
  let ia : (Fin (n + 1) → Fin (p + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inl (E₁.symm w))
  let ic : (Fin n → Fin (q + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inr (E₂.symm w))
  have hA' : ⨆ i : Fin (p + 1), nonzeroLocus (ζ (ia fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (p + 1) => ia fun _ => i) (by
      rw [iSup_range, ← ha0.1]
      refine iSup_congr fun i => ?_
      rw [hz1, nonzeroLocus_secMono_const h1 _ _ (by omega)])
    rwa [iSup_range] at this
  have hC' : ⨆ i : Fin (q + 1), nonzeroLocus (ζ (ic fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (q + 1) => ic fun _ => i) (by
      rw [iSup_range, ← hc0.1]
      refine iSup_congr fun i => ?_
      rw [hz2, nonzeroLocus_secMono_const h2 _ _ hn])
    rwa [iSup_range] at this
  obtain ⟨A, ωA, hAL, hωA, hAc⟩ := GlobalTheory.T.line_bundle_root_from_relations X.left Q hQ (n + 1) (by omega) (Fin (p + 1)) (fun w => ζ (ia w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ia, hz1]; exact secMono_mul h1 (a e) w₁ w₂ w₃ w₄ hw c'') c') hA'
  obtain ⟨C, ωC, hCL, hωC, hCc⟩ := GlobalTheory.T.line_bundle_root_from_relations X.left Q hQ n hn (Fin (q + 1)) (fun w => ζ (ic w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ic, hz2]; exact secMono_mul h2 (c e) w₁ w₂ w₃ w₄ hw c'') c') hC'
  refine ⟨X, tw C A (-1), b, hX, isLB_tw hCL hAL _,
    GlobalTheory.T.relatively_ample_twist_difference R X Q m ζ hQ hXa A C n hn hAL hCL ⟨ωA, hωA⟩ ⟨ωC, hωC⟩, hb, hbc, fun e => ?_⟩
  refine GlobalTheory.T.pullback_twist_iso_difference (b e) A C (N e) n hAL hCL (hN e) ?_ ?_
  · refine hAc _ (b e) (N e) n D h1 (a e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ia w)
    simp only [ia, hz1] at this
    exact this
  · refine hCc _ (b e) (N e) ((n : ℤ) + 1) D h2 (c e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ic w)
    simp only [ic, hz2] at this
    exact this

end GlobalTheory.CompanionTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_algebraisation_schemes : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj
end
