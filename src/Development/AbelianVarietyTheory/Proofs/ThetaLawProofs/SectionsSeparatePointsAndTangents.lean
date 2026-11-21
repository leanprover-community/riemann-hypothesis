import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSymmetricInterpolating
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KaFormHomogeneous
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.UnifDifferential GlobalTheory.SqZero

noncomputable section

namespace GlobalTheory.KaScale

section Lin

variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))}

theorem valT_comp {T : Type} [CommRing T] {X Y : Scheme.{0}} (w : Sp T ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valT (w ≫ φ) U f = valT w (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valT
  by_cases h : ⊤ ≤ w ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]
    rfl
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]

def der (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U)) : K :=
  TrivSqZeroExt.snd (valT (T := DualNumber K) v.left U f)

theorem der_pos (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U))
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) : der v U f = (pullFn v U h f).snd := congrArg _ (dif_pos h)

theorem der_neg (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U))
    (h : ¬ ⊤ ≤ v.left ⁻¹ᵁ U) : der v U f = 0 := congrArg _ (dif_neg h)

theorem der_scale (v : sp (R₀ := K) (DualNumber K) ⟶ A) (c : K) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der (Chart.spMap (scaleD c) ≫ v) U f = c * der v U f := by
  have : Subsingleton (PrimeSpectrum (DualNumber K)) := subsingleton_primeSpectrum K K
  by_cases h : ⊤ ≤ v.left ⁻¹ᵁ U
  · have h' := le_preimage_comp (scaleD c) v _ rfl U h
    rw [der_pos _ _ _ h, der_pos _ _ _ h', pullFn_comp (scaleD c) v _ rfl U h h' f, scaleD_eq]
    simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
  · rw [der_neg _ _ _ h, der_neg _ _ _ (fun h' => h (le_preimage_of_comp (scaleD c) v _ rfl U h')), mul_zero]

variable [GrpObj A]

theorem le_of_isTan {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : Chart.IsTan v) (hv' : Chart.IsTan v')
    (U : A.left.Opens) (h : ⊤ ≤ v.left ⁻¹ᵁ U) : ⊤ ≤ v'.left ⁻¹ᵁ U := by
  have : Subsingleton (PrimeSpectrum (DualNumber K)) := subsingleton_primeSpectrum K K
  exact le_preimage_of_comp (fstD K) v' 1 hv'.symm U (le_preimage_comp (fstD K) v 1 hv.symm U h)

theorem der_mul {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : Chart.IsTan v) (hv' : Chart.IsTan v')
    (U : A.left.Opens) (f : Γ(A.left, U)) : der (v * v') U f = der v U f + der v' U f := by
  by_cases h : ⊤ ≤ (v * v').left ⁻¹ᵁ U
  · obtain ⟨h₁, h₂, e⟩ := snd_pullFn_mul hv hv' U h
    rw [der_pos _ _ _ h, der_pos _ _ _ h₁, der_pos _ _ _ h₂, e]
  · rw [der_neg _ _ _ h, der_neg _ _ _ (fun h' => h (le_of_isTan hv (isTan_mul hv hv') U h')),
      der_neg _ _ _ (fun h' => h (le_of_isTan hv' (isTan_mul hv hv') U h')), add_zero]

theorem der_one (U : A.left.Opens) (f : Γ(A.left, U)) :
    der (1 : sp (R₀ := K) (DualNumber K) ⟶ A) U f = 0 := by
  rw [← comp_one' (Chart.spMap (scaleD (0 : K))), der_scale, zero_mul]

theorem der_prod (U : A.left.Opens) (f : Γ(A.left, U)) :
    ∀ {n : ℕ} (v : Fin n → (sp (R₀ := K) (DualNumber K) ⟶ A)), (∀ i, Chart.IsTan (v i)) →
      Chart.IsTan (List.ofFn v).prod ∧ der (List.ofFn v).prod U f = ∑ i, der (v i) U f
  | 0, v, _ => by
    rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨isTan_one, der_one U f⟩
  | n + 1, v, hv => by
    obtain ⟨h₁, h₂⟩ := der_prod U f (fun i => v i.succ) (fun i => hv _)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, der_mul (hv 0) h₁, h₂]
    exact ⟨isTan_mul (hv 0) h₁, rfl⟩

theorem der_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (hw : IsLieComb c v w) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der w U f = ∑ i, c i * der (v i) U f := by
  rw [(isLieComb_iff c v w).1 hw]
  refine (der_prod U f _ (fun i => isTan_scale (c i) ((isTan_iff _).2 (hv i)))).2.trans ?_
  exact Finset.sum_congr rfl fun i _ => der_scale _ _ _ _

theorem translate_left (z : 𝟙_ (Over (Sp K)) ⟶ A) (v : epsR K ⟶ A) :
    ((toUnit (epsR K) ≫ z) * v).left = v.left ≫ ((toUnit A ≫ z) * 𝟙 A).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem snd_valT_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (hw : IsLieComb c v w) (z : 𝟙_ (Over (Sp K)) ⟶ A)
    (U : A.left.Opens) (f : Γ(A.left, U)) :
    TrivSqZeroExt.snd (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * w).left U f) =
      ∑ i, c i * TrivSqZeroExt.snd (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * v i).left U f) := by
  simp only [translate_left]
  exact (congrArg _ (valT_comp _ _ _ _)).trans ((der_comb hv hw _ _).trans
    (Finset.sum_congr rfl fun i _ => congrArg (fun t => c i * TrivSqZeroExt.snd t) (valT_comp _ _ _ _).symm))

end Lin

def cS {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) : K →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (p ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem gs_constFn' {K : Type} [CommRing K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) (W : X.Opens) (r : Y ⟶ X)
    (y : Y) (hy : r y ∈ W) (a : K) : gs r y W (constFn p W a) = cS (r ≫ p) y a :=
  ((gs_res r y (fun _ _ => trivial : W ≤ p ⁻¹ᵁ ⊤) hy _).trans (gs_pull r p y ⊤ trivial _)).trans
    (gs_eq (r ≫ p) y ⊤ trivial _)

theorem gs_cst' {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) (a : K) :
    gs (𝟙 Y) y ⊤ (AbLaw.cst p ⊤ a) = cS p y a :=
  (gs_constFn' p ⊤ (𝟙 Y) y trivial a).trans (by rw [Category.id_comp])

variable {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'}

theorem isSquareDetComparison_scale_sec (a : Kˣ) (hth₀ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ (a : K) * LB.Sec.f th i)
    (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b) (lam : Kˣ)
    (h : IsSquareDeterminantComparison ⟨P, hg, rig, hr, th, hth, v, hv⟩ m al b lam) :
    IsSquareDeterminantComparison ⟨P, hg, rig, hr, th', hth', v', hv'⟩ m al b (lam * a ^ (8 * m ^ (4 * P.g + 2))) := by
  obtain ⟨ξ, mu, w, Q, rho, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨ξ, mu, w, (a : K) ^ 4 • Q, rho, h₁, h₂, h₃, h₄, h₅, fun I y J hJ => ?_, ?_⟩
  · have e := h₆ I y J hJ
    simp only [gs_cst'] at e ⊢
    have e₂ : ∀ r : Fin 4, gs (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left y _
        (LB.Sec.f th' (J (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left)) =
        cS (Out.powObj P.A 4).hom y a * gs (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left y _
        (LB.Sec.f th (J (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left)) := fun r => by
      rw [hth₀, gs_mul _ _ _ (hJ _), gs_constFn' _ _ _ _ (hJ _), Over.w]
      rfl
    refine (Finset.prod_congr rfl fun r _ => e₂ r).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg _ e).trans ?_
    rw [mul_left_comm, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, _root_.mul_assoc]
  · rw [Units.val_mul, h₇, Matrix.det_smul, Units.val_pow_eq_pow_val]
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring

theorem jac_scale (M : Matrix (Fin P.g) (Fin P.g) K) (hM : ∀ i, IsLieComb (M i) v (v' i)) {n : ℕ}
    (s : Fin P.g → LB.Sec (pw P.L (n : ℤ))) (z) (c) :
    jac ⟨P, hg, rig, hr, th', hth', v', hv'⟩ s z c = jac ⟨P, hg, rig, hr, th, hth, v, hv⟩ s z c * M.det := by
  unfold jac
  rw [← Matrix.det_transpose M, ← Matrix.det_mul]
  congr 1
  ext i k
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine (snd_valT_comb hv.1 (hM k) z _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  exact mul_comm _ _

theorem kaVal_scale : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin P.g → LB.Sec (pw P.L (n : ℤ))) (κ : Kˣ), admitted P.g n l l' al → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → KaVal ⟨P, hg, rig, hr, th, hth, v, hv⟩ n l l' al s κ → ∃ κ' : Kˣ, KaVal ⟨P, hg, rig, hr, th', hth', v', hv'⟩ n l l' al s κ' ∧ a ^ (8 * kaExp P.g n l l') * (κ' : K) = M.det ^ (4 * kaExp P.g n l l') * κ := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M n l l' al s κ hadm hth₀ hM hκ
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨y, -, hy⟩ := hth' (IsLocalRing.closedPoint K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hth₀, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  have : IsCommMonObj P.A := P.isAb.comm
  have hdet : IsUnit M.det := ((LieComb.lieComb_algebra K P.A P.g v hv.1).2.2.2.2 M v' hv hM).1 hv'
  lift a to Kˣ using ha.isUnit
  obtain ⟨D, hD⟩ := hdet
  obtain ⟨z, ch, b, b', t, t', J, lam, lam', ⟨e₁, e₂, e₃, e₄, e₅⟩, hJ, hb, hb', ht, ht', rfl⟩ := hκ
  refine ⟨_, ⟨z, ch, b, b', t, t', J * D ^ (P.g.factorial * n ^ P.g),
    fun j => lam j * a ^ (8 * (l - j * n) ^ (4 * P.g + 2)),
    fun j => lam' j * a ^ (8 * (l' - j * n) ^ (4 * P.g + 2)), ⟨e₁, e₂, fun k => ?_, e₄, e₅⟩, ?_,
    fun j hj => ⟨(hb j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb j hj).2⟩,
    fun j hj => ⟨(hb' j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb' j hj).2⟩, ht, ht', rfl⟩, ?_⟩
  · rw [jac_scale (th := th) (hth := hth) (hv := hv) M hM, ← hD]
    exact (e₃ k).mul D.isUnit
  · rw [Units.val_mul, hJ, Units.val_pow_eq_pow_val, hD]
    simp only [jac_scale (th := th) (hth := hth) (hv := hv) (th' := th') (hth' := hth') (hv' := hv') M hM]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have key := kaForm_homogeneous K P.g n l l' t t' J 1 a 1 lam lam' (fun _ => 1) (fun _ => 1)
      hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at key
    rw [← hD]
    norm_cast
    rw [← key]
    unfold kaForm kaExp
    generalize tComb P.g n l _ t _ = X
    generalize tComb P.g n l' _ t' _ = X'
    generalize degProd P.g n l l' ^ (3 * P.g + 2) = N
    generalize P.g.factorial * n ^ P.g = F
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
    push_cast [Nat.cast_sub hadm.2.2.1.le]
    module

end GlobalTheory.KaScale
end
end

section
noncomputable section

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

theorem GlobalTheory.VeryAmpleJet.veryAmpleBy_of_veryAmpleAt {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
    [GrpObj A] {L : LB A.left} (hL : L.IsLB) {N : ℕ} (hA : VeryAmpleAt A L N) {X : Scheme.{0}} (e : X ⟶ A.left)
    [IsIso e] {f : X ⟶ Spec (CommRingCat.of R)} (hf : e ≫ A.hom = f) {H : LB X} (hH : H.IsLB)
    (hw : LBIso H (L.pull e)) :
    ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw H N)), VeryAmpleBy f (pw H N) s := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  have : IsIso (A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso A.left.topIso.hom)
  obtain ⟨ψ, hiso, hψ⟩ : ∃ ψ : X ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, IsIso ψ ∧ ψ ≫ (A.hom ⁻¹ᵁ ⊤).ι = e :=
    ⟨e ≫ inv (A.hom ⁻¹ᵁ ⊤).ι, inferInstance, by simp⟩
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1)
  have hP' := isLB_pw hH N
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullPw H N)
    (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) ψ _
      fun _ => (Category.id_comp _).trans hψ.symm)
    (iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin N => 𝟙 X) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := pw H N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1
        ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L ⊤ N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have hT : IsIso (⊤ : (Spec (CommRingCat.of R)).Opens).ι :=
      inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
    let θ : CommRingCat.of R ⟶ Γ((⊤ : (Spec (CommRingCat.of R)).Opens).toScheme, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι.app ⊤
    have hθi : IsIso θ := IsIso.comp_isIso' inferInstance (inferInstanceAs
      (IsIso ((⊤ : (Spec (CommRingCat.of R)).Opens).ι.app ⊤)))
    have hθ : Function.Surjective θ.hom :=
      (ConcreteCategory.bijective_of_isIso θ).2
    have hf' : f = ψ ≫ (A.hom ∣_ ⊤) ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι := by
      rw [morphismRestrict_ι, ← Category.assoc, hψ, hf]
    have hap : IsIso (ψ.appLE _ _ (loc i).le) := by
      have key : ∀ (V : X.Opens) (h : V = ψ ⁻¹ᵁ nonzeroLocus (s i)), IsIso (ψ.appLE _ V h.le) := by
        rintro _ rfl
        rw [Scheme.Hom.appLE_eq_app]
        infer_instance
      exact key _ (loc i)
    have hc : cst f (nonzeroLocus (M := pw H N) (s' i)) =
        (ψ.appLE _ _ (loc i).le).hom.comp
          (((A.hom ∣_ ⊤).appLE ⊤ (nonzeroLocus (s i)) le_top).hom.comp θ.hom) := by
      rw [hf']
      have e₁ := Scheme.Hom.appLE_comp_appLE ψ (A.hom ∣_ ⊤) ⊤ (nonzeroLocus (s i))
        (nonzeroLocus (M := pw H N) (s' i)) le_top (loc i).le
      ext x
      have e₂ := congrArg (fun q => q.hom (θ.hom x)) e₁
      exact e₂.symm
    intro d
    obtain ⟨d, rfl⟩ := (ConcreteCategory.bijective_of_isIso (ψ.appLE _ _ (loc i).le)).2 d
    obtain ⟨p, rfl⟩ := hsurj d
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective θ.hom hθ p
    refine ⟨p, ?_⟩
    rw [hc, MvPolynomial.eval₂Hom_map_hom]
    exact (MvPolynomial.map_eval₂Hom _ _ _ p).symm

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.VeryAmpleJet

open GlobalTheory.KeyKa.EtBaseChange GlobalTheory.PointInterp

theorem exists_rows_det_ne_zero {K m : Type} [Field K] [Fintype m] {g : ℕ} (M : Matrix m (Fin g) K)
    (h : ∀ c, M.mulVec c = 0 → c = 0) : ∃ a : Fin g → m, (M.submatrix a id).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K M.row
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hr : M.rank = g := by
    have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [LinearMap.ker_eq_bot'.2 h, finrank_bot, add_zero, Module.finrank_fin_fun] at h1
    exact h1
  have hκ : Fintype.card κ = g := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hr]
  let e : Fin g ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  have h1 : LinearIndependent K (M.submatrix (a ∘ e) id).row := hli.comp e e.injective
  exact ⟨a ∘ e, ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 h1)).ne_zero⟩

variable {T K : Type} [CommRing T] [Field K] {X : Scheme.{0}}

theorem isUnit_valH (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U))
    (hu : ⊤ ≤ w ⁻¹ᵁ X.basicOpen a) : IsUnit (valH w U h a) := by
  have hb := Scheme.basicOpen_appLE w ⊤ U h a
  rw [top_inf_eq] at hb
  rw [← hb] at hu
  refine IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom ?_
  exact (Spec (CommRingCat.of T)).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
    (Scheme.mem_basicOpen _ _ y hy).1 (hu hy)

theorem eq_of_valH_eq (p q : Sp T ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (hp : ⊤ ≤ p ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) (h : valH p U hp = valH q U hq) : p = q := by
  have e : p.appLE U ⊤ hp = q.appLE U ⊤ hq := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of T)).hom]
    exact CommRingCat.hom_ext h
  have hV := isAffineOpen_top (Spec (CommRingCat.of T))
  have : IsIso hV.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi hV.fromSpec, ← hU.SpecMap_appLE_fromSpec p hV hp, ← hU.SpecMap_appLE_fromSpec q hV hq, e]

theorem valH_cst_eq (f : X ⟶ Sp K) (p q : Sp T ⟶ X) (e : p ≫ f = q ≫ f) (U V : X.Opens) (hp : ⊤ ≤ p ⁻¹ᵁ U)
    (hq : ⊤ ≤ q ⁻¹ᵁ V) (c : K) : valH p U hp (AbLaw.cst f U c) = valH q V hq (AbLaw.cst f V c) := by
  have h1 := valT_appLE p f (U := ⊤) le_top hp ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)
  have h2 := valT_appLE q f (U := ⊤) le_top hq ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)
  rw [e, ← h2, valT_eq _ _ hp, valT_eq _ _ hq] at h1
  exact h1

theorem valH_rs (w : Sp T ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ w ⁻¹ᵁ V) (h' : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) :
    valH w V h (rs X hle a) = valH w U h' a :=
  (valT_eq w V h _).symm.trans ((valT_res w hle h a).trans (valT_eq w U h' a))

theorem exists_cutting (f : X ⟶ Sp K) {H : LB X} {m : ℕ} {s : Fin (m + 1) → LB.Sec H} (hs : VeryAmpleBy f H s)
    (p : Sp K ⟶ X) (hp : p ≫ f = 𝟙 _) (l : H.ι) (hl : ⊤ ≤ p ⁻¹ᵁ H.U l) :
    (∃ σ : LB.Sec H, valT p (H.U l) (σ.f l) ≠ 0) ∧
    ∃ t : Fin (m + 1) → LB.Sec H, (∀ j, valT p (H.U l) ((t j).f l) = 0) ∧
      ∀ w w' : Sp T ⟶ X, w ≫ f = w' ≫ f → (∀ U, ⊤ ≤ p ⁻¹ᵁ U → ⊤ ≤ w ⁻¹ᵁ U) → (∀ U, ⊤ ≤ p ⁻¹ᵁ U → ⊤ ≤ w' ⁻¹ᵁ U) →
        (∀ j, valT w (H.U l) ((t j).f l) = 0) → (∀ j, valT w' (H.U l) ((t j).f l) = 0) → w = w' := by
  let z : Spec (CommRingCat.of K) := (default : PrimeSpectrum K)
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show p z ∈ ⨆ i, Out.nonzeroLocus (s i) by rw [hs.1]; trivial)
  have hpa := (PointInterp.top_le_iff p _ z).2 ha
  obtain ⟨haff, r, hr, hsurj⟩ := hs.2 a
  have h0 := (top_le_nonzeroLocus_iff (s a) p l hl).1 hpa
  have hb := (valueAt_ne_zero_iff p _ hl _).1 h0
  have key : ∀ {T : Type} [CommRing T] (w : Sp T ⟶ X) (hwa : ⊤ ≤ w ⁻¹ᵁ Out.nonzeroLocus (s a))
      (hwl : ⊤ ≤ w ⁻¹ᵁ H.U l) (j) (c : K),
      valT w (H.U l) ((subMulSec f (s j) (s a) c).f l) =
        (valH w _ hwa (r j) - valH w _ hwa (AbLaw.cst f _ c)) * valH w _ hwl ((s a).f l) := by
    intro T _ w hwa hwl j c
    have hm : ⊤ ≤ w ⁻¹ᵁ (Out.nonzeroLocus (s a) ⊓ H.U l) := le_inf hwa hwl
    have e := congrArg (valH w _ hm) (hr j l)
    rw [map_mul, valH_rs w _ hm hwl, valH_rs w _ hm hwl, valH_rs w _ hm hwa] at e
    rw [valT_eq w _ hwl]
    change valH w _ hwl ((s j).f l - AbLaw.cst f _ c * (s a).f l) = _
    rw [map_sub, map_mul, e, sub_mul, valH_cst_eq f w w rfl _ _ hwl hwa]
  refine ⟨⟨s a, (valT_eq p _ hl _).trans_ne h0⟩,
    fun j => subMulSec f (s j) (s a) (valueAt p _ hpa (r j)), fun j => ?_, fun w w' e hw hw' h h' => ?_⟩
  · rw [key p hpa hl]
    exact mul_eq_zero_of_left (sub_eq_zero.2 (valueAt_cst f p hp _ hpa _).symm) _
  · have aux : ∀ (w : Sp T ⟶ X) (hw : ∀ U, ⊤ ≤ p ⁻¹ᵁ U → ⊤ ≤ w ⁻¹ᵁ U) (j) (c : K),
        valT w (H.U l) ((subMulSec f (s j) (s a) c).f l) = 0 →
        valH w _ (hw _ hpa) (r j) = valH w _ (hw _ hpa) (AbLaw.cst f _ c) := fun w hw j c h => by
      rw [key w (hw _ hpa) (hw _ hl)] at h
      exact sub_eq_zero.1 ((isUnit_valH w _ (hw _ hl) _ (hw _ hb)).mul_left_eq_zero.1 h)
    refine eq_of_valH_eq w w' haff (hw _ hpa) (hw' _ hpa) (RingHom.ext fun x => ?_)
    obtain ⟨F, rfl⟩ := hsurj x
    induction F using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.eval₂Hom_C, valH_cst_eq f w w' e]
    | add F G hF hG => rw [map_add, map_add, map_add, hF, hG]
    | mul_X F j hF =>
      rw [map_mul, MvPolynomial.eval₂Hom_X', map_mul, map_mul, hF, aux w hw j _ (h j), aux w' hw' j _ (h' j),
        valH_cst_eq f w w' e]

end GlobalTheory.VeryAmpleJet

open GlobalTheory.VeryAmpleJet GlobalTheory.KeyKa.EtBaseChange GlobalTheory.PointInterp in

theorem GlobalTheory.KeyKa.sections_separate_points_and_tangents : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (n : ℕ), 4 ≤ n → (∀ (z : Pt x) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → (∃ s₀ : RR x n, valT (T := K) z.left (x.P.L.U c) (s₀.f c) ≠ 0) ∧ ∃ s : Fin x.P.g → RR x n, (∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0) ∧ jac x s z c ≠ 0) ∧ ∀ (z z' : Pt x) (c c' : x.P.L.ι), z ≠ z' → ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → ⊤ ≤ z'.left ⁻¹ᵁ x.P.L.U c' → ∃ s₀ : RR x n, valT (T := K) z.left (x.P.L.U c) (s₀.f c) = 0 ∧ valT (T := K) z'.left (x.P.L.U c') (s₀.f c') ≠ 0 := by
  intro hL K _ x n hn
  obtain ⟨m, s, hs⟩ := veryAmpleBy_of_veryAmpleAt x.P.isLB (hL.ample _ x.P n hn).2 (𝟙 x.P.A.left)
    (Category.id_comp _) x.P.isLB (LBIso.chartPull (h := 𝟙 _) ⟨id, fun _ _ h => h, fun _ _ _ _ _ => rfl⟩
      (chartPullPull x.P.L (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl x.P.isLB))
  refine ⟨fun z c hc => ?_, fun z z' c c' hne hc hc' => ?_⟩
  · obtain ⟨h₀, t, ht, hcut⟩ := exists_cutting (T := DualNumber K) x.P.A.hom hs z.left (Over.w z) c hc
    refine ⟨h₀, ?_⟩
    obtain ⟨hex, htan, -⟩ := LieComb.lieComb_algebra K x.P.A x.P.g x.v x.basis.1
    choose w hw _ using hex
    obtain ⟨a, ha⟩ := exists_rows_det_ne_zero (Matrix.of fun j k => TrivSqZeroExt.snd
      (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * x.v k).left (x.P.L.U c) ((t j).f c))) fun d hd => by
        have hz : ∀ d : Fin x.P.g → K, (Matrix.of fun j k => TrivSqZeroExt.snd
            (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * x.v k).left (x.P.L.U c) ((t j).f c))).mulVec d = 0 →
            ∀ j, valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * w d).left (x.P.L.U c) ((t j).f c) = 0 :=
          fun d hd j => TrivSqZeroExt.ext ((fst_valT_translate z _ (htan _ _ (hw d)) hc _).trans (ht j))
            ((KaScale.snd_valT_comb x.basis.1 (hw d) z _ _).trans
              ((Finset.sum_congr rfl fun k _ => mul_comm _ _).trans (congrFun hd j)))
        have e := hcut ((toUnit (epsR K) ≫ z) * w d).left ((toUnit (epsR K) ≫ z) * w 0).left
          ((Over.w _).trans (Over.w _).symm) (fun U => translate_le z _ (htan _ _ (hw d)))
          (fun U => translate_le z _ (htan _ _ (hw 0))) (hz d hd) (hz 0 (Matrix.mulVec_zero _))
        have e' : w d = w 0 := mul_left_cancel (Over.OverMorphism.ext e)
        exact (x.basis.2 _ (htan _ _ (hw 0))).unique (e' ▸ hw d) (hw 0)
    exact ⟨fun i => t (a i), fun i => ht _, ha⟩
  · obtain ⟨σ, h₁, h₂⟩ := exists_separating x.P.A.hom (isLB_pw x.P.isLB n) hs z'.left z.left (Over.w z') (Over.w z)
      fun e => hne (Over.OverMorphism.ext e.symm)
    refine ⟨σ, (valT_eq (T := K) z.left _ hc _).trans ?_, (valT_eq (T := K) z'.left _ hc' _).trans_ne ?_⟩
    · exact not_not.1 fun h => h₂ ((top_le_nonzeroLocus_iff σ z.left c hc).2 h)
    · exact (top_le_nonzeroLocus_iff σ z'.left c' hc').1 h₁

end
end
