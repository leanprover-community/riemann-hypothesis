import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleVanishing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowAmple

theorem pw_pw_mul {X : Scheme.{0}} (H : LB X) (a b : ℤ) :
    GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw H a) b = GlobalTheory.AbLaw.pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem relAmple_pw : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left),
    L.IsLB → RelAmple B L → ∀ a : ℕ, 1 ≤ a → RelAmple B (GlobalTheory.AbLaw.pw L (a : ℤ)) := by
  intro R _ B L hL hA a ha
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 hA
  obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R B.left B.hom (GlobalTheory.AbLaw.pw L d) n s
    (GlobalTheory.AbLaw.isLB_pw hL d) hs a ha
  have e : GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d : ℤ)) (a : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ) := by
    rw [pw_pw_mul, pw_pw_mul, mul_comm]
  have h2 : ∃ t : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy B.hom _ t := by
    rw [← e]; exact ⟨s', hs'⟩
  obtain ⟨t, ht⟩ := h2
  exact GlobalTheory.Unif.relAmple_of_veryAmpleBy (GlobalTheory.AbLaw.isLB_pw hL a) hd t ht

end GlobalTheory.PowAmple
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_pos_pow_affine_base : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), L.IsLB → RelAmple B L → ∀ a : ℕ, 1 ≤ a → RelAmple B (GlobalTheory.AbLaw.pw L (a : ℤ)) := by
  atlas_forward_decl GlobalTheory.PowAmple.relAmple_pw
end

section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.ExactCoboundaryTriple

theorem exists_triple {κ : Type} [LinearOrder κ] {t : Finset κ} (ht : t.card = 3) :
    ∃ i j k, i < j ∧ j < k ∧ t = {i, j, k} := by
  refine ⟨t.orderEmbOfFin ht 0, t.orderEmbOfFin ht 1, t.orderEmbOfFin ht 2,
    (t.orderEmbOfFin ht).strictMono (by decide), (t.orderEmbOfFin ht).strictMono (by decide), ?_⟩
  ext x
  constructor
  · intro hx
    have : x ∈ Set.range (t.orderEmbOfFin ht) := by rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨m, rfl⟩ := this
    fin_cases m <;> simp
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem _ _ _

theorem totalD_triple {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (A : Cube.{0} κ R)
    (x : ∀ s, A.obj s) {i j k : κ} (hij : i < j) (hjk : j < k) :
    Cube.totalD A x {i, j, k} =
      Cube.res A (by intro; simp; tauto) (x {j, k}) - Cube.res A (by intro; simp; tauto) (x {i, k}) +
        Cube.res A (by intro; simp; tauto) (x {i, j}) := by
  have hik := hij.trans hjk
  have e1 : ({i, j, k} : Finset κ).erase i = {j, k} := by
    ext m; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact ⟨hij.ne', by tauto⟩
      · exact ⟨hik.ne', by tauto⟩
  have e2 : ({i, j, k} : Finset κ).erase j = {i, k} := by
    ext m; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact ⟨hij.ne, by tauto⟩
      · exact ⟨hjk.ne', by tauto⟩
  have e3 : ({i, j, k} : Finset κ).erase k = {i, j} := by
    ext m; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact ⟨hik.ne, by tauto⟩
      · exact ⟨hjk.ne, by tauto⟩
  have s1 : cubeSign ({i, j, k} : Finset κ) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [hij.le, hik.le])
  have s2 : cubeSign ({i, j, k} : Finset κ) j = -1 := by
    have h := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) hij
    rw [e1, cubeSign_eq_one_of_forall_le (by simp [hjk.le])] at h
    omega
  have s3 : cubeSign ({i, j, k} : Finset κ) k = 1 := by
    have h := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) hik
    have h' := cubeSign_erase_of_lt (t := {j, k}) (by simp) hjk
    rw [e1] at h
    rw [cubeSign_eq_one_of_forall_le (by
      intro m hm
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hm
      exact (hm.2.resolve_left hm.1).ge)] at h'
    omega
  rw [Cube.totalD_apply, Finset.sum_insert (by simp [hij.ne, hik.ne]), Finset.sum_pair hjk.ne,
    Cube.res_congr A x e1 _ (by intro; simp; tauto), Cube.res_congr A x e2 _ (by intro; simp; tauto),
    Cube.res_congr A x e3 _ (by intro; simp; tauto), s1, s2, s3]
  simp only [one_smul, neg_smul, sub_eq_add_neg, add_assoc]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X)

theorem coboundary_of_exact {κ : Type} [LinearOrder κ] (W : κ → X.Opens)
    (hW : (cechLB f M W).ExactAt (0 + 1)) (Φ : ∀ k l, SecOnR f M (W k ⊓ W l))
    (hΦ : ∀ k l m (O : X.Opens) (h₁ : O ≤ W k ⊓ W l) (h₂ : O ≤ W l ⊓ W m) (h₃ : O ≤ W k ⊓ W m),
      SecOnR.restrict f M h₁ (Φ k l) + SecOnR.restrict f M h₂ (Φ l m) = SecOnR.restrict f M h₃ (Φ k m)) :
    ∃ y : ∀ k, SecOnR f M (W k), ∀ k l (O : X.Opens) (h : O ≤ W k ⊓ W l),
      SecOnR.restrict f M h (Φ k l) =
        SecOnR.restrict f M (h.trans inf_le_right) (y l) - SecOnR.restrict f M (h.trans inf_le_left) (y k) := by
  classical
  have hle : ∀ {s : Finset κ} {i : κ}, i ∈ s → ⨅ j ∈ s, W j ≤ W i := fun {s i} hi => biInf_le W hi
  let x : ∀ s : Finset κ, SecOnR f M (⨅ j ∈ s, W j) := fun s =>
    if h : s.Nonempty then
      SecOnR.restrict f M (le_inf (hle (s.min'_mem h)) (hle (s.max'_mem h))) (Φ (s.min' h) (s.max' h))
    else 0
  have hcongr : ∀ {k l k' l' : κ} (_ : k = k') (_ : l = l') {O : X.Opens} (h : O ≤ W k ⊓ W l)
      (h' : O ≤ W k' ⊓ W l'), SecOnR.restrict f M h (Φ k l) = SecOnR.restrict f M h' (Φ k' l') := by
    rintro k l _ _ rfl rfl O h h'
    rfl
  have hx : ∀ {k l : κ} (_ : k < l), x {k, l} =
      SecOnR.restrict f M (le_inf (hle (by simp)) (hle (by simp))) (Φ k l) := by
    intro k l hkl
    have hn : ({k, l} : Finset κ).Nonempty := by simp
    simp only [x, dif_pos hn]
    exact hcongr (by simp [hkl.le]) (by simp [hkl.le]) _ _
  have hE := (cechComplex_exactAt_succ_iff (secCube f M W) 0).1 hW
  have hd : Cube.d (secCube f M W) (0 + 2) (fun s => x s.1) = 0 := by
    funext t
    rw [Cube.d_apply_eq_totalD (secCube f M W) _ x (fun _ => rfl)]
    obtain ⟨t, ht⟩ := t
    obtain ⟨i, j, k, hij, hjk, rfl⟩ := exists_triple ht
    refine (totalD_triple (secCube f M W) x hij hjk).trans ?_
    rw [hx hij, hx hjk, hx (hij.trans hjk)]
    simp only [res_secCube]
    erw [SecOnR.restrict_restrict, SecOnR.restrict_restrict, SecOnR.restrict_restrict]
    rw [← hΦ i j k _ (le_inf (hle (by simp)) (hle (by simp))) (le_inf (hle (by simp)) (hle (by simp)))]
    change (_ : SecOnR f M _) = 0
    abel
  obtain ⟨z, hz⟩ := (hE _).1 hd
  have hs : ∀ k, W k ≤ ⨅ j ∈ ({k} : Finset κ), W j := fun k => by simp
  let y : ∀ k, SecOnR f M (W k) := fun k => SecOnR.restrict f M (hs k) (z ⟨{k}, Finset.card_singleton k⟩)
  have hlt : ∀ k l, k < l → ∀ (O : X.Opens) (h : O ≤ W k ⊓ W l),
      SecOnR.restrict f M h (Φ k l) =
        SecOnR.restrict f M (h.trans inf_le_right) (y l) - SecOnR.restrict f M (h.trans inf_le_left) (y k) := by
    intro k l hkl O h
    have hO : O ≤ ⨅ j ∈ ({k, l} : Finset κ), W j := by
      simp only [Finset.mem_insert, Finset.mem_singleton, le_iInf_iff]
      rintro j (rfl | rfl)
      · exact h.trans inf_le_left
      · exact h.trans inf_le_right
    have e := (congrFun hz ⟨{k, l}, Finset.card_pair hkl.ne⟩).symm.trans
      (Cube.d_one_apply_pair (secCube f M W) z hkl)
    have e' := congrArg (SecOnR.restrict f M hO) ((hx hkl).symm.trans e)
    simp only [res_secCube] at e'
    erw [map_sub, SecOnR.restrict_restrict, SecOnR.restrict_restrict, SecOnR.restrict_restrict] at e'
    exact e'.trans (congrArg₂ (· - ·) (SecOnR.restrict_restrict f (hs l) _ _).symm
      (SecOnR.restrict_restrict f (hs k) _ _).symm)
  have h0 : ∀ k (O : X.Opens) (h : O ≤ W k ⊓ W k), SecOnR.restrict f M h (Φ k k) = 0 := fun k O h =>
    add_eq_left.1 (hΦ k k k O h h h)
  refine ⟨y, fun k l O h => ?_⟩
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · exact hlt k l hkl O h
  · rw [h0, sub_self]
  · have h' : O ≤ W l ⊓ W k := le_inf (h.trans inf_le_right) (h.trans inf_le_left)
    have e := hΦ k l k O h h' (le_inf (h.trans inf_le_left) (h.trans inf_le_left))
    rw [h0, hlt l k hkl O h'] at e
    rw [eq_neg_of_add_eq_zero_left e, neg_sub]

theorem coboundary_of_refine {I κ : Type} (V : I → X.Opens) (W : κ → X.Opens) (hW : ⨆ k, W k = ⊤) (r : κ → I)
    (hr : ∀ k, W k ≤ V (r k)) (Φ : ∀ a b, SecOnR f M (V a ⊓ V b))
    (hΦ : ∀ a b d (O : X.Opens) (h₁ : O ≤ V a ⊓ V b) (h₂ : O ≤ V b ⊓ V d) (h₃ : O ≤ V a ⊓ V d),
      SecOnR.restrict f M h₁ (Φ a b) + SecOnR.restrict f M h₂ (Φ b d) = SecOnR.restrict f M h₃ (Φ a d))
    (y : ∀ k, SecOnR f M (W k))
    (hy : ∀ k l (O : X.Opens) (h : O ≤ W k ⊓ W l),
      SecOnR.restrict f M (h.trans (inf_le_inf (hr k) (hr l))) (Φ (r k) (r l)) =
        SecOnR.restrict f M (h.trans inf_le_right) (y l) - SecOnR.restrict f M (h.trans inf_le_left) (y k)) :
    ∃ Ψ : ∀ a, SecOnR f M (V a), ∀ a b, Φ a b =
      SecOnR.restrict f M inf_le_left (Ψ a) - SecOnR.restrict f M inf_le_right (Ψ b) := by
  have hcov : ∀ U : X.Opens, U ≤ ⨆ k, U ⊓ W k := fun U => by
    rw [← inf_iSup_eq, hW, inf_top_eq]
  have hg : ∀ a, ∃ t : SecOnR f M (V a), ∀ k, SecOnR.restrict f M (inf_le_left : V a ⊓ W k ≤ V a) t =
      SecOnR.restrict f M (inf_le_inf_left _ (hr k)) (Φ a (r k)) -
        SecOnR.restrict f M inf_le_right (y k) := by
    intro a
    refine (SecOnR.existsUnique_glue f (fun k => V a ⊓ W k) (fun _ => inf_le_left) (hcov _) _ ?_).exists
    intro k l
    simp only [map_sub, SecOnR.restrict_restrict]
    have h : V a ⊓ W k ⊓ (V a ⊓ W l) ≤ W k ⊓ W l := inf_le_inf inf_le_right inf_le_right
    rw [← hΦ a (r k) (r l) _ (inf_le_left.trans (inf_le_inf_left _ (hr k)))
      (h.trans (inf_le_inf (hr k) (hr l))), hy k l _ h]
    abel
  choose Ψ hΨ using hg
  refine ⟨Ψ, fun a b => SecOnR.ext_of_cover f (fun k => V a ⊓ V b ⊓ W k) (fun _ => inf_le_left) (hcov _)
    fun k => ?_⟩
  have ea := congrArg (SecOnR.restrict f M (inf_le_inf_right _ inf_le_left :
    V a ⊓ V b ⊓ W k ≤ V a ⊓ W k)) (hΨ a k)
  have eb := congrArg (SecOnR.restrict f M (inf_le_inf_right _ inf_le_right :
    V a ⊓ V b ⊓ W k ≤ V b ⊓ W k)) (hΨ b k)
  simp only [map_sub, SecOnR.restrict_restrict] at ea eb ⊢
  rw [ea, eb, ← hΦ a b (r k) _ inf_le_left (inf_le_inf inf_le_right (hr k))]
  abel

theorem exists_affine_refinement [CompactSpace X] {I : Type} (V : I → X.Opens) (hV : ⨆ a, V a = ⊤) :
    ∃ (n : ℕ) (W : Fin n → X.Opens) (r : Fin n → I), (∀ k, IsAffineOpen (W k)) ∧ ⨆ k, W k = ⊤ ∧
      ∀ k, W k ≤ V (r k) := by
  classical
  have h : ∀ x : X, ∃ (a : I) (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧ U ≤ V a := by
    intro x
    have hx : x ∈ ⨆ a, V a := by rw [hV]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨U, hU, hxU, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens ha
    exact ⟨a, U, hU, hxU, hle⟩
  choose c U hU hxU hle using h
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨T.card, fun k => U (T.equivFin.symm k), fun k => c (T.equivFin.symm k), fun _ => hU _, ?_,
    fun _ => hle _⟩
  refine top_unique fun x _ => ?_
  obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨p, hp⟩, ?_⟩
  simpa using hx

theorem firstCohomologyVanishes_of_isRelAcyclic (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R))
    (M : LB X) (hM : M.IsLB) (hX : CompactSpace X) (h : GlobalTheory.CxForm.IsRelAcyclic f f M) : FirstCohomologyVanishes M := by
  intro I V c hV hc φ hφ
  obtain ⟨n, W, r, hW, hWc, hr⟩ := exists_affine_refinement V hc
  let Φ : ∀ a b, SecOnR f M (V a ⊓ V b) := fun a b =>
    (SecOn.chart hM (c a) (inf_le_left.trans (hV a))).symm (φ a b)
  have hch : ∀ a b (O : X.Opens) (h₁ : O ≤ V a ⊓ V b),
      SecOn.chart hM (c a) (h₁.trans (inf_le_left.trans (hV a))) (SecOnR.restrict f M h₁ (Φ a b)) =
        rs X h₁ (φ a b) := fun a b O h₁ =>
    (SecOn.chart_restrict hM (c a) (inf_le_left.trans (hV a)) h₁ (Φ a b)).trans
      (congrArg _ (LinearEquiv.apply_symm_apply _ _))
  have hΦ : ∀ a b d (O : X.Opens) (h₁ : O ≤ V a ⊓ V b) (h₂ : O ≤ V b ⊓ V d) (h₃ : O ≤ V a ⊓ V d),
      SecOnR.restrict f M h₁ (Φ a b) + SecOnR.restrict f M h₂ (Φ b d) = SecOnR.restrict f M h₃ (Φ a d) := by
    intro a b d O h₁ h₂ h₃
    have ha : O ≤ M.U (c a) := h₁.trans (inf_le_left.trans (hV a))
    have hb : O ≤ M.U (c b) := h₂.trans (inf_le_left.trans (hV b))
    apply (SecOn.chart hM (c a) ha).injective
    have e := congrArg (rs X (le_inf h₁ (h₂.trans inf_le_right) : O ≤ V a ⊓ V b ⊓ V d)) (hφ a b d)
    simp only [map_add, map_mul, rs_rs] at e
    refine ((SecOn.chart hM (c a) ha).map_add _ _).trans ?_
    refine Eq.trans ?_ (e.trans (hch a d O h₃).symm)
    exact congrArg₂ (· + ·) (hch a b O h₁) ((SecOn.chart_change hM (c a) (c b) ha hb _).trans
      (congrArg (rs X (le_inf ha hb) (M.g (c a) (c b)).val * ·) (hch b d O h₂)))
  obtain ⟨y, hy⟩ := coboundary_of_exact f M W (h ⊤ (isAffineOpen_top _) (Fin n) W hW (by rw [hWc]; rfl) 0)
    (fun k l => SecOnR.restrict f M (inf_le_inf (hr k) (hr l)) (Φ (r k) (r l)))
    (fun k l m O h₁ h₂ h₃ => by
      simp only [SecOnR.restrict_restrict]
      exact hΦ _ _ _ _ _ _ _)
  obtain ⟨Ψ, hΨ⟩ := coboundary_of_refine f M V W hWc r hr Φ hΦ y (fun k l O hO => by
    simpa only [SecOnR.restrict_restrict] using hy k l O hO)
  refine ⟨fun a => SecOn.chart hM (c a) (hV a) (Ψ a), fun a b => ?_⟩
  have ha : V a ⊓ V b ≤ M.U (c a) := inf_le_left.trans (hV a)
  have hb : V a ⊓ V b ≤ M.U (c b) := inf_le_right.trans (hV b)
  have e := congrArg (SecOn.chart hM (c a) ha) (hΨ a b)
  refine ((LinearEquiv.apply_symm_apply _ _).symm.trans e).trans ?_
  refine ((SecOn.chart hM (c a) ha).map_sub _ _).trans ?_
  exact congrArg₂ (· - ·) (SecOn.chart_restrict hM (c a) (hV a) inf_le_left (Ψ a))
    ((SecOn.chart_change hM (c a) (c b) ha hb _).trans
      (congrArg (rs X (le_inf ha hb) (M.g (c a) (c b)).val * ·)
        (SecOn.chart_restrict hM (c b) (hV b) inf_le_right (Ψ b))))

end GlobalTheory.ExactCoboundaryTriple
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → CompactSpace X → GlobalTheory.CxForm.IsRelAcyclic f f M → GlobalTheory.AbLaw.FirstCohomologyVanishes M := by
  first
  | exact @_root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic
  | exact _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic
  | (apply _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic ..)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCohomologyVanishes_of_isRelAcyclic_over_spec : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → CompactSpace X → GlobalTheory.CxForm.IsRelAcyclic f f M → GlobalTheory.AbLaw.FirstCohomologyVanishes M := by
  atlas_forward_decl GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw.SecBC

open GlobalTheory.AbLaw in

theorem GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar
    (hV : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B]
      (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → FirstCohomologyVanishes (pw M (a : ℤ)))
    (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hA : IsAbelianScheme A)
    (hL : L.IsLB) (hAm : RelAmple A L) (a : ℕ) (ha : 1 ≤ a) (T : Over S) (K : Type) [Field K] [IsAlgClosed K]
    (q : Spec (CommRingCat.of K) ⟶ T.left) :
    ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)),
      IsPullback π f' (fst T A).left q ∧ FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) := by
  let s : Spec (CommRingCat.of K) ⟶ S := q ≫ T.hom
  let AK : Over (Spec (CommRingCat.of K)) := (Over.pullback s).obj A
  let g : AK.left ⟶ A.left := pullback.fst A.hom s
  have hg : IsPullback g AK.hom A.hom s := IsPullback.of_hasPullback A.hom s
  let M : LB AK.left := L.pull g
  have hM : M.IsLB := LB.isLB_pull hL g
  have hAK : IsAbelianScheme AK := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := s (default : PrimeSpectrum K)) trivial
  have hsub : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hMA : RelAmple AK M := ReciprocityTheory.ChartRestriction.G.Geo.Tor.relAmple_pull (w := ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso M) hg hL hM
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hM)) U hU
    (fun y => by rwa [Subsingleton.elim y (default : PrimeSpectrum K)]) hAm
  have hK := hV K AK M hAK hM hMA a ha
  have H := isPullback_snd A T
  let π : AK.left ⟶ (T ⊗ A).left := H.lift g (AK.hom ≫ q) (by rw [hg.w, Category.assoc])
  have e₁ : π ≫ (snd T A).left = g := H.lift_fst _ _ _
  have e₂ : π ≫ (fst T A).left = AK.hom ≫ q := H.lift_snd _ _ _
  refine ⟨AK.left, π, AK.hom, IsPullback.of_right (by rw [e₁]; exact hg) e₂ H, ?_⟩
  refine h1Zero_of_isIso _ _ (𝟙 _) (pw M a) _ inferInstance (isLB_pw hM _)
    (LB.isLB_pull (LB.isLB_linComb hL _ _) π) ?_ hK
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (chartOut L (fun _ : Fin 1 => (snd T A).left) (fun _ => (a : ℤ)) π
    (fun _ => 𝟙 _ ≫ g) fun _ => by rw [e₁, Category.id_comp]) (chartPw M a)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm (ReciprocityTheory.ChartRestriction.G.Geo.Tor.iso_linComb
      ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hM))
      (fun _ : Fin 1 => 𝟙 _) (fun _ => (a : ℤ))))

theorem GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all : ((∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ))) → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π)) := by
  intro hV S A _ _ L hA hL hAm a ha T K _ _ q
  exact GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar hV S A L hA hL hAm a ha T K q
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundlePow_h1Vanishes_geometricFibre_all : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ))) → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) := by
  atlas_forward_decl GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AmpleSecBC

open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecBC

theorem isProjBy_of_openImmersion {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hA : RelAmple A L) {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion t] :
    IsProjBy (R := R) (fst (Over.mk t) A).left := by
  have hpb := isPullback_snd A (Over.mk t)
  have hL' : (L.pull (snd (Over.mk t) A).left).IsLB := LB.isLB_pull hL _
  have hR : RelAmple (Over.mk (fst (Over.mk t) A).left) (L.pull (snd (Over.mk t) A).left) :=
    relAmple_pull (A' := Over.mk (fst (Over.mk t) A).left) (f := t) hpb hL hL'
      ((isGen_iff _).1 (idIso_isGen hL')) t.opensRange (isAffineOpen_opensRange t) (fun y => ⟨y, rfl⟩) hA
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R _ _ hL').1 hR
  exact ⟨_, isLB_pw hL' d, n, s, hs⟩

theorem fieldVanishing : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ)) := by
  intro K _ _ B _ _ M hB hM hA a ha
  have hM' := isLB_pw hM (a : ℤ)
  have hR := GlobalTheory.T.relAmple_pos_pow_affine_base K B M hM hA a ha
  have hP : IsProper B.hom := hB.proper
  have : CompactSpace B.left := by
    have : QuasiCompact B.hom := inferInstance
    exact (quasiCompact_iff_compactSpace B.hom).1 this
  exact GlobalTheory.T.firstCohomologyVanishes_of_isRelAcyclic_over_spec K B.left B.hom _ hM' this (GlobalTheory.AmpleGen.ampleVanishing K B hB _ hM' hR)

theorem geomVanishing : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) :=
  GlobalTheory.T.lineBundlePow_h1Vanishes_geometricFibre_all fieldVanishing

theorem secBaseChange_relAmple : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Rigidified A L → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ p : S, ∃ V : S.Opens, p ∈ V ∧ ∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (a : ℤ) (overRes (T := baseOver S) V))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left) (b' : Fin m → LB.Sec (LPow A L (a : ℤ) (baseAt t))), (∀ i, IsPullSec A L (a : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (a : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (a : ℤ) (baseAt t))) = ⊤ := by
  have hB := geomVanishing
  intro S _ A _ _ L hAb hL _ hAmp a ha p
  obtain ⟨R₀, t₀, hto, ⟨q, rfl⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := p) (U := ⊤) trivial
  obtain ⟨R, _⟩ := R₀
  change Spec (CommRingCat.of R) ⟶ S at t₀
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := isLocallyNoetherian_of_isOpenImmersion t₀
  have : IsNoetherianRing R := by
    have : AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of R)) := {}
    exact (isNoetherian_Spec (R := CommRingCat.of R)).1 this
  have hpb := isPullback_snd A (Over.mk t₀)
  have hfl : Flat (fst (Over.mk t₀) A).left := by
    have : Smooth A.hom := hAb.smooth
    exact MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have hpr := isProjBy_of_openImmersion A L hL hAmp t₀
  obtain ⟨F⟩ := nonempty_perf_of_noetherian R _ _ hfl hpr (LPow A L (a : ℤ) (Over.mk t₀)) (LB.isLB_linComb hL _ _)
  obtain ⟨K, _, _, g₀, hg₀⟩ := exists_geomPoint (R := R) q
  obtain ⟨X', π, f', hX', hH⟩ := hB S A L hAb hL hAmp a ha (Over.mk t₀) K (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨r, m, B, hr, hB', hu⟩ := GlobalTheory.exists_matrix_basis_ker_of_exact_at_point R K g₀ _ _ _ F.D₀ F.D₁ F.comp
    (F.exact K g₀ X' π f' hX' hH)
  have aff : ∀ {R' : Type} [CommRing R'] (t : Spec (CommRingCat.of R') ⟶ S), IsAffine (Over.mk t).left :=
    fun {R'} _ _ => inferInstanceAs (IsAffine (Spec (CommRingCat.of R')))
  have := aff t₀
  have ex : ∀ i, ∃ s, RepAt F (𝟙 (Over.mk t₀)) (fun k => cfun (𝟙 (Over.mk t₀)) (B k i)) s := fun i =>
    (repAt_main (F := F) (𝟙 (Over.mk t₀))).1 _ (by
      have e := congrArg (fun Q => Q.map (cfun (𝟙 (Over.mk t₀)))) hB'
      simp only [Matrix.map_mul] at e
      funext l
      exact (congrFun (congrFun e l) i).trans (map_zero (cfun (𝟙 (Over.mk t₀)))))
  choose b₀ hb₀ using ex
  let D : (Spec (CommRingCat.of R)).Opens :=
    (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have hq : q ∈ D := by
    have : D = PrimeSpectrum.basicOpen r := basicOpen_eq_of_affine (R := CommRingCat.of R) r
    rw [this]
    exact fun hq => hr (hg₀ r hq)
  let l : (t₀ ''ᵁ D).toScheme ⟶ Spec (CommRingCat.of R) := IsOpenImmersion.lift t₀ (t₀ ''ᵁ D).ι (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩)
  have hl : l ≫ t₀ = (t₀ ''ᵁ D).ι := IsOpenImmersion.lift_fac _ _ _
  have hlD : ∀ y, l y ∈ D := fun y => by
    obtain ⟨x, hx, e⟩ := y.2
    have : t₀ (l y) = t₀ x := (congrArg (fun Q => Q y) hl).trans e.symm
    rw [t₀.isOpenEmbedding.injective this]
    exact hx
  let hD : overRes (T := baseOver S) (t₀ ''ᵁ D) ⟶ Over.mk t₀ := Over.homMk l (hl.trans (Category.comp_id _).symm)
  choose b hb using fun i => exists_pullSec A L (a : ℤ) hD (b₀ i)
  refine ⟨t₀ ''ᵁ D, ⟨q, hq, rfl⟩, m, b, fun R' _ t b' hb' => ?_⟩
  have : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R')))
  refine basis_of_rep (F := F) (homAt t ≫ hD ≫ 𝟙 _) B hB' (hu _ _ ?_) b'
    fun i => ((hb₀ i).pull hD (hb i)).pull (homAt t) (hb' i)
  refine (baseAt t).left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ?_
  refine ((baseAt t).left.mem_basicOpen _ y hy).1 ?_
  have := Scheme.preimage_basicOpen_top (homAt t ≫ hD ≫ 𝟙 _).left ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  exact (congrArg (y ∈ ·) this).mp (hlD (t y))

end GlobalTheory.AmpleSecBC
end
end
