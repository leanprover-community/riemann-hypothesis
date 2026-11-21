import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import BuildAid.ForwardExisting

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.CubeGen

section Field

variable {F : Type} [Field F] {X : Scheme.{0}}

theorem toStk_surjective (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

def ev (z : Sp F) : (Sp F).presheaf.stalk z ≃+* F :=
  (RingEquiv.ofBijective (toStk z) ⟨(toStk z).injective, toStk_surjective z⟩).symm

theorem ev_gs (x : Sp F ⟶ X) (z : Sp F) {U : X.Opens} (h : x z ∈ U) (f : Γ(X, U)) :
    ev z (gs x z U f) = valF x U f := by
  refine (RingEquiv.symm_apply_eq _).2 ?_
  have h' := (top_le_iff_mem x U z).2 h
  rw [valF, dif_pos h', gs_eq x z U h]
  show _ = ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _))
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE h') z trivial _).symm

theorem ev_gm (x : Sp F ⟶ X) (z : Sp F) {U : X.Opens} (h : x z ∈ U) (f : Γ(X, U)ˣ) :
    ev z (gm x z U f).val = valF x U f.val := by
  rw [← gs_unit x z U h, ev_gs x z h]

theorem range_subset_iff (x : Sp F ⟶ X) (z : Sp F) (U : Set X) : Set.range x ⊆ U ↔ x z ∈ U := by
  refine ⟨fun h => h ⟨z, rfl⟩, fun h => ?_⟩
  rintro _ ⟨y, rfl⟩
  rwa [Subsingleton.elim (α := PrimeSpectrum F) y z]

end Field

section Sections

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem isUnit_gs_iff (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine ((Z.mem_basicOpen ((r.app U).hom a) z h).symm).trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem gs_sec (θ : LB.Sec L) (r : Z ⟶ X) (z : Z) {i j : L.ι} (hi : r z ∈ L.U i) (hj : r z ∈ L.U j) :
    gs r z _ (θ.f i) = (gm r z _ (L.g i j)).val * gs r z _ (θ.f j) := by
  have hm : r z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have e := congrArg (gs r z _) (θ.compat i j)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm] at e

theorem mem_nonzeroLocus_iff (θ : LB.Sec L) (r : Z ⟶ X) (z : Z) {k : L.ι}
    (hk : r z ∈ L.U k) : r z ∈ Out.nonzeroLocus θ ↔ IsUnit (gs r z _ (θ.f k)) := by
  rw [isUnit_gs_iff r z _ hk]
  refine ⟨fun h => ?_, fun h => TopologicalSpace.Opens.mem_iSup.2 ⟨k, h⟩⟩
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hj' : r z ∈ L.U j := X.basicOpen_le _ hj
  rw [← isUnit_gs_iff r z _ hk, gs_sec θ r z hk hj']
  exact (Units.isUnit _).mul ((isUnit_gs_iff r z _ hj' _).2 hj)

theorem exists_gen_of_sec (θ : LB.Sec L) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : ∀ k y, φ k y ∈ Out.nonzeroLocus θ) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      ∃ u : K → (Z.presheaf.stalk z)ˣ, (∀ k, (u k).val = gs (r ≫ φ k) z _ (θ.f (J (r ≫ φ k)))) ∧
        val t r z J = ∏ k, u k ^ ε k := by
  let f : ∀ (j : K → L.ι) (k : K), Γ(Y, LB.wchart L φ j) := fun j k =>
    (Y.presheaf.map (homOfLE (LB.wchart_le L φ j k)).op).hom (((φ k).app _).hom (θ.f (j k)))
  have hf : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j k, r z ∈ LB.wchart L φ j →
      gs r z _ (f j k) = gs (r ≫ φ k) z _ (θ.f (j k)) := fun Z r z j k hz =>
    (gs_res r z _ hz _).trans (gs_pull r (φ k) z _ (LB.wchart_le L φ j k hz) _)
  have hu : ∀ j k, IsUnit (f j k) := fun j k => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have e := hf _ (𝟙 Y) y j k hy
    have := (mem_nonzeroLocus_iff θ (𝟙 Y ≫ φ k) y (LB.wchart_le L φ j k hy)).1 (h k y)
    rw [← e, gs_eq _ y _ hy] at this
    exact this
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j k, r z ∈ LB.wchart L φ j →
      (gm r z _ (hu j k).unit).val = gs (r ≫ φ k) z _ (θ.f (j k)) := fun Z r z j k hz =>
    (gs_unit r z _ hz _).symm.trans (hf Z r z j k hz)
  have hp : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j,
      gm r z (LB.wchart L φ j) (∏ k, (hu j k).unit ^ ε k) = ∏ k, gm r z _ (hu j k).unit ^ ε k := fun Z r z j => by
    simp only [map_prod, map_zpow]
  refine ⟨⟨fun j => ∏ k, (hu j k).unit ^ ε k⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z J hJ =>
    ⟨fun k => gm r z _ (hu (fun k => J (r ≫ φ k)) k).unit, fun k => hv Z r z _ k (hJ.mem φ r), hp Z r z _⟩⟩
  refine ((gm_res _ y _ hy _).trans (hp _ _ y j)).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res _ y _ hy _).trans (hp _ _ y j'))).trans ?_)))
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow]
  congr 1
  apply Units.ext
  rw [Units.val_mul, hv _ (𝟙 Y) y j k hy.1, hv _ (𝟙 Y) y j' k hy.2]
  exact (gs_sec θ _ y (LB.wchart_le L φ j k hy.1) (LB.wchart_le L φ j' k hy.2)).symm

end Sections

section Norms

variable {X Y Y' : Scheme.{0}} {L : LB X} {ν : Nrm L} {p : ℕ} [Fact p.Prime] {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {z : Sp (PadicAlgCl p)} {J : (Sp (PadicAlgCl p) ⟶ X) → L.ι}

def nv (ν : Nrm L) (t : LB.Gen (LB.LinComb L φ ε)) (q : Sp (PadicAlgCl p) ⟶ Y) (z : Sp (PadicAlgCl p))
    (J : (Sp (PadicAlgCl p) ⟶ X) → L.ι) : ℝ :=
  ‖ev z (val t q z J).val‖ * ∏ k, ν p (q ≫ φ k) (J (q ≫ φ k)) ^ ε k

theorem norm_ev_prod (u : K → ((Sp (PadicAlgCl p)).presheaf.stalk z)ˣ) :
    ‖ev z (∏ k, u k ^ ε k).val‖ = ∏ k, ‖ev z (u k).val‖ ^ ε k := by
  have e : ∀ v : ((Sp (PadicAlgCl p)).presheaf.stalk z)ˣ,
      ev z v.val = (Units.map (ev z).toMonoidHom v).val := fun _ => rfl
  rw [e, map_prod, Units.coe_prod, norm_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, norm_zpow, e]

theorem normOne_iff (hν : IsNrm L ν) (hJ : Good L z J) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (q : Sp (PadicAlgCl p) ⟶ Y) : NormOne ν t q ↔ nv ν t q z J = 1 := by
  have hm := hJ.mem φ q
  refine ⟨fun h => ?_, fun h j hj => ?_⟩
  · exact (congrArg (fun a => ‖a‖ * _) (ev_gm q z hm _)).trans (h _ ((range_subset_iff q z _).2 hm))
  · have hj' : q z ∈ LB.wchart L φ j := (range_subset_iff q z _).1 hj
    refine Eq.trans ?_ h
    have e : gm q z (LB.wchart L φ j) (t.s j) = _ * val t q z J := gen_trans ht q z hj' hm
    refine (congrArg (fun a => ‖a‖ * _) ((ev_gm q z hj' _).symm.trans (congrArg (fun a => ev z a.val) e))).trans ?_
    rw [nv, Units.val_mul, map_mul, norm_mul, trF, norm_ev_prod, mul_right_comm,
      mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have a : (q ≫ φ k) z ∈ L.U (j k) := Set.mem_iInter.1 hj' k
    have b := hJ (q ≫ φ k)
    rw [← mul_zpow, ev_gm (q ≫ φ k) z (U := L.U (j k) ⊓ L.U (J (q ≫ φ k))) ⟨a, b⟩,
      hν.trans p _ _ _ ((range_subset_iff _ z _).2 a) ((range_subset_iff _ z _).2 b)]

theorem nv_mul (hJ : Good L z J) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (q : Sp (PadicAlgCl p) ⟶ Y) : nv ν (LB.mulGen L φ ε φ' ε' t t') q z J = nv ν t q z J * nv ν t' q z J := by
  rw [nv, val_mul hJ, Units.val_mul, map_mul, norm_mul, Fintype.prod_sum_type, _root_.mul_mul_mul_comm]
  rfl

theorem nv_pull (hJ : Good L z J) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (q : Sp (PadicAlgCl p) ⟶ Y') : nv ν (LB.pullGen L φ ε t h) q z J = nv ν t (q ≫ h) z J := by
  rw [nv, val_pull hJ, nv]
  simp only [Category.assoc]

theorem nv_form (hν : IsNrm L ν) (h : FormEq φ ε φ' ε') {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (q : Sp (PadicAlgCl p) ⟶ Y) (e : val t' q z J = val t q z J) :
    nv ν t' q z J = nv ν t q z J := by
  have := congrArg Units.val (h ℝˣ fun ψ => Units.mk0 (ν p (q ≫ ψ) (J (q ≫ ψ))) (hν.pos p _ _).ne')
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_mk0] at this
  rw [nv, nv, e, this]

end Norms

section Cube

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']

def six {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} (x b c : T ⟶ G) : Fin 6 → (T ⟶ G) :=
  ![x * b, x * c, b * c, x * b * c, b, c]

theorem six_map {T : Over S} {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) (x b c : T' ⟶ G') (i : Fin 6) :
    ρ (six x b c i) = six (ρ x) (ρ b) (ρ c) i := by
  fin_cases i <;> simp [six]

theorem six_comp {T T' : Over S} (r : T'.left ⟶ T.left) (x b c : T ⟶ G) (x' b' c' : T' ⟶ G)
    (hx : x'.left = r ≫ x.left) (hb : b'.left = r ≫ b.left) (hc : c'.left = r ≫ c.left) (i : Fin 6) :
    (six x' b' c' i).left = r ≫ (six x b c i).left := by
  let ρ : T' ⟶ T := Over.homMk r (by rw [← Over.w x, ← Category.assoc, ← hx, Over.w])
  have e := six_map (preHom (G := G) ρ) x b c i
  rw [show preHom ρ x = x' from Over.OverMorphism.ext hx.symm, show preHom ρ b = b' from Over.OverMorphism.ext hb.symm,
    show preHom ρ c = c' from Over.OverMorphism.ext hc.symm] at e
  rw [← e]
  rfl

theorem six_push {f : S' ⟶ S} {a : G'.left ⟶ G.left} (h : IsGrpPullback G' G f a) {T : Over S} {T' : Over S'}
    (r : T'.left ⟶ T.left) (x b c : T ⟶ G) (x' b' c' : T' ⟶ G')
    (hx : x'.left ≫ a = r ≫ x.left) (hb : b'.left ≫ a = r ≫ b.left) (hc : c'.left ≫ a = r ≫ c.left) (i : Fin 6) :
    (six x' b' c' i).left ≫ a = r ≫ (six x b c i).left :=
  (congrArg (fun q => q.left) (six_map (pushHom h T') x' b' c' i)).trans
    (six_comp (T' := Over.mk (T'.hom ≫ f)) r x b c _ _ _ hx hb hc i)

theorem exists_gen_cube (L : RigLB G) (cub : CubicalStr G L) (θ : LB.Sec L.L) {T : Over S} (x b c : T ⟶ G)
    (h : ∀ i y, (six x b c i).left y ∈ Out.nonzeroLocus θ) :
    ∃ g : LB.Gen (L.L.pull x.left), g.IsGen ∧ ∀ ν : Nrm L.L, IsNrm L.L ν → ∀ (p : ℕ) [Fact p.Prime]
      (q : Sp (PadicAlgCl p) ⟶ T.left) (δ : ℝ), 0 < δ → NormOne ν L.rig (q ≫ T.hom) →
      NormOne (φ := thφ G (x3 G)) (ε := thε) ν cub.t (q ≫ (lift x (lift b c)).left) →
      (∀ i j, Set.range (q ≫ (six x b c i).left) ⊆ L.L.U j →
        ‖valF (q ≫ (six x b c i).left) _ (θ.f j)‖ * ν p (q ≫ (six x b c i).left) j = δ) → NormOne ν g q := by
  obtain ⟨t, ht, hv⟩ := exists_gen_of_sec θ (fun i => (six x b c i).left) ![1, 1, 1, -1, -1, -1] h
  let t₁ := LB.pullGen L.L (thφ G (x3 G)) thε cub.t (lift x (lift b c)).left
  let t₂ := LB.pullGen L.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig T.hom
  have e0 : T.hom ≫ eSec G = (1 : T ⟶ G).left := by
    show _ = (toUnit _ ≫ η[G]).left
    simp [eSec]
  have F : FormEq (Sum.elim (Sum.elim (fun k => (lift x (lift b c)).left ≫ thφ G (x3 G) k)
      (fun i => (six x b c i).left)) (fun _ : PUnit => T.hom ≫ eSec G))
      (Sum.elim (Sum.elim thε ![1, 1, 1, -1, -1, -1]) (fun _ => 1)) (fun _ : PUnit => x.left) (fun _ => 1) := by
    intro U _ f
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [prod_cub x b c f, e0]
    apply Additive.ofMul.injective
    simp [Fin.prod_univ_succ, six, ofMul_mul, ofMul_inv]
    abel
  obtain ⟨g, hg, hgv⟩ := exists_gen L.isLB F (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ t₁ t) t₂)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cub.isGen _) ht)
      (DVR.pullGen_isGen _ _ _ _ L.rigGen _))
  refine ⟨g, hg, fun ν hν p _ q δ hδ hr hc hθ => ?_⟩
  let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  choose J hJ using fun χ : Sp (PadicAlgCl p) ⟶ G.left => exists_chart L.isLB (χ z)
  have hJ' : Good L.L z J := hJ
  have n₁ : nv ν t₁ q z J = 1 := (nv_pull hJ' _ _ _).trans ((normOne_iff hν hJ' cub.isGen _).1 hc)
  have n₂ : nv ν t₂ q z J = 1 := (nv_pull hJ' _ _ _).trans ((normOne_iff hν hJ' L.rigGen _).1 hr)
  have n₃ : nv ν t q z J = 1 := by
    obtain ⟨u, hu, e⟩ := hv _ q z J hJ'
    have a : ∀ i, ‖ev z (u i).val‖ * ν p (q ≫ (six x b c i).left) (J (q ≫ (six x b c i).left)) = δ := fun i => by
      rw [hu i, ev_gs _ z (hJ _)]
      exact hθ i _ ((range_subset_iff _ z _).2 (hJ _))
    rw [nv, e, norm_ev_prod, ← Finset.prod_mul_distrib]
    simp only [← mul_zpow, a]
    simp [Fin.prod_univ_succ]
    field_simp
  refine (normOne_iff hν hJ' hg q).2 ((nv_form hν F q (hgv _ q z J hJ')).trans ((nv_mul hJ' _ _ q).trans ?_))
  exact (congrArg₂ (· * ·) ((nv_mul hJ' t₁ t q).trans ((congrArg₂ (· * ·) n₁ n₃).trans (_root_.mul_one _))) n₂).trans
    (_root_.mul_one _)

end Cube

section Geometry

theorem exists_fac_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {Y : Scheme.{0}} (β : Sp R ⟶ Y) (V : Y.Opens)
    (h : β (IsLocalRing.closedPoint R) ∈ V) : ∃ β' : Sp R ⟶ V.toScheme, β' ≫ V.ι = β := by
  refine ⟨IsOpenImmersion.lift V.ι β ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  have : β ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp h
  exact (this.ge (Set.mem_univ x) : x ∈ β ⁻¹ᵁ V)

theorem exists_fac {Z Y Y' : Scheme.{0}} (β : Z ⟶ Y) (i : Y' ⟶ Y) [IsOpenImmersion i]
    (h : Set.range β ⊆ Set.range i) : ∃ β' : Z ⟶ Y', β' ≫ i = β :=
  ⟨IsOpenImmersion.lift i β h, IsOpenImmersion.lift_fac _ _ _⟩

def preInter {X Y : Scheme.{0}} {K : Type} [Finite K] (φ : K → (Y ⟶ X)) (O : Set X) (hO : IsOpen O) : Y.Opens :=
  ⟨⋂ k, φ k ⁻¹' O, isOpen_iInter_of_finite fun k => hO.preimage (φ k).continuous⟩

theorem mem_preInter {X Y : Scheme.{0}} {K : Type} [Finite K] {φ : K → (Y ⟶ X)} {O : Set X} {hO : IsOpen O} {y : Y} :
    y ∈ preInter φ O hO ↔ ∀ k, φ k y ∈ O := Set.mem_iInter

theorem intAt_mono {X Y : Scheme.{0}} {a : X ⟶ Y} {W : Set Y} {p : ℕ} [Fact p.Prime]
    {x : Sp (PadicAlgCl p) ⟶ X} (h : IntAt a W x) : IntAt a Set.univ x :=
  let ⟨b, hb, _⟩ := h; ⟨b, hb, trivial⟩

end Geometry

end GlobalTheory.ZJ.CubeGen

namespace GlobalTheory.ZJ

open CubeGen

theorem Core.exists_gen_normOne : ∀ (C : Core) (L : C.Law) (T : C.Theta) (Om : Set C.G.toScheme) (ν), IsOpen Om → T.Norms Om ν → L.CompanionTheory Om → (∀ w : C.G.toScheme, IsClosed ({w} : Set C.G.toScheme) → ∃ (W : C.G.toScheme.Opens) (W₀ : C.A.left.Opens) (gen₀ : LB.Gen (T.L.L.pull W₀.ι)), w ∈ W ∧ (W₀ : Set C.A.left).Nonempty ∧ gen₀.IsGen ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ W₀.toScheme), IntAt (W₀.ι ≫ C.a) W x → NormOne ν gen₀ x) := by
  intro C L T Om ν hOm hN h6 w hw
  letI := L.grp
  haveI := L.comm
  haveI := C.isOpenImmersion_a
  obtain ⟨N, b, c, K, _, t, x', b', c', hx', hb', hc', hsix⟩ := h6 w hw

  let X : C.G.toScheme.Opens := C.GG.hom ⁻¹ᵁ N
  let n : X.toScheme ⟶ N.toScheme := C.GG.hom ∣_ N
  have hn : n ≫ N.ι = X.ι ≫ C.GG.hom := morphismRestrict_ι _ _
  let TG : Over C.Z := Over.mk (X.ι ≫ C.GG.hom)
  let m : TG ⟶ Over.mk N.ι := Over.homMk n hn
  let xG : TG ⟶ C.GG := Over.homMk X.ι rfl
  let V : Fin 6 → (X.toScheme ⟶ C.G.toScheme) := fun i => (six xG (m ≫ b) (m ≫ c) i).left
  let W' : X.toScheme.Opens := preInter V Om hOm
  have hwW : w ∈ X.ι ''ᵁ W' := by
    let s : Sp K := IsLocalRing.closedPoint K
    have hs : x'.left s = w := by
      have : x'.left s ∈ Set.range x'.left := ⟨s, rfl⟩
      rwa [hx'] at this
    have hw' : x'.left ≫ C.GG.hom = t ≫ N.ι := Over.w x'
    obtain ⟨r, hr⟩ := exists_fac_of_closedPoint x'.left X (by
      change (x'.left ≫ C.GG.hom) s ∈ N
      rw [hw']
      exact (t s).2)
    have hrn : r ≫ n = t := by
      rw [← cancel_mono N.ι, Category.assoc, hn, ← Category.assoc, hr, hw']
    refine ⟨r s, mem_preInter.2 fun i => ?_, (congrArg (fun q => q s) hr).trans hs⟩
    have e := six_comp (T := TG) (T' := Over.mk (t ≫ N.ι)) r xG (m ≫ b) (m ≫ c) x' b' c' hr.symm
      (hb'.trans (by rw [← hrn]; exact Category.assoc _ _ _)) (hc'.trans (by rw [← hrn]; exact Category.assoc _ _ _)) i
    have : (six x' b' c' i).left s ∈ Om := hsix _ (by fin_cases i <;> simp [six]) ⟨s, rfl⟩
    rw [e] at this
    exact this

  let XA : C.A.left.Opens := C.a ⁻¹ᵁ X
  let ρ : XA.toScheme ⟶ X.toScheme := C.a ∣_ X
  have hρ : ρ ≫ X.ι = XA.ι ≫ C.a := morphismRestrict_ι _ _
  let TA : Over C.U.toScheme := Over.mk (XA.ι ≫ C.A.hom)
  let xA : TA ⟶ C.A := Over.homMk XA.ι rfl
  have lft : ∀ d : TG ⟶ C.GG, ∃ d' : TA ⟶ C.A, d'.left ≫ C.a = ρ ≫ d.left := fun d => by
    have sq : (ρ ≫ d.left) ≫ C.GG.hom = (XA.ι ≫ C.A.hom) ≫ C.U.ι := by
      rw [Category.assoc, Over.w d, Category.assoc, ← C.isPullback_a.w]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.GG.hom) hρ).trans (Category.assoc _ _ _))
    exact ⟨Over.homMk (C.isPullback_a.lift _ _ sq) (C.isPullback_a.lift_snd _ _ _), C.isPullback_a.lift_fst _ _ _⟩
  obtain ⟨bA, hbA⟩ := lft (m ≫ b)
  obtain ⟨cA, hcA⟩ := lft (m ≫ c)
  let VA : Fin 6 → (XA.toScheme ⟶ C.A.left) := fun i => (six xA bA cA i).left
  have hVA : ∀ i, VA i ≫ C.a = ρ ≫ V i := fun i =>
    six_push L.pull (T := TG) (T' := TA) ρ xG (m ≫ b) (m ≫ c) xA bA cA hρ.symm hbA hcA i
  have hVs : ∀ i, VA i ≫ C.A.hom = XA.ι ≫ C.A.hom := fun i => Over.w (six xA bA cA i)

  have key : ∀ (p : ℕ) [Fact p.Prime] (q : Sp (PadicAlgCl p) ⟶ XA.toScheme), IntAt (XA.ι ≫ C.a) (X.ι ''ᵁ W') q →
      (∀ i, IntAt C.a Om (q ≫ VA i)) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ i j, Set.range (q ≫ VA i) ⊆ T.L.L.U j →
        ‖valF (q ≫ VA i) _ (T.θ.f j)‖ * ν p (q ≫ VA i) j = δ := by
    intro p _ q ⟨β, hβ, y, hy, hyβ⟩
    obtain ⟨β', rfl⟩ := exists_fac_of_closedPoint β X (hyβ ▸ y.2)
    have e₁ : gPt p ≫ β' = q ≫ ρ := by
      rw [← cancel_mono X.ι, Category.assoc, hβ, Category.assoc, hρ]
    have e₂ : β' (cPt p) = y := X.ι.injective hyβ.symm
    have I : ∀ i, IntAt C.a Om (q ≫ VA i) := fun i => ⟨β' ≫ V i, by
      rw [← Category.assoc, e₁, Category.assoc, Category.assoc, hVA], by
      have := mem_preInter.1 hy i
      rwa [← e₂] at this⟩
    obtain ⟨δ, hδ, H⟩ := hN.theta p (q ≫ XA.ι ≫ C.A.hom)
    exact ⟨I, δ, hδ, fun i j hj => (H _ j (by rw [Category.assoc, hVs]) hj (intAt_mono (I i))).2.2 (I i)⟩
  let W₁ : XA.toScheme.Opens := preInter VA (Out.nonzeroLocus T.θ) (Out.nonzeroLocus T.θ).isOpen
  let W₀ : C.A.left.Opens := XA.ι ''ᵁ W₁
  have hne : (W₀ : Set C.A.left).Nonempty := by
    haveI := C.isIntegral_G
    obtain ⟨-, h₂, -, -, h₅, -⟩ := core_basic C
    haveI := C.lft
    obtain ⟨a₀⟩ := C.nonempty_A
    obtain ⟨p, _, β, hβ, hU⟩ := padicAlgCl_integral_points.1 C.G.toScheme (C.GG.hom ≫ C.π) w hw
      C.a.opensRange ⟨_, a₀, rfl⟩
    obtain ⟨q', hq'⟩ := exists_fac (gPt p ≫ β) C.a hU
    have hwX : w ∈ X := by
      obtain ⟨y, -, rfl⟩ := hwW
      exact y.2
    obtain ⟨β', hβ'⟩ := exists_fac_of_closedPoint β X (hβ ▸ hwX)
    let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    obtain ⟨q, rfl⟩ := exists_fac_of_closedPoint q' XA (by
      change (q' ≫ C.a) z ∈ X
      rw [hq', ← hβ']
      exact (β' (gPt p z)).2)
    obtain ⟨-, δ, hδ, H⟩ := key p q ⟨β, by rw [← hq', Category.assoc], hβ ▸ hwW⟩
    refine ⟨_, q z, mem_preInter.2 fun i => ?_, rfl⟩
    obtain ⟨j, hj⟩ := exists_chart T.L.isLB ((q ≫ VA i) z)
    have e := H i j ((range_subset_iff _ z _).2 hj)
    refine (mem_nonzeroLocus_iff T.θ (q ≫ VA i) z hj).2 ?_
    have h0 : ev z (gs (q ≫ VA i) z _ (T.θ.f j)) ≠ 0 := fun h0 => by
      rw [← ev_gs _ z hj, h0, norm_zero, zero_mul] at e
      exact hδ.ne e
    simpa using (IsUnit.mk0 _ h0).map (ev z).symm
  obtain ⟨k, hk⟩ := exists_fac W₀.ι XA.ι (by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y', -, e⟩ := y.2
    exact ⟨y', e⟩)
  have hk₁ : ∀ y, k y ∈ W₁ := fun y => by
    obtain ⟨y', h, e⟩ := y.2
    have : k y = y' := XA.ι.injective ((congrArg (fun q => q y) hk).trans e.symm)
    exact this ▸ h
  let T₀ : Over C.U.toScheme := Over.mk (W₀.ι ≫ C.A.hom)
  let κ : T₀ ⟶ TA := Over.homMk k ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.A.hom) hk))
  let x₀ : T₀ ⟶ C.A := Over.homMk W₀.ι rfl
  have h₀ : ∀ i, (six x₀ (κ ≫ bA) (κ ≫ cA) i).left = k ≫ VA i := fun i =>
    six_comp (T := TA) (T' := T₀) k xA bA cA _ _ _ hk.symm rfl rfl i
  obtain ⟨g, hg, H⟩ := exists_gen_cube T.L T.cub T.θ x₀ (κ ≫ bA) (κ ≫ cA) fun i y => by
    rw [h₀]
    exact mem_preInter.1 (hk₁ y) i
  refine ⟨X.ι ''ᵁ W', W₀, g, hwW, hne, hg, fun p _ q hq => ?_⟩
  obtain ⟨β, hβ, hβW⟩ := hq
  obtain ⟨I, δ, hδ, Hδ⟩ := key p (q ≫ k) ⟨β, by rw [hβ, ← hk]; simp only [Category.assoc], hβW⟩
  refine H ν hN.isNrm p q δ hδ (hN.rig p _ ⟨β ≫ C.GG.hom, ?_, trivial⟩) (hN.cube p _ fun i => ?_) fun i j hj => ?_
  · rw [← Category.assoc, hβ]
    simp only [Category.assoc]
    rw [C.isPullback_a.w]
    exact (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _)
  · have e : ∀ i, (q ≫ (lift x₀ (lift (κ ≫ bA) (κ ≫ cA))).left) ≫ (x3 C.A i).left =
        q ≫ (![x₀, κ ≫ bA, κ ≫ cA] i).left := fun i => by
      rw [Category.assoc, ← Over.comp_left]
      fin_cases i <;> simp [x3]
    rw [e]
    fin_cases i
    · exact ⟨β, hβ.trans (Category.assoc _ _ _).symm, trivial⟩
    · have := intAt_mono (I 4)
      rw [Category.assoc] at this
      exact this
    · have := intAt_mono (I 5)
      rw [Category.assoc] at this
      exact this
  · rw [h₀] at hj ⊢
    rw [← Category.assoc] at hj ⊢
    exact Hδ i j hj

end GlobalTheory.ZJ

end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime] {X Y Z : Scheme.{0}}

abbrev z₀ (p : ℕ) [Fact p.Prime] : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)

def sn (p : ℕ) [Fact p.Prime] : (Sp (PadicAlgCl p)).presheaf.stalk (z₀ p) →* ℝ :=
  (normHom : PadicAlgCl p →*₀ ℝ).toMonoidHom.comp (ev (z₀ p)).toRingHom.toMonoidHom

def un (p : ℕ) [Fact p.Prime] : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ →* ℝ :=
  (sn p).comp (Units.coeHom _)

theorem sn_val (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : sn p u.val = un p u := rfl

theorem un_pos (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : 0 < un p u :=
  norm_pos_iff.2 (u.isUnit.map (ev (z₀ p))).ne_zero

theorem sn_gs (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)) :
    sn p (gs x (z₀ p) U a) = ‖valF x U a‖ := congrArg norm (ev_gs x _ h a)

theorem un_gm (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm x (z₀ p) U a) = ‖valF x U a.val‖ := congrArg norm (ev_gm x _ h a)

theorem gs_comp (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

theorem gm_comp (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  refine Units.ext ?_
  rw [← gs_unit (r ≫ q) z U h, gs_comp r q z U h, gs_unit q (r z) U h]
  rfl

theorem mem_of_cPt (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : ⊤ ≤ b ⁻¹ᵁ U :=
  fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (b ⁻¹ᵁ U).isOpen h

theorem gen_mem (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : (gPt p ≫ b) (z₀ p) ∈ U :=
  mem_of_cPt b h (show gPt p (z₀ p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)

theorem isUnit_iff_norm (v : OO p) : IsUnit v ↔ ‖(v : PadicAlgCl p)‖ = 1 := by
  have le : ∀ u : OO p, ‖(u : PadicAlgCl p)‖ ≤ 1 := fun u =>
    (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have e : ‖(v : PadicAlgCl p)‖ * ‖(u : PadicAlgCl p)‖ = 1 := by
      rw [← norm_mul]
      exact (congrArg (fun t : OO p => ‖(t : PadicAlgCl p)‖) hu).trans norm_one
    have := le u
    have := le v
    have := norm_nonneg (v : PadicAlgCl p)
    nlinarith
  · intro h
    have h0 : (v : PadicAlgCl p) ≠ 0 := norm_pos_iff.1 (by rw [h]; exact one_pos)
    refine IsUnit.of_mul_eq_one ⟨(v : PadicAlgCl p)⁻¹,
      (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).2 (by rw [norm_inv, h, inv_one])⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)

theorem sn_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)) :
    sn p (gs (gPt p ≫ b) (z₀ p) U a) ≤ 1 ∧
      (sn p (gs (gPt p ≫ b) (z₀ p) U a) = 1 ↔ b (cPt p) ∈ X.basicOpen a) := by
  have h' := mem_of_cPt b h
  have hg := gen_mem b h
  let v : OO p := (Scheme.ΓSpecIso (CommRingCat.of (OO p))).hom.hom ((b.appLE U ⊤ h').hom a)
  have e : valF (gPt p ≫ b) U a = (v : PadicAlgCl p) := by
    rw [valF, dif_pos ((top_le_iff_mem _ U _).2 hg)]
    have e₁ := Scheme.Hom.appLE_comp_appLE (gPt p) b U ⊤ ⊤ h' le_top
    have e₂ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (OO p).subtype)
    have e₃ : (gPt p).appLE ⊤ ⊤ le_top = (gPt p).appTop := (Scheme.Hom.app_eq_appLE _).symm
    rw [← e₁, e₃]
    exact congrArg (fun q => q.hom ((b.appLE U ⊤ h').hom a)) e₂
  rw [sn_gs _ hg, e]
  refine ⟨(mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 v.2, (isUnit_iff_norm v).symm.trans ?_⟩
  have e₄ : (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) = PrimeSpectrum.basicOpen v :=
    basicOpen_eq_of_affine' _
  have e₅ := Scheme.basicOpen_appLE b ⊤ U h' a
  have e₆ : cPt p ∈ (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) ↔ b (cPt p) ∈ X.basicOpen a := by
    erw [e₅]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  rw [← e₆, e₄]
  exact (IsLocalRing.notMem_maximalIdeal).symm

theorem un_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm (gPt p ≫ b) (z₀ p) U a) = 1 := by
  rw [← sn_val, ← gs_unit _ _ _ (gen_mem b h)]
  refine (sn_integral b h a.val).2.2 ?_
  rw [Scheme.basicOpen_of_isUnit _ a.isUnit]
  exact h

theorem un_eq_of_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (r : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ)
    (hU : ∀ x, ∃ a, x ∈ U a)
    (hr : ∀ a a' x, j x ∈ U a → j x ∈ U a' →
      gm (𝟙 HK) x _ (r a) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a')) :
    ∃ u : Γ(Sp K, ⊤)ˣ, ∀ (c : Sp (OO p) ⟶ H) (cK : Sp (PadicAlgCl p) ⟶ HK), cK ≫ j = gPt p ≫ c → ∀ a,
      c (cPt p) ∈ U a → un p (gm cK (z₀ p) _ (r a)) = un p (gm (cK ≫ fK) (z₀ p) ⊤ u) := by
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  let eK : Sp K ⟶ HK := hK.lift (spMap (algebraMap V K) ≫ e) (𝟙 _) (by simp [he])
  have h₁ : eK ≫ j = spMap (algebraMap V K) ≫ e := hK.lift_fst _ _ _
  have h₂ : eK ≫ fK = 𝟙 _ := hK.lift_snd _ _ _
  obtain ⟨a₀, ha₀⟩ := hU (e (IsLocalRing.closedPoint V))
  have hA : ⊤ ≤ e ⁻¹ᵁ U a₀ := fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (e ⁻¹ᵁ U a₀).isOpen ha₀
  have hA'' : ⊤ ≤ eK ⁻¹ᵁ (j ⁻¹ᵁ U a₀) := fun y _ => by
    show (eK ≫ j) y ∈ U a₀
    rw [h₁]
    exact hA (show spMap (algebraMap V K) y ∈ (⊤ : (Sp V).Opens) from trivial)
  let u : Γ(Sp K, ⊤)ˣ := res hA'' (pullU eK _ (r a₀))
  let r' : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ := fun a => r a * res (le_top : j ⁻¹ᵁ U a ≤ fK ⁻¹ᵁ ⊤) (pullU fK ⊤ u⁻¹)
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a, j (q z) ∈ U a →
      gm q z _ (r' a) = gm q z _ (r a) * (gm (q ≫ fK) z ⊤ u)⁻¹ := fun Z q z a h =>
    (map_mul _ _ _).trans (congrArg (_ * ·) (((gm_res q z _ h _).trans (gm_pull q fK z ⊤ trivial _)).trans
      (map_inv _ _)))
  obtain ⟨s, ⟨hs₁, -, hs₂⟩, -⟩ := DvrModel.existsUnique_isUnit_appLE_eq hK hs (U := U) (g := fun a b => (g a b).val)
    (W := fun a => j ⁻¹ᵁ U a) (fun _ => rfl) hU (fun a b => (g a b).isUnit) (r := fun a => (r' a).val)
    (fun a b => fn_ext fun x hx => by
      refine (gs_res (𝟙 HK) x _ hx _).trans (Eq.trans ?_ ((gs_mul (𝟙 HK) x _ hx _ _).trans
        (congrArg₂ (· * ·) (gs_appLE j _ _ _ (𝟙 HK) x hx _) (gs_res (𝟙 HK) x _ hx _))).symm)
      rw [Category.id_comp, gs_unit (𝟙 HK) x _ hx.1, gs_unit (𝟙 HK) x _ hx.2, gs_unit j x (U a ⊓ U b) hx,
        v _ (𝟙 HK) x a hx.1, v _ (𝟙 HK) x b hx.2, hr a b x hx.1 hx.2, _root_.mul_assoc, Units.val_mul])
    (fun a => (r' a).isUnit) he h₁ (A := ⊤) trivial hA (A' := ⊤) rfl hA'' (u := 1) isUnit_one (by
      rw [map_one]
      refine fn_ext fun y hy => ?_
      refine Eq.trans ?_ (gs_appLE eK _ _ _ (𝟙 _) y hy _).symm
      rw [Category.id_comp, gs_unit eK y _ (hA'' hy), v _ eK y a₀ (hA'' hy), h₂]
      have : gm (𝟙 (Sp K)) y ⊤ u = gm eK y _ (r a₀) := by
        refine ((gm_res _ y _ hy _).trans (gm_pull (𝟙 _) eK y _ (hA'' hy) _)).trans ?_
        rw [Category.id_comp]
      rw [this, mul_inv_cancel, gs_eq _ y ⊤ hy, map_one, map_one, Units.val_one])
  refine ⟨u, fun c cK hc a ha => ?_⟩
  have hm : j (cK (z₀ p)) ∈ U a := by
    show (cK ≫ j) _ ∈ U a
    rw [hc]
    exact gen_mem c ha
  have e₁ : un p (gm cK (z₀ p) _ (r' a)) = 1 := by
    rw [← un_integral c ha (hs₁ a).unit, ← hc]
    refine congrArg (un p) (Units.ext ?_)
    rw [← gs_unit cK _ _ hm, ← gs_unit (cK ≫ j) _ _ hm, ← hs₂ a]
    exact gs_appLE j _ _ _ cK _ hm _
  rw [v _ cK _ a hm, map_mul, map_inv] at e₁
  exact (mul_inv_eq_one₀ (un_pos _).ne').1 e₁

theorem un_eq_of_fine_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α κ : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (W : α → κ → HK.Opens)
    (r : ∀ a b, Γ(HK, W a b)ˣ) (hU : ∀ x, ∃ a, x ∈ U a) (hW : ∀ a x, j x ∈ U a ↔ ∃ b, x ∈ W a b)
    (hr : ∀ a b a' b' x, x ∈ W a b → x ∈ W a' b' →
      gm (𝟙 HK) x _ (r a b) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a' b'))
    {c c' : Sp (OO p) ⟶ H} {cK cK' : Sp (PadicAlgCl p) ⟶ HK} (hc : cK ≫ j = gPt p ≫ c) (hc' : cK' ≫ j = gPt p ≫ c')
    (h : c ≫ f = c' ≫ f) {a a' : α} {b b' : κ} (ha : c (cPt p) ∈ U a) (ha' : c' (cPt p) ∈ U a')
    (hb : cK (z₀ p) ∈ W a b) (hb' : cK' (z₀ p) ∈ W a' b') :
    un p (gm cK (z₀ p) _ (r a b)) = un p (gm cK' (z₀ p) _ (r a' b')) := by
  have le : ∀ a b, W a b ≤ j ⁻¹ᵁ U a := fun a b x hx => (hW a x).2 ⟨b, hx⟩
  choose R hR using fun a => glue_unit (j ⁻¹ᵁ U a) (W a) (le a)
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ((hW a x).1 hx)) (r a) (fun b b' x hx => by
      rw [hr a b a b' x hx.1 hx.2, mul_eq_right.1 (hr a b a b x hx.1 hx.1).symm, _root_.one_mul])
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a b, q z ∈ W a b → gm q z _ (r a b) = gm q z _ (R a) :=
    fun Z q z a b h => by rw [← hR a b, gm_res q z _ h]
  obtain ⟨u, hu⟩ := un_eq_of_charts (p := p) hK e he U g R hU fun a a' x hx hx' => by
    obtain ⟨b, hb⟩ := (hW a x).1 hx
    obtain ⟨b', hb'⟩ := (hW a' x).1 hx'
    rw [← v _ (𝟙 HK) x a b hb, ← v _ (𝟙 HK) x a' b' hb', hr a b a' b' x hb hb']
  have := DvrModel.isOpenImmersion_generic (IsPullback.of_id_snd (f := spMap (algebraMap V K)))
  rw [v _ _ _ _ _ hb, v _ _ _ _ _ hb', hu c cK hc a ha, hu c' cK' hc' a' ha']
  refine congrArg (fun q => un p (gm q (z₀ p) ⊤ u)) ?_
  rw [← cancel_mono (spMap (algebraMap V K)), Category.assoc, Category.assoc, ← hK.w, ← Category.assoc, hc,
    ← Category.assoc, hc', Category.assoc, Category.assoc, h]

theorem exists_norm_ext {L : LB X} (hL : L.IsLB) (x : Sp (PadicAlgCl p) ⟶ X) (S : L.ι → ℝ → Prop)
    (hS : ∀ j t, S j t → 0 < t ∧ x (z₀ p) ∈ L.U j)
    (hS' : ∀ j t j' t', S j t → S j' t' → un p (gm x (z₀ p) _ (L.g j j')) * t = t') :
    ∃ n : L.ι → ℝ, (∀ j, 0 < n j) ∧ (∀ j j', x (z₀ p) ∈ L.U j → x (z₀ p) ∈ L.U j' →
      un p (gm x (z₀ p) _ (L.g j j')) * n j = n j') ∧ ∀ j t, S j t → n j = t := by
  classical
  obtain ⟨i, t₀, h₀, hi, H⟩ : ∃ i t₀, 0 < t₀ ∧ x (z₀ p) ∈ L.U i ∧
      ∀ j t, S j t → un p (gm x (z₀ p) _ (L.g i j)) * t₀ = t := by
    by_cases h : ∃ j t, S j t
    · obtain ⟨i, t₀, h⟩ := h
      exact ⟨i, t₀, (hS _ _ h).1, (hS _ _ h).2, fun j t h' => hS' _ _ _ _ h h'⟩
    · obtain ⟨i, hi⟩ := exists_chart hL (x (z₀ p))
      exact ⟨i, 1, one_pos, hi, fun j t h' => absurd ⟨j, t, h'⟩ h⟩
  refine ⟨fun j => un p (gm x (z₀ p) _ (L.g i j)) * t₀, fun j => mul_pos (un_pos _) h₀, fun j j' hj hj' => ?_, H⟩
  rw [← _root_.mul_assoc, ← map_mul, _root_.mul_comm (gm x _ _ _), gm_cocycle hL x _ hi hj hj']

end GlobalTheory.ZJ.TestNorm
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime]

section Bundle

variable {H HK A : Scheme.{0}} {M : LB H} {L : LB A} {j : HK ⟶ H} {φ : HK ⟶ A}

def wg (w : LB.Iso (L.pull φ) (M.pull j)) {Z : Scheme.{0}} (q : Z ⟶ HK) (z : Z) (a : M.ι) (b : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm q z ((M.pull j).U (fun _ => a) ⊓ (L.pull φ).U (fun _ => b)) (w.s (fun _ => a, fun _ => b))

theorem wg_trans {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen) {Z : Scheme.{0}} (q : Z ⟶ HK) (z : Z)
    {a a' : M.ι} {b b' : L.ι} (ha : j (q z) ∈ M.U a) (ha' : j (q z) ∈ M.U a') (hb : φ (q z) ∈ L.U b)
    (hb' : φ (q z) ∈ L.U b') :
    wg w q z a b = gm (q ≫ j) z _ (M.g a a') * (gm (q ≫ φ) z _ (L.g b b'))⁻¹ * wg w q z a' b' := by
  have hm : q z ∈ (M.pull j).U (fun _ => a) ⊓ (L.pull φ).U (fun _ => b) ⊓
      ((M.pull j).U (fun _ => a') ⊓ (L.pull φ).U (fun _ => b')) :=
    ⟨⟨mem_pull.2 ha, mem_pull.2 hb⟩, mem_pull.2 ha', mem_pull.2 hb'⟩
  have e := congrArg (gm q z _) (hw (fun _ => a, fun _ => b) (fun _ => a', fun _ => b'))
  refine (gm_res q z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div (L.pull φ) (M.pull j) q z (fun _ => a, fun _ => b) (fun _ => a', fun _ => b') hm).trans ?_)
    (gm_res q z _ hm _))))
  exact congrArg₂ (fun s t => s * t⁻¹) (gm_pull_g M j q z _ _ hm.1.1 hm.2.1) (gm_pull_g L φ q z _ _ hm.1.2 hm.2.2)

def wv (w : LB.Iso (L.pull φ) (M.pull j)) (q : Sp (PadicAlgCl p) ⟶ HK) (a : M.ι) (b : L.ι) : ℝ :=
  un p (wg w q (z₀ p) a b)

theorem wv_pos (w : LB.Iso (L.pull φ) (M.pull j)) (q : Sp (PadicAlgCl p) ⟶ HK) (a : M.ι) (b : L.ι) :
    0 < wv w q a b := un_pos _

theorem wv_trans {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen) {c : Sp (OO p) ⟶ H}
    {q : Sp (PadicAlgCl p) ⟶ HK} (h : q ≫ j = gPt p ≫ c) {a a' : M.ι} {b b' : L.ι} (ha : c (cPt p) ∈ M.U a)
    (ha' : c (cPt p) ∈ M.U a') (hb : (q ≫ φ) (z₀ p) ∈ L.U b) (hb' : (q ≫ φ) (z₀ p) ∈ L.U b') :
    un p (gm (q ≫ φ) (z₀ p) _ (L.g b b')) * wv w q a b = wv w q a' b' := by
  have m : ∀ {a}, c (cPt p) ∈ M.U a → j (q (z₀ p)) ∈ M.U a := fun {a} ha => by
    show (q ≫ j) _ ∈ M.U a
    rw [h]
    exact gen_mem c ha
  rw [wv, wg_trans hw q _ (m ha) (m ha') hb hb', map_mul, map_mul, map_inv, h,
    un_integral c (U := M.U a ⊓ M.U a') ⟨ha, ha'⟩, _root_.one_mul, mul_inv_cancel_left₀ (un_pos _).ne']
  rfl

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
  [Algebra V K] [IsFractionRing V K]

theorem wv_eq_of_extends (hM : M.IsLB) (hL : L.IsLB) {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen)
    {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f] {fK : HK ⟶ Sp K}
    (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H) (he : e ≫ f = 𝟙 _) (ψ : H ⟶ A)
    (hψ : j ≫ ψ = φ) {c c' : Sp (OO p) ⟶ H} {q q' : Sp (PadicAlgCl p) ⟶ HK} (hc : q ≫ j = gPt p ≫ c)
    (hc' : q' ≫ j = gPt p ≫ c') (h : c ≫ f = c' ≫ f) {a a' : M.ι} {b b' : L.ι} (ha : c (cPt p) ∈ M.U a)
    (ha' : c' (cPt p) ∈ M.U a') (hb : (c ≫ ψ) (cPt p) ∈ L.U b) (hb' : (c' ≫ ψ) (cPt p) ∈ L.U b') :
    wv w q a b = wv w q' a' b' := by
  subst hψ
  have m : ∀ {c : Sp (OO p) ⟶ H} {q : Sp (PadicAlgCl p) ⟶ HK}, q ≫ j = gPt p ≫ c → ∀ {a b},
      c (cPt p) ∈ M.U a → (c ≫ ψ) (cPt p) ∈ L.U b →
      q (z₀ p) ∈ (M.pull j).U (fun _ => a) ⊓ (L.pull (j ≫ ψ)).U (fun _ => b) := fun {c q} hc {a b} ha hb => by
    have : (q ≫ j) (z₀ p) ∈ M.U a ⊓ ψ ⁻¹ᵁ L.U b := by
      rw [hc]
      exact gen_mem c ⟨ha, hb⟩
    exact ⟨mem_pull.2 this.1, mem_pull.2 this.2⟩
  refine un_eq_of_fine_charts hK e he (α := M.ι × L.ι) (κ := PUnit) (fun s => M.U s.1 ⊓ ψ ⁻¹ᵁ L.U s.2)
    (fun s t => res (inf_le_inf inf_le_left inf_le_left) (M.g s.1 t.1) *
      (res (inf_le_inf inf_le_right inf_le_right : _ ≤ ψ ⁻¹ᵁ L.U s.2 ⊓ ψ ⁻¹ᵁ L.U t.2)
        (pullU ψ (L.U s.2 ⊓ L.U t.2) (L.g s.2 t.2)))⁻¹)
    (fun s _ => (M.pull j).U (fun _ => s.1) ⊓ (L.pull (j ≫ ψ)).U (fun _ => s.2))
    (fun s _ => w.s (fun _ => s.1, fun _ => s.2)) (fun x => ?_) (fun s x => ?_) (fun s _ t _ x hs ht => ?_)
    hc hc' h (a := (a, b)) (a' := (a', b')) (b := ⟨⟩) (b' := ⟨⟩) ⟨ha, hb⟩ ⟨ha', hb'⟩ (m hc ha hb) (m hc' ha' hb')
  · obtain ⟨a, ha⟩ := exists_chart hM x
    obtain ⟨b, hb⟩ := exists_chart hL (ψ x)
    exact ⟨(a, b), ha, hb⟩
  · exact ⟨fun h => ⟨⟨⟩, mem_pull.2 h.1, mem_pull.2 h.2⟩, fun ⟨_, h⟩ => ⟨mem_pull.1 h.1, mem_pull.1 h.2⟩⟩
  · have hm : j x ∈ M.U s.1 ⊓ ψ ⁻¹ᵁ L.U s.2 ⊓ (M.U t.1 ⊓ ψ ⁻¹ᵁ L.U t.2) :=
      ⟨⟨mem_pull.1 hs.1, mem_pull.1 hs.2⟩, mem_pull.1 ht.1, mem_pull.1 ht.2⟩
    refine (wg_trans hw (𝟙 HK) x hm.1.1 hm.2.1 hm.1.2 hm.2.2).trans (congrArg (· * _) ?_)
    rw [Category.id_comp, Category.id_comp]
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res j x _ hm _) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((gm_res j x _ hm _).trans (gm_pull j ψ x (L.U s.2 ⊓ L.U t.2) ⟨hm.1.2, hm.2.2⟩ _)))))).symm

theorem gen_wv_eq (hM : M.IsLB) (hL : L.IsLB) {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen)
    {Y YK B : Scheme.{0}} {f : Y ⟶ Sp V} [Smooth f] [GeometricallyIntegral f] {i : YK ⟶ Y} {fK : YK ⟶ Sp K}
    (hK : IsPullback i fK f (spMap (algebraMap V K))) (e : Sp V ⟶ Y) (he : e ≫ f = 𝟙 _)
    {I : Type} [Fintype I] (α : I → (Y ⟶ H)) (ψ : I → (YK ⟶ HK)) (β : I → (B ⟶ A)) (Φ : YK ⟶ B)
    (h₁ : ∀ k, ψ k ≫ j = i ≫ α k) (h₂ : ∀ k, ψ k ≫ φ = Φ ≫ β k) {ε : I → ℤ} {t : LB.Gen (LB.LinComb L β ε)}
    (ht : t.IsGen) {c c' : Sp (OO p) ⟶ Y} {q q' : Sp (PadicAlgCl p) ⟶ YK} (hc : q ≫ i = gPt p ≫ c)
    (hc' : q' ≫ i = gPt p ≫ c') (h : c ≫ f = c' ≫ f) {a a' : I → M.ι} {b b' : I → L.ι}
    (ha : ∀ k, (c ≫ α k) (cPt p) ∈ M.U (a k)) (ha' : ∀ k, (c' ≫ α k) (cPt p) ∈ M.U (a' k))
    (hb : ∀ k, ((q ≫ Φ) ≫ β k) (z₀ p) ∈ L.U (b k)) (hb' : ∀ k, ((q' ≫ Φ) ≫ β k) (z₀ p) ∈ L.U (b' k)) :
    un p (gm (q ≫ Φ) (z₀ p) (LB.wchart L β b) (t.s b)) * ∏ k, wv w (q ≫ ψ k) (a k) (b k) ^ ε k =
      un p (gm (q' ≫ Φ) (z₀ p) (LB.wchart L β b') (t.s b')) * ∏ k, wv w (q' ≫ ψ k) (a' k) (b' k) ^ ε k := by
  let D := LB.div (M.pull j) (L.pull φ)
  let s : (I → M.ι) → (I → L.ι) → I → D.ι := fun a b k => (fun _ => a k, fun _ => b k)
  have p₁ : ∀ k x, j (ψ k x) = α k (i x) := fun k x => congrArg (fun g => g x) (h₁ k)
  have p₂ : ∀ k x, φ (ψ k x) = β k (Φ x) := fun k x => congrArg (fun g => g x) (h₂ k)
  have mem : ∀ a b x, x ∈ LB.wchart D ψ (s a b) ↔
      (∀ k, α k (i x) ∈ M.U (a k)) ∧ ∀ k, β k (Φ x) ∈ L.U (b k) := fun a b x => by
    refine Set.mem_iInter.trans (Iff.trans (forall_congr' fun k => ?_) forall_and)
    rw [← p₁, ← p₂]
    exact and_congr mem_pull mem_pull
  have le : ∀ a b, LB.wchart D ψ (s a b) ≤ Φ ⁻¹ᵁ LB.wchart L β b := fun a b x hx =>
    Set.mem_iInter.2 ((mem a b x).1 hx).2
  let r : ∀ a b, Γ(YK, LB.wchart D ψ (s a b))ˣ := fun a b => res (le a b) (pullU Φ _ (t.s b)) *
    ∏ k, res (LB.wchart_le D ψ (s a b) k) (pullU (ψ k) _ (w.s (s a b k))) ^ ε k
  have v : ∀ (Z : Scheme.{0}) (u : Z ⟶ YK) (z : Z) a b, u z ∈ LB.wchart D ψ (s a b) →
      gm u z _ (r a b) = gm (u ≫ Φ) z (LB.wchart L β b) (t.s b) * ∏ k, wg w (u ≫ ψ k) z (a k) (b k) ^ ε k :=
    fun Z u z a b hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res u z _ hz _).trans (gm_pull u Φ z _ (le a b hz) _))
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
        ((gm_res u z _ hz _).trans (gm_pull u (ψ k) z _ (LB.wchart_le D ψ (s a b) k hz) _))))))
  have m : ∀ {c : Sp (OO p) ⟶ Y} {q : Sp (PadicAlgCl p) ⟶ YK}, q ≫ i = gPt p ≫ c → ∀ {a b},
      (∀ k, (c ≫ α k) (cPt p) ∈ M.U (a k)) → (∀ k, ((q ≫ Φ) ≫ β k) (z₀ p) ∈ L.U (b k)) →
      q (z₀ p) ∈ LB.wchart D ψ (s a b) := fun {c q} hc {a b} ha hb => (mem a b _).2 ⟨fun k => by
    show ((q ≫ i) ≫ α k) _ ∈ M.U (a k)
    rw [hc, Category.assoc]
    exact gen_mem _ (ha k), hb⟩
  have key := un_eq_of_fine_charts hK e he (LB.wchart M α) (LB.LinComb M α ε).g (fun a b => LB.wchart D ψ (s a b)) r
    (fun x => by
      choose a ha using fun k => exists_chart hM (α k x)
      exact ⟨a, Set.mem_iInter.2 ha⟩)
    (fun a x => by
      choose b hb using fun k => exists_chart hL (β k (Φ x))
      exact ⟨fun h => ⟨b, (mem a b x).2 ⟨Set.mem_iInter.1 h, hb⟩⟩,
        fun ⟨b, h⟩ => Set.mem_iInter.2 ((mem a b x).1 h).1⟩)
    (fun a b a' b' x hx hx' => by
      obtain ⟨m₁, m₂⟩ := (mem a b x).1 hx
      obtain ⟨m₁', m₂'⟩ := (mem a' b' x).1 hx'
      rw [v _ (𝟙 YK) x a b hx, v _ (𝟙 YK) x a' b' hx', Category.id_comp,
        gen_trans ht Φ x (Set.mem_iInter.2 m₂) (Set.mem_iInter.2 m₂')]
      erw [gm_linComb M α ε i x a a' (Set.mem_iInter.2 m₁) (Set.mem_iInter.2 m₁')]
      rw [trF, mul_left_comm, _root_.mul_assoc, mul_left_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine congrArg (_ * ·) (Finset.prod_congr rfl fun k _ => ?_)
      rw [← mul_zpow, ← mul_zpow, Category.id_comp, wg_trans hw (ψ k) x (a := a k) (a' := a' k) (b := b k) (b' := b' k)
        (by rw [p₁]; exact m₁ k) (by rw [p₁]; exact m₁' k) (by rw [p₂]; exact m₂ k) (by rw [p₂]; exact m₂' k),
        h₁, h₂, _root_.mul_assoc, mul_left_comm, mul_inv_cancel_left])
    hc hc' h (Set.mem_iInter.2 ha) (Set.mem_iInter.2 ha') (m hc ha hb) (m hc' ha' hb')
  rw [v _ _ _ _ _ (m hc ha hb), v _ _ _ _ _ (m hc' ha' hb')] at key
  simpa only [map_mul, map_prod, map_zpow, wv] using key

end Bundle

theorem ext_gPt {X S : Scheme.{0}} (s : X ⟶ S) [IsSeparated s] {b b' : Sp (OO p) ⟶ X} (h : b ≫ s = b' ≫ s)
    (h' : gPt p ≫ b = gPt p ≫ b') : b = b' := by
  have := InvExt.isDominant_gPt p
  exact ext_of_isDominant_of_isSeparated s h (gPt p) h'

theorem isPullback_cube {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {A : Over U} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left} (gp : IsGrpPullback A G j F) :
    IsPullback (cubeMapOf gp).F3 (G3 A).hom (G3 G).hom j := by
  have hp := gp.1
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have w : (cubeMapOf gp).F3 ≫ (G3 G).hom = (G3 A).hom ≫ j :=
    Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2))))
  have ex : ∀ s : PullbackCone (G3 G).hom j, ∃ l : s.pt ⟶ (G3 A).left,
      l ≫ (cubeMapOf gp).F3 = s.fst ∧ l ≫ (G3 A).hom = s.snd := by
    intro s
    let P : Over U := Over.mk s.snd
    let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ F = s.fst ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
    have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
    refine ⟨l.left, hom_ext_triple _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f3, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => hom_ext_triple _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f3, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem sum_thε : ∑ I : thK.{0}, thε I = 0 := by decide

theorem prod_thε {t : ℝ} (ht : 0 < t) : ∏ I : thK.{0}, t ^ thε I = 1 := by
  have : ∀ s : Finset thK.{0}, ∏ I ∈ s, t ^ thε I = t ^ ∑ I ∈ s, thε I := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ ht.ne']
  rw [this, sum_thε, zpow_zero]

section Test

variable {C : Core} {T : C.Theta} {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)

theorem base_ext {y y' : Sp (OO p) ⟶ C.Z} (h : gPt p ≫ y = gPt p ≫ y') : y = y' :=
  have := C.sep
  ext_gPt C.π (specZIsTerminal.hom_ext _ _) h

abbrev jg : pullback τ.H.hom (Out.jK τ.V) ⟶ τ.H.left := pullback.fst τ.H.hom (Out.jK τ.V)

def IsLift (c : Sp (OO p) ⟶ τ.H.left) (q : Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V)) : Prop :=
  c ≫ τ.H.hom = spMap τ.j ∧ q ≫ jg τ = gPt p ≫ c

theorem exists_frac : ∃ r, gPt p ≫ spMap τ.j = r ≫ Out.jK τ.V := by
  obtain ⟨r, hr⟩ := spMap_factor_jK ((OO p).subtype.comp τ.j) (Subtype.val_injective.comp τ.j_inj)
  exact ⟨r, (Spec.map_comp _ _).symm.trans hr⟩

variable {τ} {c c' : Sp (OO p) ⟶ τ.H.left} {q q' : Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V)}

theorem IsLift.gen (h : IsLift τ c q) : (q ≫ τ.φ) ≫ C.a = gPt p ≫ c ≫ τ.f := by
  rw [Category.assoc, τ.φ_f, ← Category.assoc, h.2, Category.assoc]

theorem IsLift.over (h : IsLift τ c q) : (c ≫ τ.f) ≫ C.GG.hom = y := by
  rw [Category.assoc, τ.f_over, ← Category.assoc, h.1, τ.fac]

theorem IsLift.base (h : IsLift τ c q) : (q ≫ τ.φ) ≫ C.A.hom ≫ C.U.ι = gPt p ≫ y := by
  rw [← C.isPullback_a.w, ← Category.assoc, h.gen, Category.assoc, h.over]

theorem IsLift.centre (h : IsLift τ c q) : τ.H.hom (c (cPt p)) = IsLocalRing.closedPoint τ.V := by
  have := τ.j_loc
  exact (congrArg (fun g => g (cPt p)) h.1).trans (IsLocalRing.comap_closedPoint τ.j)

theorem IsLift.unique (hp : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) (h : IsLift τ c q) (h' : IsLift τ c' q')
    (e : q ≫ τ.φ = q' ≫ τ.φ) : c = c' ∧ q = q' := by
  have := τ.sep
  have := DvrModel.isOpenImmersion_generic (IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V))
  have e₁ : c = c' := ext_gPt τ.H.hom (h.1.trans h'.1.symm) (hp.hom_ext
    (by rw [Category.assoc, Category.assoc, ← h.gen, ← h'.gen, e])
    (by rw [Category.assoc, Category.assoc, h.1, h'.1]))
  exact ⟨e₁, (cancel_mono (jg τ)).1 (by rw [h.2, h'.2, e₁])⟩

variable (τ) in
theorem exists_lift {b : Sp (OO p) ⟶ C.G.toScheme} {x : Sp (PadicAlgCl p) ⟶ C.A.left} (hb : b ≫ C.GG.hom = y)
    (hx : gPt p ≫ b = x ≫ C.a) : ∃ c q, IsLift τ c q ∧ c ≫ τ.f = b ∧ q ≫ τ.φ = x := by
  have := C.isOpenImmersion_a
  obtain ⟨c, h₁, h₂⟩ := τ.lift b hb
  obtain ⟨r, hr⟩ := exists_frac τ
  have h : IsLift τ c (pullback.lift (gPt p ≫ c) r (by rw [Category.assoc, h₁, hr])) :=
    ⟨h₁, pullback.lift_fst _ _ _⟩
  exact ⟨c, _, h, h₂, (cancel_mono C.a).1 (by rw [h.gen, h₂, hx])⟩

variable (E : T.Ext τ)

theorem IsLift.theta (h : IsLift τ c q) {a : E.L.L.ι} {b : T.L.L.ι} (ha : c (cPt p) ∈ E.L.L.U a)
    (hb : (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b) :
    ‖valF (q ≫ τ.φ) _ (T.θ.f b)‖ * wv E.w q a b ≤ 1 ∧
      (‖valF (q ≫ τ.φ) _ (T.θ.f b)‖ * wv E.w q a b = 1 ↔ c (cPt p) ∈ Out.nonzeroLocus E.θ) := by
  have ha' : jg τ (q (z₀ p)) ∈ E.L.L.U a := by
    show (q ≫ jg τ) _ ∈ _
    rw [h.2]
    exact gen_mem c ha
  have hm : q (z₀ p) ∈ (E.L.L.pull (jg τ)).U (fun _ => a) ⊓ (T.L.L.pull τ.φ).U (fun _ => b) :=
    ⟨mem_pull.2 ha', mem_pull.2 hb⟩
  have e := congrArg (q.stalkMap (z₀ p)).hom (E.θ_eq _ a b ha' hb)
  rw [map_mul, ← gs_comp q _ _ _ ha', ← gs_comp q _ _ _ hb, h.2] at e
  have e₁ := (gs_stalkMap q (z₀ p) _ hm (E.w.s (fun _ => a, fun _ => b)).val).symm.trans (gs_unit q _ _ hm _)
  have e₂ : ‖valF (q ≫ τ.φ) _ (T.θ.f b)‖ * wv E.w q a b = sn p (gs (gPt p ≫ c) (z₀ p) _ (E.θ.f a)) := by
    rw [e, map_mul, ← sn_gs _ hb, _root_.mul_comm]
    exact congrArg (· * _) (congrArg (sn p) e₁).symm
  rw [e₂, mem_nonzeroLocus_iff E.θ c _ ha, isUnit_gs_iff c _ _ ha]
  exact sn_integral c ha _

def IsRigNorm (ρ : ℝ) : Prop :=
  ∀ c q (u : Sp (PadicAlgCl p) ⟶ C.U.toScheme) (a : E.L.L.ι) (b : T.L.L.ι), IsLift τ c q →
    q ≫ τ.φ = u ≫ eSec C.A → c (cPt p) ∈ E.L.L.U a → (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b →
    un p (gm u (z₀ p) (LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b) (T.L.rig.s fun _ => b)) *
      wv E.w q a b = ρ

theorem exists_isRigNorm (hp : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) : ∃ ρ, 0 < ρ ∧ IsRigNorm E ρ := by
  by_cases h : ∃ c q, ∃ (u : Sp (PadicAlgCl p) ⟶ C.U.toScheme) (a : E.L.L.ι) (b : T.L.L.ι), IsLift τ c q ∧
    q ≫ τ.φ = u ≫ eSec C.A ∧ c (cPt p) ∈ E.L.L.U a ∧ (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b
  swap
  · exact ⟨1, one_pos, fun c q u a b h₁ h₂ h₃ h₄ => absurd ⟨c, q, u, a, b, h₁, h₂, h₃, h₄⟩ h⟩
  obtain ⟨c', q', u', a', b', k₁, k₂, k₃, k₄⟩ := h
  refine ⟨_, mul_pos (un_pos (gm u' (z₀ p) (LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b')
    (T.L.rig.s fun _ => b'))) (wv_pos E.w q' a' b'), fun c q u a b h₁ h₂ h₃ h₄ => ?_⟩
  have he : eSec C.A ≫ C.A.hom = 𝟙 _ := Over.w η[C.A]
  have base : ∀ {c q} {u : Sp (PadicAlgCl p) ⟶ C.U.toScheme}, IsLift τ c q → q ≫ τ.φ = u ≫ eSec C.A →
      u ≫ C.U.ι = gPt p ≫ y := fun {c q u} h₁ h₂ => by
    rw [← h₁.base, h₂, Category.assoc]
    exact congrArg (u ≫ ·) ((Category.id_comp _).symm.trans ((congrArg (· ≫ C.U.ι) he.symm).trans
      (Category.assoc _ _ _)))
  obtain rfl : u = u' := (cancel_mono C.U.ι).1 ((base h₁ h₂).trans (base k₁ k₂).symm)
  obtain ⟨rfl, rfl⟩ := h₁.unique hp k₁ (h₂.trans k₂.symm)
  have m : ∀ {b}, (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b →
      u (z₀ p) ∈ LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b := fun {b} hb =>
    Set.mem_iInter.2 fun _ => by rw [h₂] at hb; exact hb
  rw [gen_trans T.L.rigGen u _ (m h₄) (m k₄), trF, Fintype.prod_unique, zpow_one, map_mul, ← h₂,
    ← wv_trans E.w_gen h₁.2 h₃ k₃ h₄ k₄]
  ring

variable {E}

theorem IsRigNorm.integral {ρ : ℝ} (hρ : IsRigNorm E ρ) {s : Sp (OO p) ⟶ C.A.left} (h : IsLift τ c q)
    (hs : c ≫ τ.f = s ≫ C.a) {a : E.L.L.ι} {b : T.L.L.ι} (ha : c (cPt p) ∈ E.L.L.U a)
    (hb : s (cPt p) ∈ T.L.L.U b) : wv E.w q a b = ρ := by
  have := C.isOpenImmersion_a
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := geometricallyIntegral_of_isSemiAbelian τ.H
  have hy : (s ≫ C.A.hom) ≫ C.U.ι = y := by
    rw [Category.assoc, ← C.isPullback_a.w, ← Category.assoc, ← hs, h.over]
  obtain ⟨y₁, hy₁⟩ := exists_fac_of_closedPoint τ.y₀ C.U (by
    rw [← h.centre]
    show (c ≫ τ.H.hom ≫ τ.y₀) (cPt p) ∈ C.U
    rw [← Category.assoc, h.1, τ.fac, ← hy]
    exact ((s ≫ C.A.hom) (cPt p)).2)
  let ψ : τ.H.left ⟶ C.A.left := C.isPullback_a.lift τ.f (τ.H.hom ≫ y₁) (by rw [τ.f_over, Category.assoc, hy₁])
  have hψ : ψ ≫ C.a = τ.f := C.isPullback_a.lift_fst _ _ _
  have hφ : jg τ ≫ ψ = τ.φ := (cancel_mono C.a).1 (by rw [Category.assoc, hψ, τ.φ_f])
  have he : eSec C.A ≫ C.A.hom = 𝟙 _ := Over.w η[C.A]
  let s₀ : Sp (OO p) ⟶ C.A.left := (s ≫ C.A.hom) ≫ eSec C.A
  obtain ⟨c₀, q₀, k₁, k₂, k₃⟩ := exists_lift τ (b := s₀ ≫ C.a) (x := gPt p ≫ s₀) (by
    rw [Category.assoc, C.isPullback_a.w, ← hy, ← Category.assoc]
    exact congrArg (· ≫ C.U.ι) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) he).trans (Category.comp_id _))))
    (Category.assoc _ _ _).symm
  have e₁ : c ≫ ψ = s := (cancel_mono C.a).1 (by rw [Category.assoc, hψ, hs])
  have e₂ : c₀ ≫ ψ = s₀ := (cancel_mono C.a).1 (by rw [Category.assoc, hψ, k₂])
  obtain ⟨a₀, ha₀⟩ := exists_chart E.L.isLB (c₀ (cPt p))
  obtain ⟨b₀, hb₀⟩ := exists_chart T.L.isLB (s₀ (cPt p))
  have e₃ := hρ c₀ q₀ (gPt p ≫ s ≫ C.A.hom) a₀ b₀ k₁ (k₃.trans (Category.assoc _ _ _).symm) ha₀
    (by rw [k₃]; exact gen_mem s₀ hb₀)
  have e₄ := un_integral (s ≫ C.A.hom) (U := LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b₀)
    (Set.mem_iInter.2 fun _ => hb₀) (T.L.rig.s fun _ => b₀)
  rw [← ((_root_.one_mul _).symm.trans (congrArg (· * _) e₄.symm)).trans e₃]
  exact wv_eq_of_extends E.L.isLB T.L.isLB E.w_gen (IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V)) (eSec τ.H)
    (Over.w η[τ.H]) ψ hφ h.2 k₁.2 (h.1.trans k₁.1.symm) ha ha₀ (by rw [e₁]; exact hb) (by rw [e₂]; exact hb₀)

end Test

end GlobalTheory.ZJ.TestNorm
end
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime]

section Cube

variable {C : Core} {T : C.Theta} {y : Sp (OO p) ⟶ C.Z} {τ : C.Test y} (E : T.Ext τ)

theorem cube_eq_one (hp : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) (x : Sp (PadicAlgCl p) ⟶ (G3 C.A).left)
    (s : Fin 3 → (Sp (OO p) ⟶ C.G.toScheme)) (hs : ∀ k, s k ≫ C.GG.hom = y)
    (hx : ∀ k, gPt p ≫ s k = (x ≫ (x3 C.A k).left) ≫ C.a) :
    ∃ (c : thK.{0} → (Sp (OO p) ⟶ τ.H.left)) (q : thK.{0} → (Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V))),
      (∀ I, IsLift τ (c I) (q I) ∧ q I ≫ τ.φ = x ≫ thφ C.A (x3 C.A) I) ∧
      ∀ (a : thK.{0} → E.L.L.ι) (b : thK.{0} → T.L.L.ι), (∀ I, c I (cPt p) ∈ E.L.L.U (a I)) →
        (∀ I, (x ≫ thφ C.A (x3 C.A) I) (z₀ p) ∈ T.L.L.U (b I)) →
        un p (gm x (z₀ p) (LB.wchart T.L.L (thφ C.A (x3 C.A)) b) (T.cub.t.s b)) *
          ∏ I, wv E.w (q I) (a I) (b I) ^ thε I = 1 := by
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := hG.geomConnected
  have := smooth_cube_hom τ.H
  have := geometricallyIntegral_cube_hom τ.H
  have : IsCommMonObj ((Over.pullback (Out.jK τ.V)).obj τ.H) := Functor.isCommMonObj_obj
  have : Mono (jg τ) :=
    have := DvrModel.isOpenImmersion_generic (IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V))
    inferInstance
  let HK := (Over.pullback (Out.jK τ.V)).obj τ.H
  have gp := isGrpPullback_pullback τ.H (Out.jK τ.V)
  have hK := isPullback_cube gp
  have h₁ : ∀ I : thK.{0}, thφ HK (x3 HK) I ≫ jg τ = (cubeMapOf gp).F3 ≫ thφ τ.H (x3 τ.H) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  have h₂ : ∀ I : thK.{0}, thφ HK (x3 HK) I ≫ τ.φ = (cubeMapOf τ.φ_cart).F3 ≫ thφ C.A (x3 C.A) I :=
    fun I => (cubeMapOf τ.φ_cart).psum_comm I.down
  obtain ⟨r, hr⟩ := exists_frac τ
  have lifts : ∀ (x : Sp (PadicAlgCl p) ⟶ (G3 C.A).left) (s : Fin 3 → (Sp (OO p) ⟶ C.G.toScheme)),
      (∀ k, s k ≫ C.GG.hom = y) → (∀ k, gPt p ≫ s k = (x ≫ (x3 C.A k).left) ≫ C.a) →
      ∃ (c : Sp (OO p) ⟶ (G3 τ.H).left) (q : Sp (PadicAlgCl p) ⟶ (G3 HK).left), c ≫ (G3 τ.H).hom = spMap τ.j ∧
        q ≫ (cubeMapOf gp).F3 = gPt p ≫ c ∧ q ≫ (cubeMapOf τ.φ_cart).F3 = x ∧
        ∀ I : thK.{0}, IsLift τ (c ≫ thφ τ.H (x3 τ.H) I) (q ≫ thφ HK (x3 HK) I) ∧
          (q ≫ thφ HK (x3 HK) I) ≫ τ.φ = x ≫ thφ C.A (x3 C.A) I := by
    intro x s hs hx
    choose c q k₁ k₂ k₃ using fun k => exists_lift τ (hs k) (hx k)
    let d : Fin 3 → (Over.mk (spMap τ.j) ⟶ τ.H) := fun k => Over.homMk (c k) (k₁ k).1
    let l : Over.mk (spMap τ.j) ⟶ G3 τ.H := lift (d 0) (lift (d 1) (d 2))
    have lx : ∀ k, l ≫ x3 τ.H k = d k := fun k => by fin_cases k <;> simp [l, x3]
    have lx' : ∀ k, l.left ≫ (x3 τ.H k).left = c k := fun k => congrArg (fun z => z.left) (lx k)
    have w : l.left ≫ (G3 τ.H).hom = spMap τ.j := Over.w l
    let Q : Sp (PadicAlgCl p) ⟶ (G3 HK).left := hK.lift (gPt p ≫ l.left) r
      ((Category.assoc _ _ _).trans ((congrArg (gPt p ≫ ·) w).trans hr))
    have hQ : Q ≫ (cubeMapOf gp).F3 = gPt p ≫ l.left := hK.lift_fst _ _ _
    have hQ' : ∀ k, Q ≫ (x3 HK k).left = q k := fun k => (cancel_mono (jg τ)).1
      ((Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (cubeMap_comp_proj_three (cubeMapOf gp) k).symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hQ).trans ((Category.assoc _ _ _).trans
          ((congrArg (gPt p ≫ ·) (lx' k)).trans (k₁ k).2.symm))))))
    have hx' : Q ≫ (cubeMapOf τ.φ_cart).F3 = x := hom_ext_triple _ fun k =>
      (Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (cubeMap_comp_proj_three (cubeMapOf τ.φ_cart) k)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.φ) (hQ' k)).trans (k₃ k))))
    refine ⟨l.left, Q, w, hQ, hx', fun I => ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (l.left ≫ ·) (Over.w (psum τ.H (x3 τ.H) I.down))).trans w)
    · exact (Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (h₁ I)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hQ).trans (Category.assoc _ _ _))))
    · exact (Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (h₂ I)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) hx')))
  obtain ⟨c, q, k₁, k₂, rfl, k₄⟩ := lifts x s hs hx
  refine ⟨_, _, k₄, fun a b ha hb => ?_⟩
  let u : Sp (PadicAlgCl p) ⟶ C.U.toScheme := r ≫ τ.yK
  have hu : u ≫ C.U.ι = gPt p ≫ y := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← hr, Category.assoc, τ.fac]
  let o : Over.mk u ⟶ C.A := 1
  have ho : o.left = u ≫ eSec C.A := by
    show (toUnit _ ≫ η[C.A]).left = _
    simp [eSec]
  have ox : ∀ k, lift o (lift o o) ≫ x3 C.A k = o := fun k => by fin_cases k <;> simp [x3]
  have oI : ∀ I : thK.{0}, (lift o (lift o o)).left ≫ thφ C.A (x3 C.A) I = o.left := fun I => by
    have e : lift o (lift o o) ≫ psum C.A (x3 C.A) I.down = psum C.A (fun _ => o) I.down :=
      (psum_hom (preHom (lift o (lift o o))) (x3 C.A) I.down).trans (congrArg (psum C.A · I.down) (funext ox))
    have e' : psum C.A (fun _ : Fin 3 => o) I.down = o := (psum_hom (1 : (Over.mk u ⟶ C.A) →* (Over.mk u ⟶ C.A))
      (fun _ => o) I.down).symm
    exact congrArg (fun z => z.left) (e.trans e')
  obtain ⟨c₀, q₀, m₁, m₂, m₃, m₄⟩ := lifts (lift o (lift o o)).left (fun _ => y ≫ C.e)
    (fun _ => (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) C.e_sec).trans (Category.comp_id _))) (fun k => by
      refine Eq.trans ?_ (congrArg (fun z => z.left ≫ C.a) (ox k)).symm
      rw [ho, ← Category.assoc, ← hu, Category.assoc, C.e_zero]
      exact (Category.assoc _ _ _).symm)
  have same := fun I => (m₄ I).1.unique hp (m₄ ⟨∅⟩).1 ((m₄ I).2.trans ((oI I).trans ((m₄ _).2.trans (oI _)).symm))
  obtain ⟨a₀, ha₀⟩ := exists_chart E.L.isLB ((c₀ ≫ thφ τ.H (x3 τ.H) (⟨∅⟩ : thK.{0})) (cPt p))
  choose J hJ using fun χ : Sp (PadicAlgCl p) ⟶ C.A.left => exists_chart T.L.isLB (χ (z₀ p))
  have key := gen_wv_eq E.L.isLB T.L.isLB E.w_gen hK (lift η[τ.H] (lift η[τ.H] η[τ.H])).left (Over.w _)
    (thφ τ.H (x3 τ.H)) (thφ HK (x3 HK)) (thφ C.A (x3 C.A)) (cubeMapOf τ.φ_cart).F3 h₁ h₂ (ε := thε) (t := T.cub.t)
    T.cub.isGen k₂ m₂ (k₁.trans m₁.symm) (a := a) (a' := fun _ => a₀) (b := b) (b' := fun _ => J o.left) ha
    (fun I => by rw [(same I).1]; exact ha₀) hb (fun I => by rw [m₃, oI]; exact hJ _)
  refine key.trans ?_
  have e₁ : gm (lift o (lift o o)).left (z₀ p) (LB.wchart T.L.L (thφ C.A (x3 C.A)) fun _ => J o.left)
      (T.cub.t.s fun _ => J o.left) = 1 :=
    (val_of (φ := thφ C.A (x3 C.A)) (ε := thε) T.cub.t _ _ J _ fun I => congrArg J (oI I)).symm.trans
      ((isCub_cubV T.cub (T := Over.mk u) hJ).face 1 1)
  rw [m₃]
  erw [e₁]
  rw [map_one, _root_.one_mul, Finset.prod_congr rfl fun I _ => by rw [(same I).2]]
  exact prod_thε (wv_pos _ _ _ _)

end Cube

end GlobalTheory.ZJ.TestNorm

namespace GlobalTheory.ZJ

open TestNorm CubeGen

theorem Core.Theta.exists_norms : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta), C.HasTests → T.BTest L → ∃ ν, T.Norms (T.Om L) ν := by
  intro hE C L T hT hB
  have hC : C.TestCart := fun p _ y τ => (L.test p y τ).1
  have sepG : IsSeparated C.GG.hom := (core_basic C).1
  have ex : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), C.Cl y →
      ∃ (τ : C.Test y) (E : T.Ext τ) (ρ : ℝ), 0 < ρ ∧ IsRigNorm E ρ := fun p _ y hy => by
    obtain ⟨τ⟩ := hT p y hy
    obtain ⟨E⟩ := Core.Theta.nonempty_ext hE C T p y τ hC
    exact ⟨τ, E, exists_isRigNorm E (hC p y τ)⟩
  choose τ E ρ hρ hR using ex
  have ex₂ : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left), ∃ n : T.L.L.ι → ℝ, (∀ j, 0 < n j) ∧
      (∀ j j', x (z₀ p) ∈ T.L.L.U j → x (z₀ p) ∈ T.L.L.U j' →
        un p (gm x (z₀ p) _ (T.L.L.g j j')) * n j = n j') ∧
      ∀ j t, (∃ (y : Sp (OO p) ⟶ C.Z) (hy : C.Cl y), ∃ c q a, IsLift (τ p y hy) c q ∧ q ≫ (τ p y hy).φ = x ∧
        c (cPt p) ∈ (E p y hy).L.L.U a ∧ x (z₀ p) ∈ T.L.L.U j ∧ t = wv (E p y hy).w q a j / ρ p y hy) → n j = t := by
    intro p _ x
    refine exists_norm_ext T.L.isLB x _ ?_ ?_
    · rintro j t ⟨y, hy, c, q, a, -, -, -, h, rfl⟩
      exact ⟨div_pos (wv_pos _ _ _ _) (hρ p y hy), h⟩
    · rintro j t j' t' ⟨y, hy, c, q, a, h₁, rfl, h₃, h₄, rfl⟩ ⟨y', hy', c', q', a', k₁, k₂, k₃, k₄, rfl⟩
      obtain rfl : y = y' := base_ext (by rw [← h₁.base, ← k₁.base, k₂])
      obtain ⟨rfl, rfl⟩ := h₁.unique (hC _ _ _) k₁ k₂.symm
      rw [← wv_trans (E p y hy).w_gen h₁.2 h₃ k₃ h₄ k₄, mul_div_assoc]
  choose ν h₁ h₂ h₃ using ex₂
  have hν : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (hy : C.Cl y) c q a j, IsLift (τ p y hy) c q →
      c (cPt p) ∈ (E p y hy).L.L.U a → (q ≫ (τ p y hy).φ) (z₀ p) ∈ T.L.L.U j →
      ν p (q ≫ (τ p y hy).φ) j = wv (E p y hy).w q a j / ρ p y hy :=
    fun p _ y hy c q a j k₁ k₂ k₃ => h₃ p _ j _ ⟨y, hy, c, q, a, k₁, rfl, k₂, k₃, rfl⟩
  have cl : ∀ {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} {u : Sp (PadicAlgCl p) ⟶ C.U.toScheme},
      gPt p ≫ y = u ≫ C.U.ι → C.Cl y := fun {p} _ {y u} h => by
    rw [Core.Cl, h]
    exact range_comp_ι_subset _ _
  have bas : ∀ {p : ℕ} [Fact p.Prime] {b : Sp (OO p) ⟶ C.G.toScheme} {x : Sp (PadicAlgCl p) ⟶ C.A.left},
      gPt p ≫ b = x ≫ C.a → gPt p ≫ b ≫ C.GG.hom = (x ≫ C.A.hom) ≫ C.U.ι := fun {p} _ {b x} h => by
    rw [← Category.assoc, h, Category.assoc, C.isPullback_a.w, Category.assoc]
  refine ⟨ν, ⟨h₁, fun p _ x i j hi hj => ?_, fun p _ s j hj => ?_⟩, fun p _ u ⟨y, hu, _⟩ J hJ => ?_,
    fun p _ x hx J hJ => ?_, fun p _ u => ?_⟩
  · have hi' := (range_subset_iff x (z₀ p) _).1 hi
    have hj' := (range_subset_iff x (z₀ p) _).1 hj
    rw [← un_gm x (U := T.L.L.U i ⊓ T.L.L.U j) ⟨hi', hj'⟩]
    exact h₂ p x i j hi' hj'
  · have e : gPt p ≫ s ≫ C.a = (gPt p ≫ s) ≫ C.a := (Category.assoc _ _ _).symm
    have hy := cl (bas e)
    obtain ⟨c, q, k₁, k₂, k₃⟩ := exists_lift (τ p _ hy) rfl e
    obtain ⟨a, ha⟩ := exists_chart (E p _ hy).L.isLB (c (cPt p))
    rw [← k₃, hν p _ hy c q a j k₁ ha (by rw [k₃]; exact gen_mem s hj), (hR p _ hy).integral k₁ k₂ ha hj,
      div_self (hρ p _ hy).ne']
  · have hy := cl hu
    obtain ⟨c, q, k₁, k₂, k₃⟩ := exists_lift (τ p y hy) (b := y ≫ C.e) (x := u ≫ eSec C.A)
      ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) C.e_sec).trans (Category.comp_id _))) (by
        rw [← Category.assoc, hu, Category.assoc, C.e_zero]
        exact (Category.assoc _ _ _).symm)
    obtain ⟨a, ha⟩ := exists_chart (E p _ hy).L.isLB (c (cPt p))
    have hJ' := (range_subset_iff u (z₀ p) _).1 hJ
    have hb : (q ≫ (τ p y hy).φ) (z₀ p) ∈ T.L.L.U (J ⟨⟩) := by
      rw [k₃]
      exact Set.mem_iInter.1 hJ' ⟨⟩
    have e₁ := hν p y hy c q a _ k₁ ha hb
    have e₂ := hR p y hy c q u a _ k₁ k₃ ha hb
    rw [k₃] at e₁
    rw [Fintype.prod_unique, zpow_one]
    refine (congrArg₂ (· * ·) (un_gm u hJ' _).symm e₁).trans ?_
    rw [← mul_div_assoc]
    exact (div_eq_one_iff_eq (hρ p y hy).ne').2 e₂
  · choose s hs _ using hx
    have e : ∀ k, gPt p ≫ s k ≫ C.GG.hom = (x ≫ (G3 C.A).hom) ≫ C.U.ι := fun k => by
      rw [bas (hs k), Category.assoc x, Over.w]
    have hy := cl (e 0)
    obtain ⟨c, q, k₁, k₂⟩ := cube_eq_one (E p _ hy) (hC _ _ _) x s (fun k => base_ext ((e k).trans (e 0).symm)) hs
    choose a ha using fun I => exists_chart (E p _ hy).L.isLB (c I (cPt p))
    have hJ' := (range_subset_iff x (z₀ p) _).1 hJ
    have hb : ∀ I, (x ≫ thφ C.A (x3 C.A) I) (z₀ p) ∈ T.L.L.U (J I) := Set.mem_iInter.1 hJ'
    refine (congrArg₂ (· * ·) (un_gm x hJ' _).symm (Finset.prod_congr rfl fun I _ => congrArg (· ^ thε I)
      ((congrArg (ν p · (J I)) (k₁ I).2.symm).trans
        (hν p _ hy _ _ (a I) (J I) (k₁ I).1 (ha I) (by rw [(k₁ I).2]; exact hb I))))).trans ?_
    simp only [div_zpow, Finset.prod_div_distrib]
    exact (congrArg (_ * ·) ((congrArg (_ / ·) (prod_thε (hρ p _ hy))).trans (div_one _))).trans (k₂ a J ha hb)
  · by_cases h : ∃ y : Sp (OO p) ⟶ C.Z, gPt p ≫ y = u ≫ C.U.ι
    swap
    · exact ⟨1, one_pos, fun x j hx _ ⟨b, hb, _⟩ => absurd ⟨_, hx ▸ bas hb⟩ h⟩
    obtain ⟨y, hu⟩ := h
    have hy := cl hu
    refine ⟨1 / ρ p y hy, one_div_pos.2 (hρ p y hy), fun x j hx hj ⟨b, hb, _⟩ => ?_⟩
    obtain ⟨c, q, k₁, k₂, rfl⟩ := exists_lift (τ p y hy) (base_ext ((bas hb).trans (by rw [hx, hu]))) hb
    obtain ⟨a, ha⟩ := exists_chart (E p _ hy).L.isLB (c (cPt p))
    have hj' := (range_subset_iff _ (z₀ p) _).1 hj
    obtain ⟨t₁, t₂⟩ := k₁.theta (E p y hy) ha hj'
    rw [hν p y hy c q a j k₁ ha hj', ← mul_div_assoc]
    refine ⟨div_le_div_of_nonneg_right t₁ (hρ p y hy).le, (div_left_inj' (hρ p y hy).ne').trans (t₂.trans
      ((hB p y _ (E p y hy) _ k₁.centre).symm.trans ?_))⟩
    have e : (τ p y hy).f (c (cPt p)) = b (cPt p) := congrArg (fun g => g (cPt p)) k₂
    rw [e]
    refine ⟨fun h => ⟨b, hb, h⟩, fun ⟨b', hb', h⟩ => ?_⟩
    rwa [ext_gPt C.GG.hom (base_ext ((bas hb).trans (bas hb').symm)) (hb.trans hb'.symm)]

end GlobalTheory.ZJ
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norms_of_tests : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta), C.HasTests → T.BTest L → ∃ ν, T.Norms (T.Om L) ν := by
  atlas_forward_decl GlobalTheory.ZJ.Core.Theta.exists_norms
end
