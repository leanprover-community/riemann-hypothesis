import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodUniformisationKodairaSpencer
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructure
import BuildAid.ForwardExisting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicPeriodicCocycleCoboundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructureStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AlgebraicCoboundaryOfHolomorphicCoboundary
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.ConstEndo

theorem unit_comp {S S₀ : Scheme.{0}} {f : S ⟶ S₀} {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀]
    {φ : X.left ⟶ X₀.left} (h : IsGrpPullback X X₀ f φ) :
    (η[X]).left ≫ φ = f ≫ (η[X₀]).left := by
  obtain ⟨hpb, hmul⟩ := h

  have hw : ((η[X]).left ≫ φ) ≫ X₀.hom = (𝟙_ (Over S)).hom ≫ f := by
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w]
  let x₀ : Over.mk ((𝟙_ (Over S)).hom ≫ f) ⟶ X₀ := Over.homMk ((η[X]).left ≫ φ) hw

  have hηη : (η[X] : 𝟙_ (Over S) ⟶ X) * η[X] = η[X] := by
    rw [MonObj.one_eq_one, _root_.one_mul]
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hmul (𝟙_ (Over S)) η[X] η[X] x₀ x₀ rfl rfl, hηη]
    rfl
  have h1 : x₀ = 1 := by
    simpa using hx
  have h2 := congrArg CommaMorphism.left h1
  simp only [x₀, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom,
    Over.tensorUnit_hom] at h2
  exact h2

private theorem surjective_of_isPullback_dualNumber_fst {A₀ : Over (Sp ℂ)} {A' : Over (Sp (DualNumber ℂ))} (j : A₀.left ⟶ A'.left)
    (h : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) :
    Function.Surjective j := by

  have hc : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
      rw [range_comap_of_surjective _ _ (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩)]
      intro x hx
      have hx0 : x.fst = 0 := hx
      apply p.isPrime.mem_of_pow_mem 2
      have hx' : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext hx0 rfl
      rw [hx', pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    exact hp
  have hs : Surjective (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := ⟨hc⟩
  exact (MorphismProperty.of_isPullback h.flip hs).surj

private theorem exists_unit_mul_eq_mul_uniformizer_pow {X S Y : Scheme.{0}} [IsAffine Y] (π : X ⟶ S)
    (hπ : Function.Bijective (π.appTop).hom) (g : X ⟶ Y) : ∃ c : S ⟶ Y, g = π ≫ c := by

  have : IsIso π.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hπ
  refine ⟨S.toSpecΓ ≫ Spec.map (inv π.appTop) ≫ Spec.map g.appTop ≫ inv Y.toSpecΓ, ?_⟩
  rw [← cancel_mono Y.toSpecΓ]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc,
    IsIso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem endo_comp_proj : Out.Laws → Out.Laws2 → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (f' : A' ⟶ A') (f₀ : P₀.A ⟶ P₀.A), IsAbelianScheme A' → IsMonHom f' → IsMonHom f₀ → j ≫ f'.left = f₀.left ≫ j → f'.left ≫ ρ = ρ ≫ f₀.left := by
  intro hL _ P₀ A' _ ρ j hc f' f₀ hab hf' hf₀ hj
  obtain ⟨hρ, hjp, hjρ⟩ := hc
  set ic : Sp (DualNumber ℂ) ⟶ Sp ℂ := spMap (algebraMap ℂ (DualNumber ℂ)) with hic
  have hwρ : ρ ≫ P₀.A.hom = A'.hom ≫ ic := hρ.1.w

  let T : Over (Sp ℂ) := Over.mk (A'.hom ≫ ic)
  let D : T ⟶ P₀.A := Over.homMk (f'.left ≫ ρ) (by
    simp only [T, Over.mk_hom, Category.assoc, hwρ]
    rw [← Category.assoc, Over.w])
  let E : T ⟶ P₀.A := Over.homMk (ρ ≫ f₀.left) (by
    simp only [T, Over.mk_hom, Category.assoc, Over.w, hwρ])
  suffices hDE : D = E from congrArg CommaMorphism.left hDE
  rw [← _root_.mul_inv_eq_one]
  set δ := D * E⁻¹ with hδ

  have hjT : j ≫ T.hom = P₀.A.hom := by
    simp only [T, Over.mk_hom]
    rw [← hwρ, ← Category.assoc, hjρ, Category.id_comp]
  let jT : P₀.A ⟶ T := Over.homMk j hjT
  have h1 : jT ≫ δ = 1 := by
    have hh : jT ≫ D = jT ≫ E := by
      ext1
      simp only [jT, D, E, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, hj, Category.assoc, hjρ, Category.comp_id, ← Category.assoc, hjρ,
        Category.id_comp]
    rw [hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]

  have hη : (η[A']).left ≫ ρ = ic ≫ (η[P₀.A]).left := unit_comp hρ
  have hηA : (η[A']).left ≫ A'.hom = 𝟙 _ := by
    rw [Over.w]; rfl
  let eT : Over.mk ic ⟶ T := Over.homMk (η[A']).left (by
    simp only [T, Over.mk_hom]
    rw [← Category.assoc, hηA]
    exact Category.id_comp _)
  have h2 : (eT ≫ δ).left = ic ≫ (η[P₀.A]).left := by
    have hh : eT ≫ D = eT ≫ E := by
      ext1
      simp only [eT, D, E, Over.comp_left, Over.homMk_left]
      have e1 : (η[A']).left ≫ f'.left = (η[A']).left := by
        rw [← Over.comp_left, IsMonHom.one_hom]
      have e2 : (η[P₀.A]).left ≫ f₀.left = (η[P₀.A]).left := by
        rw [← Over.comp_left, IsMonHom.one_hom]
      rw [← Category.assoc, e1, hη, ← Category.assoc, hη, Category.assoc, e2]
    rw [hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]
    simp [Hom.one_def]

  have hsurj := surjective_of_isPullback_dualNumber_fst j hjp.1
  obtain ⟨p₀⟩ : Nonempty (Sp ℂ) := inferInstance
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hxV, -⟩ :=
    P₀.A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show (η[P₀.A]).left p₀ ∈ (⊤ : P₀.A.left.Opens) from trivial) (⊤ : P₀.A.left.Opens).2
  let V : P₀.A.left.Opens := V₀
  have hrange : Set.range δ.left ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj x
    have e1 : (jT ≫ δ).left = (1 : P₀.A ⟶ P₀.A).left := by rw [h1]
    have e2 : δ.left (j y) = (η[P₀.A]).left (P₀.A.hom y) := by
      have := congrArg (fun m => m y) e1
      simpa [jT, Hom.one_def] using this
    rw [e2, Subsingleton.elim (P₀.A.hom y) p₀]
    exact hxV
  have : IsAffine V := hV
  have hG : Function.Bijective (A'.hom.appTop).hom := by
    have hgl := hL.globalFns
    unfold Out.GlobalFnsSt at hgl
    exact hgl _ A' hab
  obtain ⟨c, hc⟩ := exists_unit_mul_eq_mul_uniformizer_pow A'.hom hG (IsOpenImmersion.lift V.ι δ.left hrange)
  have hδc : δ.left = A'.hom ≫ c ≫ V.ι := by
    rw [← Category.assoc, ← hc, IsOpenImmersion.lift_fac]

  have h3 : c ≫ V.ι = ic ≫ (η[P₀.A]).left := by
    rw [← h2]
    simp only [eT, Over.comp_left, Over.homMk_left, hδc]
    rw [← Category.assoc, hηA]
    exact (Category.id_comp (c ≫ V.ι)).symm
  ext1
  rw [hδc, h3]
  simp [T, Hom.one_def]

end GlobalTheory.ConstEndo
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.endo_constant_family_dualNumbers_eq_baseChange : Out.Laws → Out.Laws2 → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (f' : A' ⟶ A') (f₀ : P₀.A ⟶ P₀.A), IsAbelianScheme A' → IsMonHom f' → IsMonHom f₀ → j ≫ f'.left = f₀.left ≫ j → f'.left ≫ ρ = ρ ≫ f₀.left := by
  first | exact @GlobalTheory.ConstEndo.endo_comp_proj | exact GlobalTheory.ConstEndo.endo_comp_proj | (intros; apply GlobalTheory.ConstEndo.endo_comp_proj <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.EpsCocycle

noncomputable section

lemma res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma cocycle_on {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  simpa only [map_mul, res_res] using this

def regauge {X : Scheme.{0}} (L : LB X) (u : ∀ i, Γ(X, L.U i)ˣ) : LB X :=
  ⟨L.ι, L.U, fun i i' => (res inf_le_left (u i))⁻¹ * L.g i i' * res inf_le_right (u i')⟩

lemma regauge_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    (regauge L u).IsLB where
  cover := hL.cover
  g_self := fun i => by
    have := hL.g_self i
    change res (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i)
      ((res inf_le_left (u i))⁻¹ * L.g i i * res inf_le_right (u i)) = 1
    simp only [map_mul, map_inv, res_res, this, _root_.mul_one, inv_mul_cancel]
  cocycle := fun i j k => by
    have := hL.cocycle i j k
    change res (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j)
        ((res inf_le_left (u i))⁻¹ * L.g i j * res inf_le_right (u j)) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k)
        ((res inf_le_left (u j))⁻¹ * L.g j k * res inf_le_right (u k)) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k)
        ((res inf_le_left (u i))⁻¹ * L.g i k * res inf_le_right (u k))
    simp only [map_mul, map_inv, res_res, ← this]
    group

lemma regauge_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    LBIso L (regauge L u) := by
  refine ⟨⟨fun p : L.ι × L.ι => ((res inf_le_left (u p.1))⁻¹ * L.g p.1 p.2 :
    Γ(X, L.U p.1 ⊓ L.U p.2)ˣ)⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨a', b'⟩
  let W : X.Opens := L.U a ⊓ L.U b ⊓ (L.U a' ⊓ L.U b')
  have ha : W ≤ L.U a := inf_le_left.trans inf_le_left
  have hb : W ≤ L.U b := inf_le_left.trans inf_le_right
  have ha' : W ≤ L.U a' := inf_le_right.trans inf_le_left
  have hb' : W ≤ L.U b' := inf_le_right.trans inf_le_right
  change res (le_inf ha hb) ((res inf_le_left (u a))⁻¹ * L.g a b) =
    (res (le_inf ha ha') ((res inf_le_left (u a))⁻¹ * L.g a a' * res inf_le_right (u a')) *
      (res (le_inf hb hb') (L.g b b'))⁻¹) *
      res (le_inf ha' hb') ((res inf_le_left (u a'))⁻¹ * L.g a' b')
  have e₁ := cocycle_on hL a a' b' (le_inf ha ha') (le_inf ha' hb') (le_inf ha hb')
  have e₂ := cocycle_on hL a b b' (le_inf ha hb) (le_inf hb hb') (le_inf ha hb')
  have e₃ : res (le_inf ha hb) (L.g a b) = res (le_inf ha ha') (L.g a a') *
      res (le_inf ha' hb') (L.g a' b') * (res (le_inf hb hb') (L.g b b'))⁻¹ := by
    rw [e₁, ← e₂, mul_inv_cancel_right]
  simp only [map_mul, map_inv, res_res, e₃]
  generalize res ha (u a) = x
  generalize res ha' (u a') = y
  generalize res (le_inf ha ha') (L.g a a') = z
  generalize res (le_inf ha' hb') (L.g a' b') = w
  generalize res (le_inf hb hb') (L.g b b') = v
  rw [mul_mul_mul_comm _ v⁻¹, mul_inv_cancel_right]
  ac_rfl

lemma appLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)) :
    (j.appLE O' O₂ h').hom ((ρ.appLE O O' h).hom a) = resG Y h'' a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Y) (_ : f = 𝟙 Y) (e : O₂ ≤ f ⁻¹ᵁ O), (f.appLE O O₂ e).hom a = resG Y h'' a := by
    intro f hf e
    subst hf
    simp [Scheme.Hom.appLE]
    rfl
  exact key _ hj _

lemma appLE_constFn_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)}
    {j : Y ⟶ Y'} (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    {O : Y.Opens} {O' : Y'.Opens} (h : O ≤ j ⁻¹ᵁ O') :
    (j.appLE O' O h).hom (constFn π O' DualNumber.eps) = 0 := by
  have h0 : O' ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  change (j.appLE O' O h).hom ((π.appLE ⊤ O' h0).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps)) = 0
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Sp (DualNumber ℂ))
      (_ : f = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (e : O ≤ f ⁻¹ᵁ ⊤),
      (f.appLE ⊤ O e).hom ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = 0 := by
    intro f hf e
    subst hf
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have e2 := congrArg (fun φ => φ.hom DualNumber.eps) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    have e3 : (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom DualNumber.eps = 0 := by
      simp
    rw [e3, map_zero] at e2
    exact (congrArg _ e2.symm).trans (map_zero _)
  exact key _ hq _

lemma eq_one_add_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)} {ρ : Y' ⟶ Y}
    {j : Y ⟶ Y'} (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (O' : Y'.Opens)
    (F : Γ(Y', O')) (hF : (j.appLE O' _ le_rfl).hom F = 1) :
    ∃ k : Γ(Y, j ⁻¹ᵁ O'), ∀ h : O' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ O'),
      F = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom k := by
  obtain ⟨h₁, -, h₃⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have key : ∀ (O : Y.Opens) (O' : Y'.Opens) (_ : ρ ⁻¹ᵁ O = O') (F : Γ(Y', O')), ∃ a b : Γ(Y, O),
      ∀ h : O' ≤ ρ ⁻¹ᵁ O,
        F = (ρ.appLE _ _ h).hom a + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom b := by
    intro O O' e F
    subst e
    obtain ⟨ab, hab, -⟩ := h₃ O F
    refine ⟨ab.1, ab.2, fun h => ?_⟩
    rw [Scheme.Hom.appLE_eq_app]
    exact hab
  obtain ⟨a, b, hab⟩ := key _ O' (h₁ O') F
  refine ⟨b, fun h => ?_⟩
  have ha : a = 1 := by
    rw [hab h, map_add, map_mul, appLE_constFn_eps hq, zero_mul, add_zero,
      appLE_section hj h le_rfl le_rfl] at hF
    have e : resG Y (le_refl (j ⁻¹ᵁ O')) a = a := by
      change (Y.presheaf.map (𝟙 _)).hom a = a
      rw [Y.presheaf.map_id]
      rfl
    exact e.symm.trans hF
  rw [hab h, ha, map_one]

def pullLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, V)ˣ := Units.map (f.appLE U V h).hom

lemma pullLE_eq {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (x : Γ(X, U)ˣ) : pullLE f h x = res h (pullU f U x) := by
  ext
  rfl

lemma pullLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U')
    (h' : U' ≤ U) (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pullLE f h (res h' x) = pullLE f h'' x := by
  ext
  simp only [pullLE, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma pullLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)ˣ) : pullLE j h' (pullLE ρ h a) = res h'' a := by
  ext
  exact appLE_section hj h h' h'' a.val

theorem exists_cocycle_one_add_eps : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ Q : LB Y', Q.IsLB → (∃ t : (Q.pull j).Gen, t.IsGen) → ∃ (Q' : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), Q'.IsLB ∧ LBIso Q Q' ∧ (∀ i i' (h : Q'.U i ⊓ Q'.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), (Q'.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) := by
  intro Y Y' q π ρ j hp hj hq Q hQ ⟨t, ht⟩
  obtain ⟨h₁, -, -⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have hw : ∀ i : Q.ι, j ⁻¹ᵁ Q.U i ≤ (Q.pull j).U (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  let s : ∀ i : Q.ι, Γ(Y, j ⁻¹ᵁ Q.U i)ˣ := fun i => res (hw i) (t.s fun _ => i)
  let u : ∀ i, Γ(Y', Q.U i)ˣ := fun i => pullLE ρ (h₁ (Q.U i)).ge (s i)
  have main : ∀ i i' : Q.ι, (j.appLE (Q.U i ⊓ Q.U i') _ le_rfl).hom ((regauge Q u).g i i').val = 1 := by
    intro i i'
    have hl : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have hr : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have e := congrArg (res (le_inf (hl.trans (hw i)) (hr.trans (hw i'))))
      (ht (fun _ => i) (fun _ => i'))
    have eg : res (le_inf (hl.trans (hw i)) (hr.trans (hw i')))
        ((Q.pull j).g (fun _ => i) (fun _ => i')) =
        pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (Q.g i i') := by
      rw [pullLE_eq]
      change res _ (∏ _k : PUnit.{1}, (res _ (pullU j _ (Q.g i i'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact res_res _ _ _
    rw [map_mul, res_res, res_res, eg] at e
    have : pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i')))
        ((res inf_le_left (u i))⁻¹ * Q.g i i' * res inf_le_right (u i')) = 1 := by
      rw [map_mul, map_mul, map_inv, pullLE_res j _ _ hl, pullLE_res j _ _ hr,
        pullLE_section hj _ _ hl, pullLE_section hj _ _ hr, res_res, res_res, _root_.mul_assoc, ← e,
        inv_mul_cancel]
    exact congrArg Units.val this
  choose k hk using fun i i' : Q.ι => eq_one_add_eps hp hj hq _ _ (main i i')
  exact ⟨regauge Q u, k, regauge_isLB hQ u, regauge_iso hQ u, hk⟩

end

end GlobalTheory.EpsCocycle
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_cocycle_one_add_eps : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ Q : LB Y', Q.IsLB → (∃ t : (Q.pull j).Gen, t.IsGen) → ∃ (Q' : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), Q'.IsLB ∧ LBIso Q Q' ∧ (∀ i i' (h : Q'.U i ⊓ Q'.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), (Q'.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) := by
  atlas_forward_decl GlobalTheory.EpsCocycle.exists_cocycle_one_add_eps
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.EpsBundle

theorem res_constFn' {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a := by
  exact congrArg (fun f => CommRingCat.Hom.hom f ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem res_appLE {Y Y' : Scheme.{0}} (ρ : Y' ⟶ Y) {O O' : Y.Opens} {W W' : Y'.Opens}
    (hW : W' ≤ W) (hO : O' ≤ O) (h : W ≤ ρ ⁻¹ᵁ O) (h' : W' ≤ ρ ⁻¹ᵁ O') (a : Γ(Y, O)) :
    resG Y' hW ((ρ.appLE O W h).hom a) = (ρ.appLE O' W' h').hom (resG Y hO a) := by
  unfold resG
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem eps_sq {X : Scheme.{0}} (p : X ⟶ Sp (DualNumber ℂ)) (U : X.Opens) :
    constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := by
  unfold constFn
  rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

theorem decomp {Y Y' : Scheme.{0}} (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (O : Y.Opens)
    (H : ∀ F : Γ(Y', ρ ⁻¹ᵁ O), ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2)
    (W : Y'.Opens) (hW : ρ ⁻¹ᵁ O = W) (h : W ≤ ρ ⁻¹ᵁ O) (F : Γ(Y', W)) :
    ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.appLE O W h).hom ab.1 + constFn π _ DualNumber.eps * (ρ.appLE O W h).hom ab.2 := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app]
  exact H F

theorem uniq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) {a b a' b' : A}
    (h : φ a + e * φ b = φ a' + e * φ b') : a = a' ∧ b = b' := by
  have := (H (φ a + e * φ b)).unique (y₁ := (a, b)) (y₂ := (a', b')) rfl h
  exact Prod.mk.inj this

theorem unit_form {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B) (he : e * e = 0)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) (u : Bˣ) :
    ∃ b b' c : A, b * b' = 1 ∧ (u : B) = φ b + e * φ c := by
  obtain ⟨⟨b, c⟩, h, -⟩ := H u
  obtain ⟨⟨b', c'⟩, h', -⟩ := H (u⁻¹ : Bˣ)
  refine ⟨b, b', c, ?_, h⟩
  have h1 : (u : B) * (u⁻¹ : Bˣ) = 1 := u.mul_inv
  rw [h', h] at h1
  refine (uniq φ e H (a := b * b') (b := b * c' + c * b') (a' := 1) (b' := 0) ?_).1
  simp only [map_mul, map_add, map_one, map_zero] at h1 ⊢
  linear_combination h1 - (φ c * φ c') * he

theorem overlap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : B) (he : e * e = 0)
    (H : ∀ F : B, ∃! ab : A × A, F = φ ab.1 + e * φ ab.2) {b b' c d d' c' k : A}
    (hb : b * b' = 1) (hd : d * d' = 1)
    (h : φ b + e * φ c = (1 + e * φ k) * (φ d + e * φ c')) : k = c * b' - c' * d' := by
  obtain ⟨h1, h2⟩ := uniq φ e H (a := b) (b := c) (a' := d) (b' := c' + k * d) (by
    simp only [map_mul, map_add]
    linear_combination h + (φ k * φ c') * he)
  subst h1
  have h3 : b' = d' := by linear_combination d' * hb - b' * hd + (0 : A)
  subst h3
  linear_combination (-b') * h2 - k * hb

theorem trivial_iff_coboundary : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (Q : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → ((∃ t : Q.Gen, t.IsGen) ↔ ∃ a : ∀ i, Γ(Y, j ⁻¹ᵁ Q.U i), ∀ i i', k i i' = resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i from fun _ hy => hy.1) (a i) - resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' from fun _ hy => hy.2) (a i')) := by
  intro Y Y' q π ρ j hp hj hq Q k _ hg
  obtain ⟨hO, -, hD⟩ := GlobalTheory.T.const_thickening_complex_functions_structure Y Y' q π ρ j hp hj hq
  have le : ∀ W : Y'.Opens, W ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ W) := fun W => (hO W).ge
  have H : ∀ (W : Y'.Opens) (F : Γ(Y', W)), ∃! ab : Γ(Y, j ⁻¹ᵁ W) × Γ(Y, j ⁻¹ᵁ W),
      F = (ρ.appLE _ W (le W)).hom ab.1 + constFn π _ DualNumber.eps * (ρ.appLE _ W (le W)).hom ab.2 :=
    fun W F => decomp π ρ _ (hD _) W (hO W) (le W) F
  constructor
  · rintro ⟨t, ht⟩
    choose b b' c hb hs using fun i =>
      unit_form (ρ.appLE _ (Q.U i) (le _)).hom _ (eps_sq π _) (H (Q.U i)) (t.s i)
    refine ⟨fun i => c i * b' i, fun i i' => ?_⟩
    have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have E : resG Y' inf_le_left (t.s i : Γ(Y', Q.U i)) =
        (Q.g i i').val * resG Y' inf_le_right (t.s i' : Γ(Y', Q.U i')) := congrArg Units.val (ht i i')
    rw [hg i i' (le _), hs, hs, map_add, map_add, map_mul, map_mul, res_constFn', res_constFn',
      res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _),
      res_appLE ρ _ l₂ _ (le _)] at E
    rw [map_mul, map_mul]
    exact overlap _ _ (eps_sq π _) (H _) (by rw [← map_mul, hb, map_one])
      (by rw [← map_mul, hb, map_one]) E
  · rintro ⟨a, ha⟩
    refine ⟨⟨fun i => ⟨1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i),
      1 - constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i), ?_, ?_⟩⟩, fun i i' => ?_⟩
    · linear_combination (-((ρ.appLE _ (Q.U i) (le _)).hom (a i)) ^ 2) * eps_sq π (Q.U i)
    · linear_combination (-((ρ.appLE _ (Q.U i) (le _)).hom (a i)) ^ 2) * eps_sq π (Q.U i)
    · have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
      have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
      apply Units.ext
      change resG Y' inf_le_left (1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i)) =
        (Q.g i i').val * resG Y' inf_le_right
          (1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i') (le _)).hom (a i'))
      rw [hg i i' (le _), map_add, map_add, map_mul, map_mul, map_one, map_one, res_constFn', res_constFn',
        res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _), ha i i', map_sub]
      linear_combination (-((ρ.appLE _ _ (le _)).hom (resG Y l₁ (a i)) -
        (ρ.appLE _ _ (le _)).hom (resG Y l₂ (a i'))) * (ρ.appLE _ _ (le _)).hom (resG Y l₂ (a i'))) *
        eps_sq π (Q.U i ⊓ Q.U i')

end GlobalTheory.KS.EpsBundle
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.EpsSym
open GlobalTheory.KS.EpsBundle

theorem period_eq_zero {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ)
    (hf : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {I : Type} (U : I → Set (Fin g → ℂ))
    (h : I → (Fin g → ℂ) → ℂ) (t : Fin g → ℂ) (a : I → I → (Fin g → ℂ) → ℂ)
    (ho : ∀ i, IsOpen (U i)) (hl : ∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) (hc : ∀ z, ∃ i, z ∈ U i)
    (hh : ∀ i, DifferentiableOn ℂ (h i) (U i) ∧
      ∀ (l : Λ), ∀ z ∈ U i, h i (z + l) = h i z + t ⬝ᵥ star (l : Fin g → ℂ))
    (ha : ∀ i i', DifferentiableOn ℂ (a i i') {z | -z ∈ U i ∧ z ∈ U i'})
    (hp : ∀ i i' (l : Λ) z, a i i' (z + l) = a i i' z)
    (hg : ∀ i i' m m' z, -z ∈ U i → z ∈ U i' → -z ∈ U m → z ∈ U m' →
      (h m (-z) - h i (-z)) - (h m' z - h i' z) = a i i' z - a m m' z) : t = 0 := by
  choose s hs using hc
  let F : I → I → (Fin g → ℂ) → ℂ := fun i i' z => a i i' z + h i (-z) - h i' z
  let v : (Fin g → ℂ) → ℂ := fun z => F (s (-z)) (s z) z
  have hv : ∀ i i' z, -z ∈ U i → z ∈ U i' → v z = F i i' z := fun i i' z h1 h2 => by
    have := hg i i' _ _ z h1 h2 (hs _) (hs _)
    simp only [v, F]
    linear_combination this
  have hO : ∀ i i', IsOpen {z | -z ∈ U i ∧ z ∈ U i'} := fun i i' =>
    ((ho i).preimage continuous_neg).inter (ho i')
  have hF : ∀ i i', DifferentiableOn ℂ (F i i') {z | -z ∈ U i ∧ z ∈ U i'} := fun i i' =>
    ((ha i i').add ((hh i).1.comp differentiableOn_id.neg fun z hz => hz.1)).sub
      ((hh i').1.mono fun z hz => hz.2)
  have hdiff : Differentiable ℂ v := fun z => by
    have hz : {w | -w ∈ U (s (-z)) ∧ w ∈ U (s z)} ∈ nhds z := (hO _ _).mem_nhds ⟨hs _, hs _⟩
    refine ((hF _ _).differentiableAt hz).congr_of_eventuallyEq ?_
    filter_upwards [hz] with w hw using hv _ _ w hw.1 hw.2
  have key := (GlobalTheory.entire_antilinear_periods_const g Λ hd hf v (-(t + t)) hdiff fun l z => by
    have e : -(z + (l : Fin g → ℂ)) = -z + ((-l : Λ) : Fin g → ℂ) := by
      rw [Submodule.coe_neg]; abel
    rw [hv (s (-z)) (s z) (z + l) (by rw [e]; exact hl _ _ _ (hs _)) (hl _ _ _ (hs _))]
    simp only [v, F]
    rw [e, (hh _).2 (-l) _ (hs _), (hh _).2 l _ (hs _), hp, Submodule.coe_neg, star_neg,
      dotProduct_neg, neg_dotProduct, add_dotProduct]
    ring).1
  funext b
  have := congrFun key b
  simp only [Pi.neg_apply, Pi.add_apply, Pi.zero_apply] at this ⊢
  linear_combination (-1 / 2 : ℂ) * this

variable {Y Y' : Scheme.{0}} {π : Y' ⟶ Sp (DualNumber ℂ)} {ρ : Y' ⟶ Y}

theorem appLE_one_add_eps {ν' : Y' ⟶ Y'} {ν : Y ⟶ Y} (h₁ : ν' ≫ π = π) (h₂ : ν' ≫ ρ = ρ ≫ ν)
    {W W₁ : Y'.Opens} {O O₁ : Y.Opens} (hW : W₁ ≤ ν' ⁻¹ᵁ W) (h : W ≤ ρ ⁻¹ᵁ O) (hO : O₁ ≤ ν ⁻¹ᵁ O)
    (h' : W₁ ≤ ρ ⁻¹ᵁ O₁) (x : Γ(Y, O)) :
    (ν'.appLE W W₁ hW).hom (1 + constFn π W DualNumber.eps * (ρ.appLE O W h).hom x) =
      1 + constFn π W₁ DualNumber.eps * (ρ.appLE O₁ W₁ h').hom ((ν.appLE O O₁ hO).hom x) := by
  have gen : ∀ {Z : Scheme.{0}} (f f' : Y' ⟶ Z) (_ : f = f') (V : Z.Opens) e e',
      f.appLE V W₁ e = f'.appLE V W₁ e' := by
    intro Z f f' hf V e e'
    subst hf
    rfl
  rw [map_add, map_mul, map_one]
  congr 2
  · exact congrArg (fun f => CommRingCat.Hom.hom f
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps))
      ((Scheme.Hom.appLE_comp_appLE ν' π ⊤ W W₁ (fun _ _ => trivial) hW).trans (gen _ _ h₁ _ _ _))
  · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE, gen _ _ h₂]

theorem val_mul_inv {B : Type} [CommRing B] (e x y : B) (he : e * e = 0) (u : Fin 2 → Bˣ)
    (hu : (u 0 : B) = 1 + e * x) (hv : (u 1 : B) = 1 + e * y) :
    ((∏ k, u k ^ (![1, -1] : Fin 2 → ℤ) k : Bˣ) : B) = 1 + e * (x - y) := by
  rw [Fin.prod_univ_two]
  change ((u 0 ^ (1 : ℤ) * u 1 ^ (-1 : ℤ) : Bˣ) : B) = _
  rw [zpow_one, zpow_neg_one, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, hu, hv]
  linear_combination (-(x - y) * y) * he

variable {q : Y ⟶ Sp ℂ} {j : Y ⟶ Y'}

theorem cocycle_val (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (Q : LB Y')
    (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (hQ : Q.IsLB)
    (hg : ∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))),
      (Q.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i'))
    (i i' i'' : Q.ι) (x : Sp ℂ ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i' ⊓ Q.U i''))) :
    valAt' x _ (k i i') + valAt' x _ (k i' i'') = valAt' x _ (k i i'') := by
  obtain ⟨hO, -, hD⟩ := GlobalTheory.T.const_thickening_complex_functions_structure Y Y' q π ρ j hp hj hq
  have le : ∀ W : Y'.Opens, W ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ W) := fun W => (hO W).ge
  have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i' ⊓ Q.U i'') ≤ j ⁻¹ᵁ (Q.U i ⊓ Q.U i') := fun _ hy => hy.1
  have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i' ⊓ Q.U i'') ≤ j ⁻¹ᵁ (Q.U i' ⊓ Q.U i'') := fun _ hy => ⟨hy.1.2, hy.2⟩
  have l₃ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i' ⊓ Q.U i'') ≤ j ⁻¹ᵁ (Q.U i ⊓ Q.U i'') := fun _ hy => ⟨hy.1.1, hy.2⟩
  have E : resG Y' (inf_le_left : Q.U i ⊓ Q.U i' ⊓ Q.U i'' ≤ _) (Q.g i i').val *
      resG Y' (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (Q.g i' i'').val =
      resG Y' (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (Q.g i i'').val :=
    congrArg Units.val (hQ.cocycle i i' i'')
  rw [hg _ _ (le _), hg _ _ (le _), hg _ _ (le _)] at E
  simp only [map_add, map_mul, map_one, res_constFn'] at E
  rw [res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _), res_appLE ρ _ l₃ _ (le _)] at E
  have := (uniq (ρ.appLE _ _ (le (Q.U i ⊓ Q.U i' ⊓ Q.U i''))).hom _
    (fun F => decomp π ρ _ (hD _) _ (hO _) (le _) F) (a := 1) (a' := 1)
    (b := resG Y l₁ (k i i') + resG Y l₂ (k i' i'')) (b' := resG Y l₃ (k i i'')) (by
      rw [map_one, map_add]
      linear_combination E - ((ρ.appLE _ _ (le _)).hom (resG Y l₁ (k i i')) *
        (ρ.appLE _ _ (le _)).hom (resG Y l₂ (k i' i''))) * eps_sq π (Q.U i ⊓ Q.U i' ⊓ Q.U i''))).2
  rw [← valAt'_res x l₁ _ hx, ← valAt'_res x l₂ _ hx, ← valAt'_res x l₃ _ hx, ← valAt'_add, this]

theorem odd_part_coboundary (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (Q : LB Y')
    (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (hQ : Q.IsLB)
    (hg : ∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))),
      (Q.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i'))
    {ν' : Y' ⟶ Y'} {ν : Y ⟶ Y} (h₁ : ν' ≫ π = π) (h₂ : ν' ≫ ρ = ρ ≫ ν) (h₃ : j ≫ ν' = ν ≫ j)
    (ht : ∃ t : (LB.LinComb Q (K := Fin 2) ![ν', 𝟙 Y'] ![1, -1]).Gen, t.IsGen) :
    ∃ (W : Q.ι → Q.ι → Y.Opens) (a : ∀ i i', Γ(Y, W i i')),
      (∀ i i', W i i' = ν ⁻¹ᵁ (j ⁻¹ᵁ Q.U i) ⊓ j ⁻¹ᵁ Q.U i') ∧
      ∀ i i' m m' (x : Sp ℂ ⟶ Y), ⊤ ≤ x ⁻¹ᵁ W i i' → ⊤ ≤ x ⁻¹ᵁ W m m' →
        valAt' (x ≫ ν) _ (k i m) - valAt' x _ (k i' m') = valAt' x _ (a i i') - valAt' x _ (a m m') := by
  obtain ⟨hO, -, -⟩ := GlobalTheory.T.const_thickening_complex_functions_structure Y Y' q π ρ j hp hj hq
  have le : ∀ W : Y'.Opens, W ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ W) := fun W => (hO W).ge
  let Q' := LB.LinComb Q (K := Fin 2) ![ν', 𝟙 Y'] ![1, -1]
  have hW : ∀ J : Fin 2 → Q.ι, j ⁻¹ᵁ Q'.U J = ν ⁻¹ᵁ (j ⁻¹ᵁ Q.U (J 0)) ⊓ j ⁻¹ᵁ Q.U (J 1) := fun J => by
    rw [← Scheme.Hom.comp_preimage, ← h₃]
    ext y
    exact Set.mem_iInter.trans Fin.forall_fin_two
  have l₀ : ∀ J J' : Fin 2 → Q.ι, j ⁻¹ᵁ (Q'.U J ⊓ Q'.U J') ≤ ν ⁻¹ᵁ (j ⁻¹ᵁ (Q.U (J 0) ⊓ Q.U (J' 0))) :=
    fun J J' y hy => ⟨((hW J).le hy.1).1, ((hW J').le hy.2).1⟩
  have l₁ : ∀ J J' : Fin 2 → Q.ι, j ⁻¹ᵁ (Q'.U J ⊓ Q'.U J') ≤ (𝟙 Y) ⁻¹ᵁ (j ⁻¹ᵁ (Q.U (J 1) ⊓ Q.U (J' 1))) :=
    fun J J' y hy => ⟨((hW J).le hy.1).2, ((hW J').le hy.2).2⟩
  obtain ⟨a, ha⟩ := (trivial_iff_coboundary Y Y' q π ρ j hp hj hq Q'
    (fun J J' => (ν.appLE _ _ (l₀ J J')).hom (k (J 0) (J' 0)) -
      (Scheme.Hom.appLE (𝟙 Y) _ _ (l₁ J J')).hom (k (J 1) (J' 1))) (LB.isLB_linComb hQ _ _) fun J J' h => by
      rw [map_sub]
      have m : ∀ n, Q'.U J ⊓ Q'.U J' ≤ (![ν', 𝟙 Y'] : Fin 2 → _) n ⁻¹ᵁ (Q.U (J n) ⊓ Q.U (J' n)) :=
        fun n y hy => ⟨LB.wchart_le Q _ J n hy.1, LB.wchart_le Q _ J' n hy.2⟩
      refine val_mul_inv _ _ _ (eps_sq π _) _ ?_ ?_
      · refine Eq.trans ?_ (appLE_one_add_eps h₁ h₂ (m 0) (le _) _ h _)
        rw [← hg]
        rfl
      · refine Eq.trans ?_ (appLE_one_add_eps (ν' := 𝟙 Y') (Category.id_comp _) (by simp) (m 1) (le _) _ h _)
        rw [← hg]
        rfl).1 ht
  refine ⟨fun i i' => j ⁻¹ᵁ Q'.U ![i, i'], fun i i' => a ![i, i'], fun i i' => hW _, ?_⟩
  intro i i' m m' x hx hx'
  have hxx : ⊤ ≤ x ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U ![i, i'] ⊓ Q'.U ![m, m'])) := fun p hp => ⟨hx hp, hx' hp⟩
  have E := congrArg (valAt' x _) (ha ![i, i'] ![m, m'])
  rw [valAt'_sub, valAt'_sub, valAt'_res _ _ _ hxx, valAt'_res _ _ _ hxx, valAt'_appLE _ _ _ _ _ _ hxx,
    valAt'_appLE _ _ _ _ _ _ hxx, Category.comp_id] at E
  exact E

theorem gen_of_sym (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (Q : LB A'.left) (h : Out.Sym A' Q) :
    ∃ t : (LB.LinComb Q (K := Fin 2) ![(GrpObj.inv : A' ⟶ A').left, 𝟙 A'.left] ![1, -1]).Gen, t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := h (IsLocalRing.closedPoint (DualNumber ℂ))
  have hU' : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  subst hU'
  let s : A'.left ⟶ (A'.hom ⁻¹ᵁ ⊤).toScheme := A'.left.topIso.inv
  have hs : s ≫ (A'.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ := A'.left.topIso.inv_hom_id
  have e : (fun k => s ≫ (![(A'.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : A' ⟶ A').left, (A'.hom ⁻¹ᵁ ⊤).ι] :
      Fin 2 → _) k) = ![(GrpObj.inv : A' ⟶ A').left, 𝟙 A'.left] := by
    funext k
    fin_cases k
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _))
    · exact hs
  rw [← e]
  exact ⟨_, DVR.pullGen_isGen_of_isGen _ _ t ht s⟩

theorem trivial_of_symmetric : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (Q : LB A'.left) (k : ∀ i i', Γ(P₀.A.left, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn A'.hom _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → Out.Sym A' Q → ∃ t : Q.Gen, t.IsGen := by
  intro laws P₀ u Hm χ hu A' _ ρ j hc Q k hQ hg hs
  obtain ⟨g₁, g₂, hj⟩ := hc
  have hq := g₂.1.w
  let U : Q.ι → Set (Fin P₀.g → ℂ) := fun i => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (j ⁻¹ᵁ Q.U i)}
  have hper : ∀ z (l : u.Λ), u.ex (z + l) = u.ex z := fun z l => CubeValues.ex_add_period u z l l.2
  have hcov : ⨆ i, j ⁻¹ᵁ Q.U i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hQ.cover]; rfl
  have ho : ∀ i, IsOpen (U i) := fun i => (u.hol _ 0).1
  have hl : ∀ i (l : u.Λ) z, z ∈ U i → z + l ∈ U i := fun i l z hz => by
    simp only [U, Set.mem_setOf_eq, hper]; exact hz
  have hcv : ∀ z, ∃ i, z ∈ U i := fun z => by
    have h : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, j ⁻¹ᵁ Q.U i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  have hin : ∀ {i i' z}, z ∈ U i → z ∈ U i' → ⊤ ≤ (u.ex z).left ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i')) :=
    fun h h' p hp => ⟨h hp, h' hp⟩
  obtain ⟨t, h, hh, hk⟩ := GlobalTheory.holomorphic_periodic_cocycle_coboundary P₀.g u.Λ u.discrete u.full Q.ι U
    (fun i i' z => valAt' (u.ex z).left _ (k i i')) ho hl hcv
    (fun i i' => (u.hol _ (k i i')).2.mono fun z hz => hin hz.1 hz.2)
    (fun i i' l z _ => by simp only [hper])
    (fun i i' i'' z hz => cocycle_val g₁.1 hj hq Q k hQ hg i i' i'' _
      fun p hp => ⟨⟨hz.1.1 hp, hz.1.2 hp⟩, hz.2 hp⟩)
  obtain ⟨W, a, hW, ha⟩ := odd_part_coboundary g₁.1 hj hq Q k hQ hg (Over.w (GrpObj.inv : A' ⟶ A'))
    (PolBaseChange.inv_comm g₁) (PolBaseChange.inv_comm g₂).symm (gen_of_sym A' Q hs)
  have hW' : ∀ {i i' z}, -z ∈ U i → z ∈ U i' → ⊤ ≤ (u.ex z).left ⁻¹ᵁ W i i' := fun {i i' z} h h' => by
    rw [hW, top_le_preimage_inf, ← top_le_preimage_comp, SymmetricSemicharacter.ex_neg_left]
    exact ⟨h, h'⟩
  have ht : t = 0 := period_eq_zero u.Λ u.discrete u.full U h t
    (fun i i' z => valAt' (u.ex z).left _ (a i i')) ho hl hcv hh
    (fun i i' => (u.hol _ (a i i')).2.mono fun z hz => hW' hz.1 hz.2)
    (fun i i' l z => by simp only [hper])
    (fun i i' m m' z h₁ h₂ h₃ h₄ => by
      have E := ha i i' m m' _ (hW' h₁ h₂) (hW' h₃ h₄)
      rw [SymmetricSemicharacter.ex_neg_left] at E
      rw [← hk i m (-z) ⟨h₁, h₃⟩, ← hk i' m' z ⟨h₂, h₄⟩]
      exact E)
  subst ht
  choose b hb using algebraic_coboundary_of_holomorphic_coboundary laws P₀ u Hm χ hu Q.ι
    (fun i => j ⁻¹ᵁ Q.U i) (fun i i' => k i i') h hcov
    (fun i => ⟨(hh i).1, fun l z hz => by rw [(hh i).2 l z hz, zero_dotProduct, add_zero]⟩)
    (fun i i' z hz => hk i i' z ⟨fun p hp => (hz hp).1, fun p hp => (hz hp).2⟩)
  refine (trivial_iff_coboundary _ _ _ _ ρ j g₁.1 hj hq Q k hQ hg).2 ⟨fun i => - b i, fun i i' => ?_⟩
  refine (GlobalTheory.existsUnique_section_of_locally_regular P₀ u Hm χ hu (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))
    (fun z => valAt' (u.ex z).left _ (k i i'))
    (fun z hz => ⟨_, k i i', le_rfl, hz, fun _ _ => rfl⟩)).unique (fun _ _ => rfl) fun z hz => ?_
  have z₁ : z ∈ U i := fun p hp => (hz hp).1
  have z₂ : z ∈ U i' := fun p hp => (hz hp).2
  rw [valAt'_sub, valAt'_res _ _ _ hz, valAt'_res _ _ _ hz, valAt'_neg, valAt'_neg, hb i z z₁, hb i' z z₂]
  exact ((hk i i' z ⟨z₁, z₂⟩).trans (by ring)).symm

end GlobalTheory.KS.EpsSym
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_bundle_trivial_constant_family_dualNumber : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (Q : LB A'.left) (k : ∀ i i', Γ(P₀.A.left, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn A'.hom _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → Out.Sym A' Q → ∃ t : Q.Gen, t.IsGen := by
  atlas_forward_decl GlobalTheory.KS.EpsSym.trivial_of_symmetric
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.SymRigid

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem sym_iff_cls {L : LB A.left} (hL : L.IsLB) : Out.Sym A L ↔ ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) = pull (A.hom ⁻¹ᵁ U).ι (cls L hL) := by
  refine forall_congr' fun s => exists_congr fun U => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL, Fin.sum_univ_two]
  change (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) +
    (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = 0 ↔ _
  rw [one_zsmul, neg_one_zsmul, add_neg_eq_zero]

theorem pull_restrict {U V : S.Opens} (h : V ≤ U) {c : Pic A.left}
    (e : pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) c = pull (A.hom ⁻¹ᵁ U).ι c) :
    pull ((A.hom ⁻¹ᵁ V).ι ≫ (GrpObj.inv : A ⟶ A).left) c = pull (A.hom ⁻¹ᵁ V).ι c := by
  have hle : A.hom ⁻¹ᵁ V ≤ A.hom ⁻¹ᵁ U := fun _ hx => h hx
  rw [← Scheme.homOfLE_ι A.left hle, Category.assoc, pull_comp, e, ← pull_comp]

theorem sym_of_cls_eq_sub {L M Q : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (hQ : Q.IsLB)
    (e : cls Q hQ = cls L hL - cls M hM) (sL : Out.Sym A L) (sM : Out.Sym A M) : Out.Sym A Q := by
  refine (sym_iff_cls hQ).2 fun s => ?_
  obtain ⟨U, hU, eU⟩ := (sym_iff_cls hL).1 sL s
  obtain ⟨V, hV, eV⟩ := (sym_iff_cls hM).1 sM s
  refine ⟨U ⊓ V, ⟨hU, hV⟩, ?_⟩
  rw [e, map_sub, map_sub, pull_restrict inf_le_left eU, pull_restrict inf_le_right eV]

theorem lbIso_pull_of_isConst : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ M : LB A'.left, M.IsLB → Out.Sym A' M → LBIso P₀.L (M.pull j) → LBIso M (P₀.L.pull ρ) := by
  intro laws P₀ u Hm χ hu A' _ ρ j hc M hM sM H
  have hL := pull_isLB P₀.isLB ρ
  have hQ : (LB.div (P₀.L.pull ρ) M).IsLB := LB.isLB_div hL hM
  have e₀ : cls _ P₀.isLB = pull j (cls M hM) := (cls_eq_iff _ (pull_isLB hM j)).2 H
  have triv : ∃ t : ((LB.div (P₀.L.pull ρ) M).pull j).Gen, t.IsGen := by
    rw [← cls_eq_zero_iff (pull_isLB hQ j), cls_pull hQ, cls_div hL hM, map_sub, cls_pull P₀.isLB, ← pull_comp,
      hc.2.2, pull_id, e₀, sub_self]
  obtain ⟨Q, k, hQ', iso, hk⟩ := GlobalTheory.T.exists_lineBundle_cocycle_one_add_eps _ _ P₀.A.hom A'.hom ρ j hc.1.1 hc.2.2 hc.2.1.1.w _ hQ triv
  have e : cls Q hQ' = cls _ hL - cls M hM := ((cls_eq_iff hQ hQ').2 iso).symm.trans (cls_div hL hM hQ)
  have z := (cls_eq_zero_iff hQ').2 (GlobalTheory.T.symmetric_bundle_trivial_constant_family_dualNumber laws P₀ u Hm χ hu A' ρ j hc Q k hQ' hk
    (sym_of_cls_eq_sub hL hM hQ' e (PolBaseChange.sym_pull hc.1 P₀.sym) sM))
  exact (cls_eq_iff hM hL).1 (sub_eq_zero.1 (e.symm.trans z)).symm

end GlobalTheory.SymRigid
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem torsion_section_const : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (k : ℕ) (y : Out.baseOver (Sp (DualNumber ℂ)) ⟶ A') (y₀ : Out.baseOver (Sp ℂ) ⟶ P₀.A), k ≠ 0 → y ^ k = 1 → y₀ ^ k = 1 → (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ y.left = y₀.left ≫ j → y.left ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y₀.left := by
  intro _ P₀ A' _ ρ j hc k y y₀ hk hy hy₀ hyj
  letI := P₀.isAb.comm
  have hu : IsUnit ((k : ℕ) : Γ(Sp ℂ, ⊤)) := by
    let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    refine (MulEquiv.isUnit_map e.toMulEquiv).mp ?_
    have he : e.toMulEquiv (k : Γ(Sp ℂ, ⊤)) = (k : ℂ) := map_natCast e k
    rw [he]
    exact (Nat.cast_ne_zero.mpr hk).isUnit
  exact GlobalTheory.ConstTheta.torsion_const hc.1 hc.2.2 hu y y₀ hy hy₀ hyj.symm

end GlobalTheory.KS
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionSection_constantFamily_dualNumbers : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (k : ℕ) (y : Out.baseOver (Sp (DualNumber ℂ)) ⟶ A') (y₀ : Out.baseOver (Sp ℂ) ⟶ P₀.A), k ≠ 0 → y ^ k = 1 → y₀ ^ k = 1 → (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ y.left = y₀.left ≫ j → y.left ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y₀.left := by
  atlas_forward_decl GlobalTheory.KS.torsion_section_const
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.KS
private theorem k_ne_zero_lemma {o : Type} [CommRing o] {k : ℕ} (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) :
    k ≠ 0 := by
  rintro rfl
  have h0 : (0 : o) = 1 := isUnit_zero_iff.mp (by simpa using b.unit)
  haveI : Subsingleton o := subsingleton_of_zero_eq_one h0
  obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum ℂ))
  exact (s₀.base x).isPrime.ne_top (Subsingleton.elim _ _)

theorem tMap_of_isConst : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) (s' : Sp (DualNumber ℂ) ⟶ Sp o) (t₀ : TObj g k J b s₀) (t' : TObj g k J b s') (ρ : t'.A.left ⟶ t₀.A.left) (j : t₀.A.left ⟶ t'.A.left), IsConst t'.A t₀.A ρ j → (IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ LBIso t₀.L (t'.L.pull j) ∧ (∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left) → TMap t' t₀ (spMap (algebraMap ℂ (DualNumber ℂ))) := by
  intro hL hL2 hT o _ g k J b s₀ s' t₀ t' ρ j hc ⟨hpb, hlb, hpt, hact⟩
  have hk : k ≠ 0 := k_ne_zero_lemma b s₀
  refine ⟨ρ, hc.1, ?_, ?_, ?_⟩
  · obtain ⟨u, Hm, χ, hu, -⟩ := GlobalTheory.KSInh.exists_goodU_ksRel hT t₀.pol
    exact GlobalTheory.SymRigid.lbIso_pull_of_isConst hL t₀.pol u Hm χ hu t'.A ρ j hc t'.L t'.isLB t'.sym hlb
  · intro i
    exact GlobalTheory.T.torsionSection_constantFamily_dualNumbers hL t₀.pol t'.A ρ j hc k (t'.pt i) (t₀.pt i) hk (t'.torsion i) (t₀.torsion i) (hpt i).symm
  · intro jj
    exact GlobalTheory.T.endo_constant_family_dualNumbers_eq_baseChange hL hL2 t₀.pol t'.A ρ j hc (t'.act jj) (t₀.act jj) t'.ab (t'.hom jj) (t₀.hom jj) (hact jj).symm
end GlobalTheory.KS
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaObject_constantFamily_dualNumbers_isPullback : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) (s' : Sp (DualNumber ℂ) ⟶ Sp o) (t₀ : TObj g k J b s₀) (t' : TObj g k J b s') (ρ : t'.A.left ⟶ t₀.A.left) (j : t₀.A.left ⟶ t'.A.left), IsConst t'.A t₀.A ρ j → (IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ LBIso t₀.L (t'.L.pull j) ∧ (∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left) → TMap t' t₀ (spMap (algebraMap ℂ (DualNumber ℂ))) := by
  atlas_forward_decl GlobalTheory.KS.tMap_of_isConst
end
