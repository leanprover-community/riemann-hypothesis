import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal

section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FieldBaseChange

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_finset_representatives (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {k : ℕ} (hk : 1 ≤ k) : ∃ T : Finset X, ∀ β, ∃ α ∈ T, ∃ mu, β = α + k • mu := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨Finset.univ.image fun r : _ → Fin k => ∑ i, ((r i : ℕ) : ℤ) • b i, fun β =>
    ⟨∑ i, (b.repr β i % k) • b i, Finset.mem_image.2 ⟨fun i => ⟨(b.repr β i % k).toNat, ?_⟩,
      Finset.mem_univ _, Finset.sum_congr rfl fun i _ => ?_⟩, ∑ i, (b.repr β i / k) • b i, ?_⟩⟩
  · have := Int.emod_lt_of_pos (b.repr β i) hk'
    have := Int.emod_nonneg (b.repr β i) hk'.ne'
    omega
  · show (((b.repr β i % k).toNat : ℕ) : ℤ) • b i = _
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hk'.ne')]
  · conv_lhs => rw [← b.sum_repr β]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← natCast_zsmul, smul_smul, ← add_smul, Int.emod_add_mul_ediv]

section Shift

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

def famBase : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.P.A).left

abbrev FamTerm (k : ℕ) (α : D.X) : Type :=
  SecOver (famBase D F) (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))

def famProj (k : ℕ) (α : D.X) : Fam D F k →ₗ[F] FamTerm D F k α where
  toFun s := s.s α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def shiftVal (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) : (T.left.presheaf.stalk z)ˣ :=
  uVal D F k α (cP D _ mu) ρ z J * val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J

def IsShift (k : ℕ) (mu α : D.X) (Θ : FamTerm D F k α →ₗ[F] FamTerm D F k (α + k • mu)) : Prop :=
  ∀ (s : FamTerm D F k α) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J),
    Good D.P.L z J → sval (Θ s) ρ.left z J =
      sval s (ρ.left ≫ (DegPre.trF D F mu).left) z J * (shiftVal D F k mu α ρ z J).val

theorem trF_famBase (mu : D.X) : (DegPre.trF D F mu).left ≫ famBase D F = famBase D F :=
  congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ fst _ _ = _)

theorem exists_isShift (hG : GlobalFnsSt) (k : ℕ) (mu α : D.X) : ∃ Θ, IsShift D F k mu α Θ := by
  have hL := D.P.isLB
  obtain ⟨⟨v, hv, hc⟩, hu⟩ := gen_fe (D := D) (F := F) hG k mu α
  have tr : ∀ σ : FamTerm D F k α, ∃ t : FamTerm D F k (α + k • mu),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval t r z J = sval σ (r ≫ (DegPre.trF D F mu).left) z J * (val v r z J).val := fun σ => by
    obtain ⟨t, ht⟩ := exists_sec hL (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [DegPre.deltaφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
          Finset.prod_inv_distrib]
        try (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel))
      (φ' := DegPre.famφ D F (α + k • mu)) (ε' := DegPre.famε k) (pullMulSec σ (DegPre.trF D F mu).left v hv)
    exact ⟨t, fun Z r z J hJ => (ht Z r z J hJ).trans (sval_pullMulSec _ _ _ hv r z hJ)⟩
  choose t ht using tr
  refine ⟨{ toFun := t
            map_add' := fun a b => sec_ext' hL fun y J hJ => ?_
            map_smul' := fun c a => sec_ext' hL fun y J hJ => ?_ }, fun s T ρ z J hJ => ?_⟩
  · rw [sval_add' hJ, ht _ _ _ y J hJ, ht _ _ _ y J hJ, ht _ _ _ y J hJ, sval_add' hJ, add_mul]
  · rw [sval_smul' hJ, ht _ _ _ y J hJ, ht _ _ _ y J hJ, sval_smul' hJ, Category.assoc, trF_famBase,
      _root_.mul_assoc]
    rfl
  · exact (ht s _ _ z J hJ).trans (congrArg (fun u : (T.left.presheaf.stalk z)ˣ => _ * u.val)
      (hu v hv hc T ρ z J hJ))

variable {D F}

theorem famFE_iff (hG : GlobalFnsSt) {k : ℕ}
    {Θ : ∀ mu α, FamTerm D F k α →ₗ[F] FamTerm D F k (α + k • mu)} (hΘ : ∀ mu α, IsShift D F k mu α (Θ mu α))
    (s : ∀ α, FamTerm D F k α) : DegPre.FamFE D F k s ↔ ∀ mu α, s (α + k • mu) = Θ mu α (s α) := by
  have hL := D.P.isLB
  constructor
  · intro H mu α
    obtain ⟨⟨v, hv, hc⟩, hu⟩ := gen_fe (D := D) (F := F) hG k mu α
    refine sec_ext' hL fun y J hJ => ?_
    refine ((secRel_iff hL _ _ _ _ _ _ _ _ _ v).1 (H mu α v hv hc) _ (𝟙 _) y J hJ).trans ?_
    exact (congrArg (fun u : ((DegPre.BF D F).left.presheaf.stalk y)ˣ => _ * u.val)
      (hu v hv hc _ (𝟙 _) y J hJ)).trans (hΘ mu α (s α) _ (𝟙 _) y J hJ).symm
  · intro H mu α u hu hc
    refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    refine (congrArg (fun t => sval t (𝟙 _) y J) (H mu α)).trans ((hΘ mu α (s α) _ (𝟙 _) y J hJ).trans ?_)
    exact (congrArg (fun u : ((DegPre.BF D F).left.presheaf.stalk y)ˣ => _ * u.val)
      ((gen_fe (D := D) (F := F) hG k mu α).2 u hu hc _ (𝟙 _) y J hJ)).symm

end Shift

section Pull

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (E F : Type) [Field F] [Algebra (FractionRing R) F]
  [Field E] [Algebra (FractionRing R) E] [Algebra E F]
  [IsScalarTower (FractionRing R) E F]

theorem specMap_jFK : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F := by
  rw [jFK, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

def baseMap : TF (R := R) F ⟶ TF (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E ≫ jK R = jFK (R := R) F ≫ jK R
    rw [← Category.assoc, specMap_jFK])

def famMap : DegPre.BF D F ⟶ DegPre.BF D E := lift (fst _ _ ≫ baseMap (R := R) E F) (snd _ _)

theorem famMap_fst : famMap D E F ≫ fst _ _ = fst _ _ ≫ baseMap (R := R) E F := lift_fst _ _

theorem famMap_snd : famMap D E F ≫ DegPre.prB D _ = DegPre.prB D F := lift_snd _ _

theorem isPullback_famMap : IsPullback (famMap D E F).left (famBase D F) (famBase D E)
    (Spec.map (CommRingCat.ofHom (algebraMap E F))) := by
  have h₁ : IsPullback (snd (TF (R := R) E) D.P.A).left (famBase D E)
      D.P.A.hom (TF (R := R) E).hom := (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (snd (TF (R := R) F) D.P.A).left (famBase D F)
      D.P.A.hom (TF (R := R) F).hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (congrArg (fun q => q.left) (famMap_fst D E F)) h₁
  have e₁ : (famMap D E F).left ≫ (snd (TF (R := R) E) D.P.A).left =
      (snd (TF (R := R) F) D.P.A).left := congrArg (fun q => q.left) (famMap_snd D E F)
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫
      (TF (R := R) E).hom = (TF (R := R) F).hom := Over.w (baseMap (R := R) E F)
  rw [e₁, e₂]
  exact h₂

theorem famφ_famMap (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (famMap D E F).left ≫ DegPre.famφ D E α i := by
  fin_cases i
  · exact congrArg (fun q => q.left) (famMap_snd D E F).symm
  · refine congrArg (fun q => q.left) (Eq.symm ((MonObj.comp_mul (famMap D E F) (DegPre.prB D _) (cP D _ α)).trans ?_))
    rw [comp_cP, famMap_snd]; rfl
  · exact congrArg (fun q => q.left) (comp_cP D (famMap D E F) α).symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (famMap D E F)).symm

theorem trF_famMap (mu : D.X) :
    DegPre.trF D F mu ≫ famMap D E F = famMap D E F ≫ DegPre.trF D E mu := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, famMap_fst, DegPre.trF, DegPre.trF, lift_fst, lift_fst_assoc, famMap_fst]
  · rw [Category.assoc, Category.assoc, famMap_snd, DegPre.trF, DegPre.trF, lift_snd, lift_snd]
    refine Eq.symm ((MonObj.comp_mul (famMap D E F) (DegPre.prB D _) (cP D _ mu)).trans ?_)
    rw [comp_cP, famMap_snd]; rfl

theorem shiftVal_famMap (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F)
    (z : T.left) {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    shiftVal D E k mu α (ρ ≫ famMap D E F) z J = shiftVal D F k mu α ρ z J := by
  refine congrArg₂ (· * ·) ?_ ?_
  · simp only [uVal, comp_cP, Category.assoc, famMap_snd]
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    congr 1
    rw [Category.assoc, famMap_fst, ← specMap_jFK (R := R) E F]
    simp only [Over.comp_left, Category.assoc]
    rfl

instance : NoetherianSpace (DegPre.BF D F).left := by
  have := D.P.isAb.proper
  have : IsProper (famBase D F) := inferInstanceAs (IsProper (pullback.fst _ _))
  have : IsLocallyNoetherian (DegPre.BF D F).left := LocallyOfFiniteType.isLocallyNoetherian (famBase D F)
  have : CompactSpace (DegPre.BF D F).left := QuasiCompact.compactSpace_of_compactSpace (famBase D F)
  have : IsNoetherian (DegPre.BF D F).left := {}
  infer_instance

def termPull (k : ℕ) (α : D.X) :
    FamTerm D E k α →ₛₗ[algebraMap E F] FamTerm D F k α :=
  pullOver D.P.L (DegPre.famε k) (isPullback_famMap D E F).w (famφ_famMap D E F α)

theorem isExtension_termPull (k : ℕ) (α : D.X) : IsExtension (termPull D E F k α) :=
  isExtension_pullOver (isPullback_famMap D E F) D.P.isLB _ _

variable {D E F} in
theorem shift_termPull {k : ℕ} {mu α : D.X} {Θ Θ'} (hΘ : IsShift D E k mu α Θ)
    (hΘ' : IsShift D F k mu α Θ') (s : FamTerm D E k α) :
    Θ' (termPull D E F k α s) = termPull D E F k _ (Θ s) := by
  refine sec_ext' D.P.isLB fun y J hJ => ?_
  refine (hΘ' _ _ (𝟙 _) y J hJ).trans (Eq.trans ?_ ((sval_pullOver _ _ _ _ hJ).trans
    (hΘ s _ (𝟙 _ ≫ famMap D E F) y J hJ)).symm)
  refine congrArg₂ (· * ·) ((sval_pullOver _ _ _ _ hJ).trans ?_)
    (congrArg Units.val (shiftVal_famMap D E F k mu α _ y hJ).symm)
  congr 1
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, Category.assoc, Category.assoc, trF_famMap]

def famPull (hG : GlobalFnsSt) (k : ℕ) :
    Fam D E k →ₛₗ[algebraMap E F] Fam D F k where
  toFun s := ⟨fun α => termPull D E F k α (s.s α), by
    choose Θ hΘ using exists_isShift D E hG k
    choose Θ' hΘ' using exists_isShift D F hG k
    refine (famFE_iff hG hΘ' _).2 fun mu α => ?_
    exact (congrArg (termPull D E F k _) ((famFE_iff hG hΘ s.s).1 s.fe mu α)).trans
      (shift_termPull (hΘ mu α) (hΘ' mu α) _).symm⟩
  map_add' s t := fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    (map_add (termPull D E F k α) (famProj D _ k α s) (famProj D _ k α t))
  map_smul' c s := fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    (map_smulₛₗ (termPull D E F k α) c (famProj D _ k α s))

theorem isExtension_famPull (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) : IsExtension (famPull D E F hG k) := by
  obtain ⟨T, hT⟩ := exists_finset_representatives D.X hk
  choose Θ hΘ using exists_isShift D E hG k
  choose Θ' hΘ' using exists_isShift D F hG k
  refine IsExtension.of_proj _ (termPull D E F k) (isExtension_termPull D E F k) (famProj D _ k) (famProj D F k)
    (fun _ _ => rfl) (fun x hx => fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) (hx α)) T
    (fun v hv => fam_ext fun β j => ?_) fun ℓ Λ hΛ x => ⟨⟨fun α => Λ α (x.s α), ?_⟩, fun _ => rfl⟩
  · obtain ⟨α, hα, mu, rfl⟩ := hT β
    have e : Θ mu α (v.s α) = 0 := (congrArg (Θ mu α) (hv α hα)).trans (map_zero _)
    exact congrArg (fun q => LB.Sec.f q j) (((famFE_iff hG hΘ v.s).1 v.fe mu α).trans e)
  · refine (famFE_iff hG hΘ _).2 fun mu α => ?_
    exact (congrArg (Λ _) ((famFE_iff hG hΘ' x.s).1 x.fe mu α)).trans
      (IsCoord.natural (isExtension_termPull D E F k α).span (hΛ α) (hΛ _) (Θ mu α) (Θ' mu α)
        (shift_termPull (hΘ mu α) (hΘ' mu α)) _)

end Pull

end GlobalTheory.FieldBaseChange
end
end

section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FieldBaseChange

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Pow

variable {S : Type} [CommRing S] {X Y Z : Scheme.{0}} {L : LB X} {g : Y ⟶ X} {k : ℤ}
  {π : Y ⟶ Spec (CommRingCat.of S)}

theorem powVal_add (a b : SecOver π (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) (r : Z ⟶ Y) (z : Z)
    {i : L.ι} (hi : g (r z) ∈ L.U i) :
    powVal (a + b : SecOver π _) r z i = powVal a r z i + powVal b r z i :=
  gs_add r z _ (mem_wchart.2 fun _ => hi) _ _

theorem powVal_smul (c : S) (a : SecOver π (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) (r : Z ⟶ Y)
    (z : Z) {i : L.ι} (hi : g (r z) ∈ L.U i) :
    powVal (c • a : SecOver π _) r z i = constVal (r ≫ π) z c * powVal a r z i :=
  gs_smul π r z _ (mem_wchart.2 fun _ => hi) c _

theorem powVal_zero (r : Z ⟶ Y) (z : Z) {i : L.ι} (hi : g (r z) ∈ L.U i) :
    powVal (0 : SecOver π (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) r z i = 0 :=
  gs_zero' r z _ (mem_wchart.2 fun _ => hi)

theorem powVal_ext (hL : L.IsLB) {a b : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))}
    (h : ∀ y i, g y ∈ L.U i → powVal a (𝟙 Y) y i = powVal b (𝟙 Y) y i) : a = b :=
  sec_ext' hL fun y J hJ => h y _ (hJ (𝟙 Y ≫ g))

end Pow

section Iso

variable {Y Y' X₁ X₂ Z₁ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
  {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}

theorem isoRelM_bijective (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (hw : w.IsGen) (e₁ : h₁ ≫ g₁ = m ≫ f₁) (n : Z₁ ⟶ Y')
    (hn : n ≫ h₁ = 𝟙 _) (hn' : h₁ ≫ n = 𝟙 _) :
    (∀ a, ∃! b, GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b) ∧
      ∀ b, ∃! a, GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b := by
  have e₂ : 𝟙 Y' ≫ m ≫ f₂ = m ≫ f₂ := Category.id_comp _
  have e₃ : g₁ = (n ≫ m) ≫ f₁ := by rw [Category.assoc, ← e₁, ← Category.assoc, hn, Category.id_comp]
  refine ⟨fun a => existsUnique_of_exists_of_unique ?_ fun b b' h h' => ?_,
    fun b => existsUnique_of_exists_of_unique ?_ fun a a' h h' => ?_⟩
  · obtain ⟨b, hb⟩ := exists_move hL₁ hL₂ hw m k h₁ e₁ rfl a
    exact ⟨b, (isoRelM_iff w m k h₁ e₁ _ e₂ a b).2 fun y i₂ i₁ a₂ a₁ => by
      rw [Category.comp_id]; exact hb _ _ y i₂ i₁ a₂ a₁⟩
  · refine powVal_ext hL₂ fun y i hi => ?_
    obtain ⟨i₁, a₁⟩ := exists_chart hL₁ (f₁ (m y))
    have := ((isoRelM_iff w m k h₁ e₁ _ e₂ a b).1 h _ (𝟙 _) y i i₁ hi a₁).trans
      ((isoRelM_iff w m k h₁ e₁ _ e₂ a b').1 h' _ (𝟙 _) y i i₁ hi a₁).symm
    rwa [Category.comp_id] at this
  · obtain ⟨a, ha⟩ := exists_move_back hL₁ hL₂ hw (n ≫ m) k n (Category.assoc _ _ _).symm e₃ b
    refine ⟨a, (isoRelM_iff w m k h₁ e₁ _ e₂ a b).2 fun y i₂ i₁ a₂ a₁ => ?_⟩
    have e : h₁ ≫ n ≫ m = m := by rw [← Category.assoc, hn', Category.id_comp]
    have pt : (n ≫ m) (h₁ y) = m y := congrArg (fun q : Y' ⟶ Y => q y) e
    have := ha _ h₁ y i₂ i₁ (pt.symm ▸ a₂) (pt.symm ▸ a₁)
    rw [hn', e] at this
    simpa only [Category.id_comp] using this
  · refine powVal_ext hL₁ fun y i hi => ?_
    obtain ⟨i₂, a₂⟩ := exists_chart hL₂ (f₂ (m (n y)))
    have a₁ : f₁ (m (n y)) ∈ L₁.U i := by rw [e₃] at hi; exact hi
    have := ((isoRelM_iff w m k h₁ e₁ _ e₂ a b).1 h _ n y i₂ i a₂ a₁).symm.trans
      ((isoRelM_iff w m k h₁ e₁ _ e₂ a' b).1 h' _ n y i₂ i a₂ a₁)
    rw [hn] at this
    exact (Units.mul_right_inj _).1 this

theorem isoRelM_lin {S : Type} [CommRing S] {π₁ : Z₁ ⟶ Spec (CommRingCat.of S)}
    {π' : Y' ⟶ Spec (CommRingCat.of S)} (hπ : h₁ ≫ π₁ = π') (c : S)
    {a a' : SecOver π₁ (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b b' : SecOver π' (LB.LinComb L₂ (K := Fin 1) (fun _ => m ≫ f₂) (fun _ => (k : ℤ)))}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b)
    (h' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a' (m ≫ f₂) (𝟙 _) b') :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ (c • a + a' : SecOver π₁ _) (m ≫ f₂) (𝟙 _) (c • b + b' : SecOver π' _) := by
  refine (isoRelM_iff w m k h₁ h.1 _ h.2.1 _ _).2 fun y i₂ i₁ a₂ a₁ => ?_
  have b₁ : g₁ ((𝟙 Y' ≫ h₁) y) ∈ L₁.U i₁ :=
    (congrArg (fun q : Y' ⟶ X₁ => q y) h.1 : g₁ (h₁ y) = f₁ (m y)).symm ▸ a₁
  have b₂ : (m ≫ f₂) ((𝟙 Y' ≫ 𝟙 Y') y) ∈ L₂.U i₂ := a₂
  rw [powVal_add _ _ _ y b₁, powVal_add _ _ _ y b₂, powVal_smul _ _ _ y b₁, powVal_smul _ _ _ y b₂,
    (isoRelM_iff w m k h₁ h.1 _ h.2.1 _ _).1 h _ (𝟙 _) y i₂ i₁ a₂ a₁,
    (isoRelM_iff w m k h₁ h.1 _ h.2.1 _ _).1 h' _ (𝟙 _) y i₂ i₁ a₂ a₁, Category.assoc, Category.assoc, hπ,
    Category.id_comp π', Category.id_comp π']
  ring

end Iso

section Data

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem famφ_prB (α : D.X) (i : Fin 4) : DegPre.famφ D F α i = (DegPre.prB D F).left ≫ D.famφB α i := by
  fin_cases i
  · exact (Category.comp_id _).symm
  · refine congrArg (fun q => q.left) (Eq.symm ((MonObj.comp_mul (DegPre.prB D F) (𝟙 _) (cP D _ α)).trans ?_))
    rw [comp_cP, Category.comp_id]; rfl
  · exact congrArg (fun q => q.left) (comp_cP D (DegPre.prB D F) α).symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (DegPre.prB D F)).symm

variable [Algebra R F] [IsScalarTower R (FractionRing R) F]

theorem bf_hom : (DegPre.BF D F).hom = famBase D F ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
  have e : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [← e]
  exact (Over.w (fst (TF (R := R) F) D.P.A)).symm

theorem prB_hom : (DegPre.prB D F).left ≫ D.P.A.hom =
    famBase D F ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) :=
  (Over.w (DegPre.prB D F)).trans (bf_hom D F)

end Data

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

abbrev IntSec (k : ℕ) : Type :=
  SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))

variable (D) in

abbrev IntTerm (k : ℕ) (α : D.toPre.X) : Type :=
  SecOver D.toPre.P.A.hom (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k))

theorem expandsAt_lin (e k : ℕ) (c : R) {σ σ' : IntSec U k} {f f' : ∀ α, IntTerm D k α}
    (h : U.ExpandsAt e k σ f) (h' : U.ExpandsAt e k σ' f') :
    U.ExpandsAt e k (c • σ + σ' : IntSec U k) (fun α => (c • f α + f' α : IntTerm D k α)) := by
  classical
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
  obtain ⟨S', hS'⟩ := expandsAt_val U e k σ' f' h'
  have hπ : fGl I G e ≫ G.hom = pGl U e ≫ D.toPre.P.A.hom := (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
  refine expandsAt_of_val U e k _ _ (S ∪ S') fun y J hJ => ?_
  obtain ⟨z₁, v₁⟩ := hS _ (𝟙 _) y J hJ
  obtain ⟨z₂, v₂⟩ := hS' _ (𝟙 _) y J hJ
  simp only [Category.id_comp] at z₁ v₁ z₂ v₂
  refine ⟨fun α hα => ?_, fun jL hj => ?_⟩
  · rw [Finset.mem_union, not_or] at hα
    rw [sval_add' hJ, sval_smul' hJ, z₁ α hα.1, z₂ α hα.2, mul_zero, add_zero]
  · have e₁ : sv U k (c • σ + σ' : IntSec U k) (fGl I G e) y jL =
        constVal (fGl I G e ≫ G.hom) y c * sv U k σ (fGl I G e) y jL + sv U k σ' (fGl I G e) y jL :=
      (powVal_add _ _ _ y hj).trans (congrArg (· + _) (powVal_smul _ _ _ y hj))
    have w₁ := (v₁ jL hj).trans (Finset.sum_subset (Finset.subset_union_left (s₂ := S'))
      fun α _ hα => by rw [z₁ α hα, zero_mul])
    have w₂ := (v₂ jL hj).trans (Finset.sum_subset (Finset.subset_union_right (s₁ := S))
      fun α _ hα => by rw [z₂ α hα, zero_mul])
    rw [e₁, mul_add, mul_left_comm, w₁, w₂, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [sval_add' hJ, sval_smul' hJ, hπ]
    ring

theorem expandsAt_zero (e k : ℕ) :
    U.ExpandsAt e k (0 : IntSec U k) (fun α => (0 : IntTerm D k α)) :=
  expandsAt_of_val U e k _ _ ∅ fun y J hJ => ⟨fun _ _ => sval_zero' hJ _, fun jL hj => by
    rw [Finset.sum_empty]
    exact (congrArg _ (powVal_zero (π := G.hom) _ y hj)).trans (mul_zero _)⟩

def expansionPairs (k : ℕ) : Submodule R (IntSec U k × ∀ α, IntTerm D k α) where
  carrier := {x | ∀ e, U.ExpandsAt e k x.1 x.2}
  zero_mem' e := expandsAt_zero U e k
  add_mem' {x y} hx hy e := by
    have := expandsAt_lin U e k 1 (hx e) (hy e)
    simp only [one_smul] at this
    exact this
  smul_mem' c x hx e := by
    have := expandsAt_lin U e k c (hx e) (expandsAt_zero U e k)
    simp only [add_zero] at this
    exact this

include U in
theorem noetherianSpace_generic : NoetherianSpace (pullback G.hom (jK R) : Scheme) := by
  have := A.isAb.proper
  have : IsIso U.gen.hom.left := ⟨⟨U.gen.inv.left, by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]⟩⟩
  have : IsProper (pullback.snd G.hom (jK R)) := by
    have e : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
    rw [← e]; infer_instance
  have : IsLocallyNoetherian (pullback G.hom (jK R) : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd G.hom (jK R))
  have : CompactSpace (pullback G.hom (jK R) : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd G.hom (jK R))
  have : IsNoetherian (pullback G.hom (jK R) : Scheme) := {}
  infer_instance

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

variable (G) in

def groupBase : (UnifPre.GF (G := G) F).left ⟶ Spec (CommRingCat.of F) :=
  (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left

variable (A) in

def abelianBase : (TFK (R := R) F ⊗ A.A).left ⟶ Spec (CommRingCat.of F) := (fst (TFK (R := R) F) A.A).left

omit [GrpObj G] [IsCommMonObj G] in
theorem isPullback_groupBase : IsPullback (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left
    (groupBase G F) (pullback.snd G.hom (jK R))
    (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))) := (IsPullback.of_hasPullback _ _).flip

abbrev GroupSec (k : ℕ) : Type :=
  SecOver (groupBase G F) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)))

def genericSec (k : ℕ) : IntSec U k →ₛₗ[algebraMap R (FractionRing R)] SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))) :=
  pullOver U.LG.L _ (p := pullback.fst G.hom (jK R)) pullback.condition (fun _ => (Category.comp_id _).symm)

variable (D) in

def genericTerm (k : ℕ) (α : D.toPre.X) :
    IntTerm D k α →ₛₗ[algebraMap R (FractionRing R)] FamTerm D.toPre (FractionRing R) k α :=
  pullOver D.toPre.P.L _ (prB_hom D.toPre (FractionRing R)) (famφ_prB D.toPre (FractionRing R) α)

def extendSec (k : ℕ) : SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)))
      →ₛₗ[algebraMap (FractionRing R) F] GroupSec U F k :=
  pullOver U.LG.L _ (isPullback_groupBase F).w (fun _ => rfl)

theorem expands_iff (k : ℕ) (v : SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (s : Fam D.toPre (FractionRing R) k) : U.Expands k v s ↔ ∃ r : R, r ≠ 0 ∧ ∃ x ∈ expansionPairs U k,
      genericSec U k x.1 = algebraMap R (FractionRing R) r • v ∧
      ∀ α, genericTerm D k α (x.2 α) = algebraMap R (FractionRing R) r • famProj D.toPre _ k α s := by
  have e₁ := fun (σ : IntSec U k) (r : R) => secScal_iff (p := pullback.fst G.hom (jK R)) pullback.condition
    (fun _ => (Category.comp_id _).symm) U.LG.isLB v σ _ (algebraMap R (FractionRing R)) rfl r
  have e₂ := fun α (f : IntTerm D k α) (r : R) => secScal_iff (prB_hom D.toPre (FractionRing R))
    (famφ_prB D.toPre (FractionRing R) α) D.toPre.P.isLB (famProj D.toPre _ k α s) f _
    (algebraMap R (FractionRing R)) (bf_hom D.toPre (FractionRing R)) r
  constructor
  · rintro ⟨r, hr, σ, f, h₁, h₂, h₃⟩
    exact ⟨r, hr, (σ, f), h₃, (e₁ σ r).1 h₁, fun α => (e₂ α (f α) r).1 (h₂ α)⟩
  · rintro ⟨r, hr, x, h₃, h₁, h₂⟩
    exact ⟨r, hr, x.1, x.2, (e₁ x.1 r).2 h₁, fun α => (e₂ α (x.2 α) r).2 (h₂ α), h₃⟩

theorem expandsG_iff (k : ℕ) (v : GroupSec U F k) (s : Fam D.toPre F k) :
    U.ExpandsG F k v s ↔ ∃ (n : ℕ) (c : Fin n → F) (x : Fin n → IntSec U k × ∀ α, IntTerm D k α),
      (∀ i, x i ∈ expansionPairs U k) ∧ v = ∑ i, c i • extendSec U F k (genericSec U k (x i).1) ∧
      ∀ α, famProj D.toPre F k α s =
        ∑ i, c i • termPull D.toPre (FractionRing R) F k α (genericTerm D k α ((x i).2 α)) := by
  have e₁ := fun (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) => secLin_iff U.LG.isLB v σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))
  have e₂ := fun α (n : ℕ) (c : Fin n → F) (f : Fin n → IntTerm D k α) => secLin_iff D.toPre.P.isLB
    (famProj D.toPre F k α s) f (DegPre.prB D.toPre F).left c
    (fun i => termPull D.toPre (FractionRing R) F k α (genericTerm D k α (f i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f i) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing R) F)))))))
  constructor
  · rintro ⟨n, c, σ, f, h₃, h₁, h₂⟩
    exact ⟨n, c, fun i => (σ i, f i), h₃, (e₁ n c σ).1 h₁, fun α => (e₂ α n c fun i => f i α).1 (h₂ α)⟩
  · rintro ⟨n, c, x, h₃, h₁, h₂⟩
    exact ⟨n, c, fun i => (x i).1, fun i => (x i).2, h₃, (e₁ n c _).2 h₁,
      fun α => (e₂ α n c fun i => (x i).2 α).2 (h₂ α)⟩

theorem expandsG_bijective (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) :
    (∀ v : GroupSec U F k, ∃! s, U.ExpandsG F k v s) ∧ ∀ s, ∃! v : GroupSec U F k, U.ExpandsG F k v s :=
  have : NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  graph_bijective (expansionPairs U k) (genericSec U k) (genericTerm D k) (extendSec U F k)
    (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) (termPull D.toPre (FractionRing R) F k)
    (isExtension_termPull D.toPre _ F k) (famPull D.toPre _ F hG k) (isExtension_famPull D.toPre _ F hG hk)
    (famProj D.toPre _ k) (famProj D.toPre F k) (fun _ _ => rfl) _ (expands_iff U k) h _ (expandsG_iff U F k)

theorem expandsG_lin (k : ℕ) (c : F) {v v' : GroupSec U F k} {s s' : Fam D.toPre F k}
    (h : U.ExpandsG F k v s) (h' : U.ExpandsG F k v' s') :
    U.ExpandsG F k (c • v + v' : GroupSec U F k) (c • s + s') := by
  obtain ⟨n, a, x, hx, e₁, e₂⟩ := (expandsG_iff U F k v s).1 h
  obtain ⟨n', a', x', hx', e₁', e₂'⟩ := (expandsG_iff U F k v' s').1 h'
  refine (expandsG_iff U F k _ _).2 ⟨n + n', Fin.append (fun i => c * a i) a', Fin.append x x',
    fun i => ?_, ?_, fun α => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hx i
    · rw [Fin.append_right]; exact hx' i
  · rw [Fin.sum_univ_add, e₁, e₁', Finset.smul_sum]
    simp only [Fin.append_left, Fin.append_right, smul_smul]
  · rw [Fin.sum_univ_add, map_add, map_smul, e₂, e₂', Finset.smul_sum]
    simp only [Fin.append_left, Fin.append_right, smul_smul]

variable {k : ℕ} {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}

theorem expandsF_lin (c : F) {t t' : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F))}
    {s s' : Fam D.toPre F k} (h : U.ExpandsF F k w t s) (h' : U.ExpandsF F k w t' s') :
    U.ExpandsF F k w (c • t + t' : SecOver (abelianBase A F) _) (c • s + s') := by
  obtain ⟨v, a, b⟩ := h
  obtain ⟨v', a', b'⟩ := h'
  have hπ : (U.genF F).left ≫ abelianBase A F = groupBase G F :=
    congrArg (fun q => q.left) (lift_fst _ _ : U.genF F ≫ fst _ _ = _)
  exact ⟨_, isoRelM_lin hπ c a a', expandsG_lin U F k c b b'⟩

theorem expandsF_bijective (hG : GlobalFnsSt) (hk : 1 ≤ k) (h : U.ExpBij k) (hw : w.IsGen) :
    (∀ t, ∃! s, U.ExpandsF F k w t s) ∧ ∀ s, ∃! t, U.ExpandsF F k w t s := by
  obtain ⟨g₁, g₂⟩ := expandsG_bijective U F hG hk h
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  obtain ⟨i₁, i₂⟩ := isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')
  refine ⟨fun t => existsUnique_of_exists_of_unique ?_ ?_, fun s => existsUnique_of_exists_of_unique ?_ ?_⟩
  · obtain ⟨v, hv⟩ := (i₁ t).exists
    obtain ⟨s, hs⟩ := (g₁ v).exists
    exact ⟨s, v, hv, hs⟩
  · rintro s s' ⟨v, a, b⟩ ⟨v', a', b'⟩
    obtain rfl := (i₁ t).unique a a'
    exact (g₁ v).unique b b'
  · obtain ⟨v, hv⟩ := (g₂ s).exists
    obtain ⟨t, ht⟩ := (i₂ v).exists
    exact ⟨t, v, ht, hv⟩
  · rintro t t' ⟨v, a, b⟩ ⟨v', a', b'⟩
    obtain rfl := (g₂ s).unique b b'
    exact (i₂ v).unique a a'

end GlobalTheory.FieldBaseChange

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR FieldBaseChange

theorem expansion_bijective_over_fields (hG : GlobalFnsSt) : Geo.Tor.ExpBijectiveUniformisation :=
  fun _ _ _ _ _ _ _ _ _ U F _ _ k hk _ hw => expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw

theorem exists_linearEquiv_expandsF (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen) :
    ∃ e : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) ≃ₗ[F] Fam D.toPre F k,
      ∀ t s, U.toUnifPre.ExpandsF F k w t s ↔ e t = s := by
  obtain ⟨h₁, h₂⟩ := expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw
  choose f hf using fun t : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) => (h₁ t).exists
  have iff : ∀ t s, U.toUnifPre.ExpandsF F k w t s ↔ f t = s := fun t s =>
    ⟨fun h => (h₁ t).unique (hf t) h, fun h => h ▸ hf t⟩
  have lin : ∀ (c : F) t t', f (c • t + t') = c • f t + f t' := fun c t t' =>
    (iff _ _).1 (expandsF_lin U.toUnifPre F c (hf t) (hf t'))
  have f0 : f 0 = 0 := by
    have := lin 1 0 0
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  let l : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) →ₗ[F] Fam D.toPre F k :=
    { toFun := f
      map_add' := fun t t' => by simpa only [one_smul] using lin 1 t t'
      map_smul' := fun c t => by simpa only [add_zero, f0, RingHom.id_apply] using lin c t 0 }
  refine ⟨LinearEquiv.ofBijective l ⟨fun t t' e => ?_, fun s => ?_⟩, iff⟩
  · exact (h₂ (f t')).unique ((iff t _).2 e) (hf t')
  · obtain ⟨t, ht⟩ := (h₂ s).exists
    exact ⟨t, (iff t s).1 ht⟩

end GlobalTheory
end
end
