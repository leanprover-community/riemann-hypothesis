import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TensSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ShaFrom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardHomQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.CardAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.PrimeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumGens
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumT
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.TorsMain
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised

section
open scoped TensorProduct
open GlobalTheory.TateLimit

private theorem step (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Finite X]
    (c : ℕ) : Nat.card (X ⧸ lpow l X (c + 1)) ≤
      Nat.card (X ⧸ lpow l X 1) * Nat.card (X ⧸ lpow l X c) := by
  haveI : ∀ P : Submodule ℤ_[l] X, Finite (X ⧸ P) := fun P =>
    Finite.of_surjective _ P.mkQ_surjective
  let f : X →ₗ[ℤ_[l]] X ⧸ lpow l X (c + 1) :=
    (lpow l X (c + 1)).mkQ ∘ₗ LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ c)
  have hf : lpow l X 1 ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.lsmul_apply]
    exact ⟨y, by rw [LinearMap.lsmul_apply, pow_add, mul_smul]⟩
  let g := (lpow l X 1).liftQ f hf
  let R := LinearMap.range g
  have h1 : Nat.card R ≤ Nat.card (X ⧸ lpow l X 1) :=
    Nat.card_le_card_of_surjective g.rangeRestrict g.surjective_rangeRestrict
  let p : X →ₗ[ℤ_[l]] (X ⧸ lpow l X (c + 1)) ⧸ R := R.mkQ ∘ₗ (lpow l X (c + 1)).mkQ
  have hp : lpow l X c ≤ LinearMap.ker p := by
    rintro _ ⟨y, rfl⟩
    simp only [p, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have hps : Function.Surjective p :=
    R.mkQ_surjective.comp (lpow l X (c + 1)).mkQ_surjective
  have h2 : Nat.card ((X ⧸ lpow l X (c + 1)) ⧸ R) ≤ Nat.card (X ⧸ lpow l X c) := by
    refine Nat.card_le_card_of_surjective ((lpow l X c).liftQ p hp) fun z => ?_
    obtain ⟨x, rfl⟩ := hps z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  rw [Submodule.card_eq_card_quotient_mul_card R]
  first
    | exact Nat.mul_le_mul h1 h2
    | exact (Nat.mul_le_mul h2 h1).trans_eq (mul_comm _ _)

theorem UpperTheory.V.K.cardQuotPow :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Finite X] (c : ℕ), Nat.card (X ⧸ lpow l X c) ≤ Nat.card (X ⧸ lpow l X 1) ^ c := by
  intro l _ X _ _ _ c
  induction c with
  | zero =>
    have h : lpow l X 0 = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact ⟨x, by simp⟩
    haveI : Subsingleton (X ⧸ lpow l X 0) := Submodule.Quotient.subsingleton_iff.2 h
    rw [pow_zero]
    exact (Nat.card_of_subsingleton (0 : X ⧸ lpow l X 0)).le
  | succ c ih =>
    rw [pow_succ']
    exact (step l X c).trans (Nat.mul_le_mul_left _ ih)
end

section
open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.cardKill :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Finite X] (c : ℕ) (Y : Submodule ℤ_[l] X), (∀ y ∈ Y, (l : ℤ_[l]) ^ c • y = 0) → Nat.card Y ≤ Nat.card (X ⧸ lpow l X 1) ^ c := by
  intro l _ X _ _ _ c Y hY
  refine le_trans ?_ (UpperTheory.V.K.cardQuotPow l X c)
  let f : X →ₗ[ℤ_[l]] X := LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ c)
  have hr : lpow l X c = LinearMap.range f := rfl
  have hYk : Y ≤ LinearMap.ker f := fun y hy => hY y hy
  have h1 : Nat.card Y ≤ Nat.card (LinearMap.ker f) :=
    Nat.card_le_card_of_injective (Submodule.inclusion hYk) (Submodule.inclusion_injective hYk)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h4 : Nat.card (X ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [hr]
  refine h1.trans (le_of_eq (Nat.eq_of_mul_eq_mul_left hpos ?_))
  rw [h4] at h2
  rw [← h3, h2, mul_comm]
end

section
open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.cardRed :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [AddCommGroup K] [Module ℤ_[l] K] [Finite K] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (W : Type) [AddCommGroup W] [Module ℤ_[l] W] (p : K →ₗ[ℤ_[l]] X) (h : K →ₗ[ℤ_[l]] W) (c : ℕ), Function.Surjective p → (∀ x, h x = 0 → (l : ℤ_[l]) ^ c • x = 0) → Nat.card X ≤ Nat.card (X ⧸ lpow l X 1) ^ c * Nat.card (LinearMap.range h) := by
  intro l _ K _ _ _ X _ _ W _ _ p h c hp hk
  haveI : Finite X := Finite.of_surjective p hp
  let Y : Submodule ℤ_[l] X := (LinearMap.ker h).map p
  have h1 : Nat.card Y ≤ Nat.card (X ⧸ lpow l X 1) ^ c := by
    refine UpperTheory.V.K.cardKill l X c Y ?_
    rintro y ⟨x, hx, rfl⟩
    rw [← map_smul, hk x hx, map_zero]
  have hle : LinearMap.ker h ≤ LinearMap.ker (Y.mkQ ∘ₗ p) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨x, hx, rfl⟩
  haveI : Finite (K ⧸ LinearMap.ker h) := Finite.of_surjective _ (LinearMap.ker h).mkQ_surjective
  have h2 : Nat.card (X ⧸ Y) ≤ Nat.card (K ⧸ LinearMap.ker h) := by
    refine Nat.card_le_card_of_surjective ((LinearMap.ker h).liftQ (Y.mkQ ∘ₗ p) hle) fun z => ?_
    obtain ⟨x, rfl⟩ := (Y.mkQ_surjective.comp hp) z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have h4 : Nat.card (K ⧸ LinearMap.ker h) = Nat.card (LinearMap.range h) :=
    Nat.card_congr h.quotKerEquivRange.toEquiv
  rw [Submodule.card_eq_card_quotient_mul_card Y, ← h4]
  exact Nat.mul_le_mul h1 h2
end

section
open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.tensTors :
    ∀ (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H] (x : ℤ_[l] ⊗[ℤ] H), IsOfFinAddOrder x → x ∈ LinearMap.range (LinearMap.lTensor ℤ_[l] (AddCommGroup.torsion H).subtype.toIntLinearMap) := by
  intro l _ H _ x hx
  let T := AddCommGroup.torsion H
  let g : H →ₗ[ℤ] (H ⧸ T) := (QuotientAddGroup.mk' T).toIntLinearMap
  have hg : Function.Surjective g := QuotientAddGroup.mk'_surjective T
  have hex : Function.Exact T.subtype.toIntLinearMap g := by
    intro h
    constructor
    · intro hh
      exact ⟨⟨h, (QuotientAddGroup.eq_zero_iff h).1 hh⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff _).2 t.2
  have hE := lTensor_exact ℤ_[l] hex hg
  haveI : IsAddTorsionFree (H ⧸ T) := inferInstance
  haveI : Module.Flat ℤ (H ⧸ T) := inferInstance
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx
  let m : ℤ_[l] →ₗ[ℤ] ℤ_[l] := n • LinearMap.id
  have hm : Function.Injective m := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : (n : ℤ_[l]) * a = 0 := by simpa [m] using ha
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (Nat.cast_eq_zero.1 h) hn.ne'
    · exact h
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := H ⧸ T) m hm
  have h0 : LinearMap.lTensor ℤ_[l] g x = 0 := by
    apply hinj
    have : LinearMap.rTensor (H ⧸ T) m = n • LinearMap.id := by
      ext a b
      simp [m, ← nsmul_eq_mul, TensorProduct.smul_tmul']
    rw [map_zero, this, LinearMap.smul_apply, LinearMap.id_apply, ← map_nsmul, hnx, map_zero]
  exact (hE x).1 h0
end

section
open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.tensCard :
    ∀ (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H] [Finite (AddCommGroup.torsion H)] (Y : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] H)) [Finite Y], Nat.card Y ≤ Nat.card (AddCommGroup.torsion H) := by
  intro l _ H _ _ Y _
  have hT : AddMonoid.IsTorsion (AddCommGroup.torsion H) := fun t => isOfFinAddOrder_of_finite t
  have key : ∀ y : Y, ∃ t : AddCommGroup.torsion H,
      ((1 : ℤ_[l]) ⊗ₜ[ℤ] (t : H) : ℤ_[l] ⊗[ℤ] H) = (y : ℤ_[l] ⊗[ℤ] H) := by
    intro y
    have hy : IsOfFinAddOrder (y : ℤ_[l] ⊗[ℤ] H) := by
      obtain ⟨n, hn, hny⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (isOfFinAddOrder_of_finite y)
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
      have := congrArg Y.subtype hny
      rw [map_nsmul, map_zero] at this
      exact this
    obtain ⟨z, hz⟩ := UpperTheory.V.K.tensTors l H _ hy
    obtain ⟨t, rfl⟩ := UpperTheory.V.K.tensSurj l _ hT z
    refine ⟨t, ?_⟩
    rw [← hz, LinearMap.lTensor_tmul]
    rfl
  choose f hf using key
  refine Nat.card_le_card_of_injective f ?_
  intro a b hab
  apply Subtype.ext
  rw [← hf a, ← hf b, hab]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

theorem UpperTheory.V.K.chiTriv :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l), HasMuQ l L → ∀ g, redChar D.chi 1 g = 1 := by
  intro l hl L Ω _ _ _ _ _ D hμ g
  obtain ⟨ζ, hζ⟩ : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ 1) := by
    obtain ⟨ζ, hζ⟩ := hμ
    rw [pow_one]
    by_cases h2 : l = 2
    · rw [if_pos h2] at hζ
      exact ⟨ζ ^ 2, hζ.pow (by norm_num) (by rw [h2])⟩
    · rw [if_neg h2] at hζ
      exact ⟨ζ, hζ⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hζ' : IsPrimitiveRoot (algebraMap L Ω ζ) (l ^ 1) := hζ.map_of_injective (algebraMap L Ω).injective
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  have hc : D.chi (QuotientGroup.mk g) = cyclotomicCharacter Ω l g.toRingEquiv := DFunLike.congr_fun D.hchi g
  apply Units.ext
  rw [redChar_coe, hc, Units.val_one, cyclotomicCharacter.toZModPow]
  refine (modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm
  have ht' : (t : Ω) ^ l ^ 1 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht', pow_one]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one ht'
  rw [← hi, ← map_pow]
  exact g.commutes _
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

private theorem mapH1_mem_sha {R G M M' I : Type} {Dd : I → Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [∀ i, Group (Dd i)] [∀ i, TopologicalSpace (Dd i)] (φ : ∀ i, Dd i →* G) (hφ : ∀ i, Continuous (φ i))
    (ρ : Representation R G M) (ρ' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
    (he : ∀ g m, u (ρ g m) = ρ' g (u m)) (x : H1 ρ) (hx : x ∈ Sha1 ρ φ hφ) :
    mapH1 ρ ρ' u hu he x ∈ Sha1 ρ' φ hφ := by
  simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i
  have key : resH1 ρ' (φ i) (hφ i) (mapH1 ρ ρ' u hu he x) =
      mapH1 (ρ.comp (φ i)) (ρ'.comp (φ i)) u hu (fun g m => he _ m) (resH1 ρ (φ i) (hφ i) x) := by
    induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  rw [key, hx i, map_zero]

private theorem mapH1_comp {R G M M' : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    (ρ : Representation R G M) (ρ' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
    (he : ∀ g m, u (ρ g m) = ρ' g (u m)) (w : M' →ₗ[R] M) (hw : Continuous w)
    (he' : ∀ g m, w (ρ' g m) = ρ g (w m)) (h : ∀ m, w (u m) = m) (x : H1 ρ) :
    mapH1 ρ' ρ w hw he' (mapH1 ρ ρ' u hu he x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => h _))

private theorem card_sha_congr {R G M M' I : Type} {Dd : I → Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [∀ i, Group (Dd i)] [∀ i, TopologicalSpace (Dd i)] (φ : ∀ i, Dd i →* G) (hφ : ∀ i, Continuous (φ i))
    (ρ : Representation R G M) (ρ' : Representation R G M') (u : M ≃ₗ[R] M') (hu : Continuous u)
    (hw : Continuous u.symm) (he : ∀ g m, u (ρ g m) = ρ' g (u m)) :
    Nat.card (Sha1 ρ φ hφ) = Nat.card (Sha1 ρ' φ hφ) := by
  have he' : ∀ g m, u.symm (ρ' g m) = ρ g (u.symm m) := fun g m => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  exact Nat.card_congr
    { toFun := fun x => ⟨_, mapH1_mem_sha φ hφ ρ ρ' u.toLinearMap hu he x.1 x.2⟩
      invFun := fun x => ⟨_, mapH1_mem_sha φ hφ ρ' ρ u.symm.toLinearMap hw he' x.1 x.2⟩
      left_inv := fun x => Subtype.ext (mapH1_comp ρ ρ' u.toLinearMap hu he u.symm.toLinearMap hw he'
        u.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (mapH1_comp ρ' ρ u.symm.toLinearMap hw he' u.toLinearMap hu he
        u.apply_symm_apply x.1) }

theorem UpperTheory.V.K.shaDualCard :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l) (n : ℤ), (∀ g, redChar D.chi 1 g = 1) → Nat.card (Sha1 (zd D n 1) (locFam D.S D.A) (continuous_locFam D.S D.A)) = Nat.card (ShaZm D 1 0) := by
  intro l _ L Ω _ _ _ _ _ D n h
  let ev : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) :=
    { toFun := fun φ => φ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hlin : ∀ (φ : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))) (m : ZMod (l ^ 1)), φ m = m * φ 1 :=
    fun φ m => by
      have := LinearMap.map_smul (show ZMod (l ^ 1) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) from φ) m 1
      rw [smul_eq_mul, mul_one, smul_eq_mul] at this
      exact this
  have hev : Function.Bijective ev := by
    refine ⟨fun φ ψ h => TDual.ext fun m => ?_, fun y => ⟨y • TDual.mk LinearMap.id, ?_⟩⟩
    · rw [hlin φ, hlin ψ]; exact congrArg _ h
    · exact mul_one y
  have hn : ∀ g, redChar (D.chi ^ n) 1 g = 1 := fun g => by
    have : redChar (D.chi ^ n) 1 g = redChar D.chi 1 g ^ n := by
      simp only [redChar, MonoidHom.comp_apply, MonoidHom.zpow_apply, map_zpow]
    rw [this, h, one_zpow]
  refine card_sha_congr _ _ _ (zmTw D 1 0) (LinearEquiv.ofBijective ev hev) continuous_of_discreteTopology
    continuous_of_discreteTopology fun g m => ?_
  have h0 : ∀ x, zmTw D 1 0 g x = x := fun x => by simp [zmTw]
  rw [h0]
  change ((redChar D.chi 1 g : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) *
    m (((redChar (D.chi ^ n) 1 g⁻¹ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) * 1) = m 1
  rw [h, hn, Units.val_one, one_mul, one_mul]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

theorem UpperTheory.V.K.shaZmCard :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l), IsTotallyComplex L → Nat.card (ShaZm D 1 0) ≤ classNumber L := by
  intro l hl L Ω _ _ _ _ _ D hL
  obtain ⟨hinj, hmap⟩ := UpperTheory.V.Kum.shaZm L Ω l D 1 (Or.inr (nrRealPlaces_eq_zero_iff.2 hL))
  obtain ⟨ι, hι, -⟩ := zmodToQZ l 1
  have hc := UpperTheory.V.Kum.cardHomQZ l (Additive (ClassGroup (𝓞 L)))
  have hf : Finite (Additive (ClassGroup (𝓞 L)) →+ QZ l) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hl.out.ne_zero)
  let f : ClDual L l (ZMod (l ^ 1)) (ZMod (l ^ 1)) → (Additive (ClassGroup (𝓞 L)) →+ QZ l) := fun θ =>
    AddMonoidHom.mk' (fun c => ι (θ.1 c.toMul)) fun a b => by rw [toMul_add, θ.2.1, map_add]
  have hfi : Function.Injective f := fun a b h =>
    Subtype.ext (funext fun c => hι (DFunLike.congr_fun h (Additive.ofMul c)))
  have hfin : Finite (ClDual L l (ZMod (l ^ 1)) (ZMod (l ^ 1))) := Finite.of_injective f hfi
  have h1 : Nat.card (ShaZm D 1 0) = Nat.card ((ShaZm D 1 0).map (resZm D 1)) :=
    Nat.card_congr (Submodule.equivMapOfInjective _ hinj _).toEquiv
  have h2 : Nat.card ((ClDual L l (ZMod (l ^ 1)) (ZMod (l ^ 1))).map
      (LinearMap.funLeft (ZMod (l ^ 1)) (ZMod (l ^ 1)) (artCl L Ω))) ≤ Nat.card (ClDual L l (ZMod (l ^ 1)) (ZMod (l ^ 1))) :=
    Nat.card_le_card_of_surjective _ (LinearMap.submoduleMap_surjective _ _)
  have h3 := Nat.card_le_card_of_injective f hfi
  have h4 : l ^ (Nat.card (Additive (ClassGroup (𝓞 L)))).factorization l ≤ Nat.card (Additive (ClassGroup (𝓞 L))) :=
    Nat.ordProj_le l Nat.card_pos.ne'
  have h5 : Nat.card (Additive (ClassGroup (𝓞 L))) = classNumber L := by
    rw [classNumber, ← Nat.card_eq_fintype_card]; rfl
  rw [h1, hmap]
  omega
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

theorem UpperTheory.V.K.card_H2_quotient_le_sha :
    GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l) (e : ℤ), IsTotallyComplex L → let n := e + 1; Nat.card (H2 (zlTw D n) ⧸ lpow l (H2 (zlTw D n)) 1) ≤ Nat.card (Sha1 (zd D n 1) (locFam D.S D.A) (continuous_locFam D.S D.A)) * l ^ Module.finrank ℚ L := by
  intro hP hF hT l hl L Ω _ _ _ _ _ D e hc
  classical
  have hcase : PTCase L l := Or.inr (NumberField.nrRealPlaces_eq_zero_iff.2 hc)
  have hS := fun r hr => (finite_level D e hP hcase r hr).2.1
  have h3 := (finite_level D e hP hcase 1 one_pos).2.2
  have hg := (global_lim D e hF hT hS h3).2 1
  intro n
  have : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have hfd : Finite (TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))) := DFunLike.finite _
  have hcd : Nat.card (TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))) = l :=
    (GlobalTheory.T.card_dual_zmod_module_eq_card (l ^ 1) (ZMod (l ^ 1))).trans ((Nat.card_zmod _).trans (pow_one l))
  have hfin := fun v => (local_zr hF hT D (e + 1) v 1 one_pos).2.1
  have hloc : ∀ v : D.S, Nat.card (H2 ((zr D (e + 1) 1).comp (locFam D.S D.A v))) ≤ l := fun v => by
    rw [(local_zr hF hT D (e + 1) v 1 one_pos).2.2.2]
    refine le_trans ?_ hcd.le
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hpi : Nat.card (∀ v : D.S, H2 ((zr D (e + 1) 1).comp (locFam D.S D.A v))) ≤
      l ^ Module.finrank ℚ L := by
    rw [Nat.card_pi]
    refine le_trans (Finset.prod_le_pow_card _ _ l fun v _ => hloc v) ?_
    refine Nat.pow_le_pow_right hl.out.pos ?_
    rw [Finset.card_univ, Fintype.card_coe]
    exact UpperTheory.V.LDataCardLeFinrank.cardAbove L Ω l D
  have hker : LinearMap.ker (GlobalTheory.Published.PoitouTate.loc2 D.S D.A (zr D (e + 1) 1)) =
      Sha2 (zr D (e + 1) 1) (locFam D.S D.A) (continuous_locFam D.S D.A) := by
    rw [GlobalTheory.Published.PoitouTate.loc2, LinearMap.ker_pi]; rfl
  refine (card_quot_lpow 1 _ hg.1 hg.2).le.trans ?_
  rw [Submodule.card_eq_card_quotient_mul_card
    (LinearMap.ker (GlobalTheory.Published.PoitouTate.loc2 D.S D.A (zr D (e + 1) 1))),
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv, hker, ← (hS 1 one_pos).1.2.2.2]
  first
  | exact Nat.mul_le_mul_left _ (le_trans (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective) hpi)
  | (rw [mul_comm]; exact Nat.mul_le_mul_left _ (le_trans (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective) hpi))
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit
open scoped TensorProduct

namespace UpperTheory.V.K

private theorem tensCard' (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H] [inst : Module ℤ H]
    [Finite (AddCommGroup.torsion H)] (Y : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] H)) [Finite Y] :
    Nat.card Y ≤ Nat.card (AddCommGroup.torsion H) := by
  obtain rfl : inst = AddCommGroup.toIntModule H := Subsingleton.elim _ _
  exact tensCard l H Y

section

variable (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
  {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  (D : LData L Ω l) (hL : IsTotallyComplex L) (hμ : HasMuQ l L)

include hP hF hT hL hμ

theorem card_mod_le (e : ℤ) :
    Nat.card (H2 (zlTw D (e + 1)) ⧸ lpow l (H2 (zlTw D (e + 1))) 1) ≤ classNumber L * l ^ Module.finrank ℚ L := by
  have h := card_H2_quotient_le_sha hP hF hT l L Ω D e hL
  dsimp only at h
  rw [shaDualCard l L Ω D (e + 1) (chiTriv l L Ω D hμ)] at h
  exact h.trans (Nat.mul_le_mul_right _ (shaZmCard l L Ω D hL))

theorem generators (e : ℤ) :
    Real.log (Nat.card (H2 (zlTw D (e + 1)) ⧸ lpow l (H2 (zlTw D (e + 1))) 1)) ≤
      4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) * Real.log l :=
  numGens l L _ (card_mod_le hP hF hT D hL hμ e)

theorem reduction (hK : KBridge) (e : ℕ) (he : 1 ≤ e) [Finite (torsHGL L (4 * e + 4) (2 * e))] :
    Finite (H2 (zlTw D ((e : ℤ) + 1))) ∧
      Real.log (Nat.card (H2 (zlTw D ((e : ℤ) + 1)))) ≤
        4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) * ((2 * (e : ℝ)) * (2 * (e : ℝ) + 3)) *
          Real.log ((Module.finrank ℚ L : ℝ) + 1) + Real.log (Nat.card (torsHGL L (4 * e + 4) (2 * e))) := by
  obtain ⟨K, _, _, _, p, h, hp, hh⟩ := hK l L Ω D hL hμ e he
  have hfin : Finite (H2 (zlTw D ((e : ℤ) + 1))) := Finite.of_surjective p hp
  refine ⟨hfin, ?_⟩
  have hr : Finite (LinearMap.range h) := Finite.of_surjective h.rangeRestrict h.surjective_rangeRestrict
  have h1 := (cardRed l K _ _ p h _ hp hh).trans
    (Nat.mul_le_mul_left _ (tensCard' l (HGL L (4 * e + 4) (2 * e)) (LinearMap.range h)))
  have hg := generators hP hF hT D hL hμ (e : ℤ)
  have hq : Finite (H2 (zlTw D ((e : ℤ) + 1)) ⧸ lpow l (H2 (zlTw D ((e : ℤ) + 1))) 1) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  set a := Nat.card (H2 (zlTw D ((e : ℤ) + 1)) ⧸ lpow l (H2 (zlTw D ((e : ℤ) + 1))) 1) with ha
  set b := Nat.card (torsHGL L (4 * e + 4) (2 * e)) with hb
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (Nat.card_pos : 0 < a)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (Nat.card_pos : 0 < b)
  have hx0 : (0 : ℝ) < Nat.card (H2 (zlTw D ((e : ℤ) + 1))) := Nat.cast_pos.2 Nat.card_pos
  have h2 : Real.log (Nat.card (H2 (zlTw D ((e : ℤ) + 1)))) ≤ cOne (2 * e) * Real.log a + Real.log b := by
    rw [← Real.log_pow, ← Real.log_mul (by positivity) hb0.ne']
    exact Real.log_le_log hx0 (by exact_mod_cast h1)
  have hc : (cOne (2 * e) : ℝ) ≤ (2 * (e : ℝ)) * (2 * (e : ℝ) + 3) := by exact_mod_cast cOne_le (2 * e)
  have hl : Real.log l ≤ Real.log ((Module.finrank ℚ L : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast (Fact.out : l.Prime).pos) (by exact_mod_cast primeLe l L hμ)
  have hD : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.2 (discr_ne_zero L)
  have hlog : 0 ≤ Real.log (2 * ((discr L).natAbs : ℝ)) := Real.log_nonneg (by linarith)
  have hn : 0 ≤ Real.log ((Module.finrank ℚ L : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have h3 : Real.log a ≤ 4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) *
      Real.log ((Module.finrank ℚ L : ℝ) + 1) := hg.trans (mul_le_mul_of_nonneg_left hl (by positivity))
  have h4 := mul_le_mul hc h3 (Real.log_natCast_nonneg a) (by positivity)
  linarith

end

theorem TorsBound.pow {C : ℝ} (h : TorsBound C) : ∃ C', TorsBoundPow C' := by
  obtain ⟨C', H⟩ := numT C
  exact ⟨C', fun L _ _ hL e he => ⟨(h L hL e he).1, (h L hL e he).2.trans
    (H e _ _ he Module.finrank_pos (Int.natAbs_pos.2 (discr_ne_zero L)))⟩⟩

theorem lemmaK_of (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) (hK : KBridge)
    (h : ∃ C, TorsBoundPow C) : ∃ CK : ℝ, 0 < CK ∧ LemmaK CK := by
  obtain ⟨C, h⟩ := h
  obtain ⟨CK, h0, H⟩ := numFin C
  refine ⟨CK, h0, fun l _ L Ω _ _ _ _ _ D hL hμ e he => ?_⟩
  obtain ⟨hf, hb⟩ := h L hL e he
  obtain ⟨h1, h2⟩ := reduction hP hF hT D hL hμ hK e he
  refine ⟨h1, h2.trans (le_trans ?_ (H e _ _ he Module.finrank_pos (Int.natAbs_pos.2 (discr_ne_zero L))))⟩
  gcongr

end UpperTheory.V.K

end
end

section
open Formalism.GaloisCohomology

namespace UpperTheory.V.K

theorem lemmaK (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) (hK : KBridge) :
    ∃ CK : ℝ, 0 < CK ∧ LemmaK CK :=
  lemmaK_of hP hF hT hK UpperTheory.V.KT.torsMain

end UpperTheory.V.K
end
