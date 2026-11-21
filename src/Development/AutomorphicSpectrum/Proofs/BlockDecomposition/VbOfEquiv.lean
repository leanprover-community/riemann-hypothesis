import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem projective_of_genInverse_of_exact {S P Q T : Type} [CommRing S]
    [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q] [Module.Projective S Q]
    [AddCommGroup T] [Module S T] (f : P →ₗ[S] Q) (g : Q →ₗ[S] T) (s : Q →ₗ[S] P)
    (hs : f ∘ₗ s ∘ₗ f = f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    Module.Projective S T := by
  have hker : LinearMap.ker g ≤ LinearMap.ker (LinearMap.id - f ∘ₗ s) := by
    intro q hq
    obtain ⟨p, rfl⟩ := (hex q).1 hq
    have hp : f (s (f p)) = f p := LinearMap.congr_fun hs p
    simp [LinearMap.mem_ker, hp]
  let t : T →ₗ[S] Q := (LinearMap.ker g).liftQ (LinearMap.id - f ∘ₗ s) hker ∘ₗ
    (g.quotKerEquivOfSurjective hg).symm.toLinearMap
  refine Module.Projective.of_split t g ?_
  ext x
  obtain ⟨q, rfl⟩ := hg x
  have h1 : (g.quotKerEquivOfSurjective hg).symm (g q) = Submodule.Quotient.mk q := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub, hex.apply_apply_eq_zero, sub_zero]

theorem exists_genInverse_of_forall_maximal (R A B : Type) [CommRing R] [AddCommGroup A]
    [Module R A] [Module.Finite R A] [Module.Projective R A] [AddCommGroup B] [Module R B]
    [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (h : ∀ (m : Ideal R) [m.IsMaximal], ∃ s : Localization.AtPrime m ⊗[R] B →ₗ[Localization.AtPrime m] Localization.AtPrime m ⊗[R] A, f.baseChange (Localization.AtPrime m) ∘ₗ s ∘ₗ f.baseChange (Localization.AtPrime m) = f.baseChange (Localization.AtPrime m)) :
    ∃ s : B →ₗ[R] A, f ∘ₗ s ∘ₗ f = f := by
  haveI : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
  haveI : Module.FinitePresentation R (B ⧸ LinearMap.range f) :=
    Module.finitePresentation_of_surjective (LinearMap.range f).mkQ
      (LinearMap.range f).mkQ_surjective
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map f)
  haveI : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl
      (TensorProduct.mk R (Localization.AtPrime P) (B ⧸ LinearMap.range f) 1) := fun P _ =>
    (isLocalizedModule_iff_isBaseChange P.primeCompl _ _).2 (TensorProduct.isBaseChange R _ _)
  haveI : Module.Projective R (B ⧸ LinearMap.range f) := by
    refine Module.projective_of_localization_maximal' (fun P _ => Localization.AtPrime P)
      (fun P _ => Localization.AtPrime P ⊗[R] (B ⧸ LinearMap.range f))
      (fun P _ => TensorProduct.mk R (Localization.AtPrime P) (B ⧸ LinearMap.range f) 1) ?_
    intro m hm
    obtain ⟨s, hs⟩ := h m
    refine GlobalTheory.CompanionTheory.PerfVB.projective_of_genInverse_of_exact (f.baseChange (Localization.AtPrime m))
      ((LinearMap.range f).mkQ.baseChange (Localization.AtPrime m)) s hs ?_ ?_
    · rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      exact lTensor_exact _ (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective
    · rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective _ (LinearMap.range f).mkQ_surjective
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id
    (LinearMap.range f).mkQ_surjective
  have hmem : ∀ b, (LinearMap.id - t ∘ₗ (LinearMap.range f).mkQ : B →ₗ[R] B) b ∈
      LinearMap.range f := by
    intro b
    refine (Submodule.Quotient.mk_eq_zero _).1 ?_
    have hb : (LinearMap.range f).mkQ (t ((LinearMap.range f).mkQ b)) =
        (LinearMap.range f).mkQ b := LinearMap.congr_fun ht ((LinearMap.range f).mkQ b)
    change (LinearMap.range f).mkQ (b - t ((LinearMap.range f).mkQ b)) = 0
    rw [map_sub, hb, sub_self]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict (LinearMap.range f) (LinearMap.id - t ∘ₗ (LinearMap.range f).mkQ) hmem)
    f.surjective_rangeRestrict
  refine ⟨s, ?_⟩
  ext a
  have h2 : (LinearMap.range f).mkQ (f a) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self f a
  have h1 : f (s (f a)) = f a - t ((LinearMap.range f).mkQ (f a)) :=
    congrArg Subtype.val (LinearMap.congr_fun hs (f a))
  rw [h2, map_zero, sub_zero] at h1
  simpa only [LinearMap.comp_apply] using h1

end GlobalTheory.CompanionTheory.PerfVB
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_splitting_global_generalized_inverse : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A] [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B), (∀ (m : Ideal R) [m.IsMaximal], ∃ s : Localization.AtPrime m ⊗[R] B →ₗ[Localization.AtPrime m] Localization.AtPrime m ⊗[R] A, f.baseChange (Localization.AtPrime m) ∘ₗ s ∘ₗ f.baseChange (Localization.AtPrime m) = f.baseChange (Localization.AtPrime m)) → ∃ s : B →ₗ[R] A, f ∘ₗ s ∘ₗ f = f := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem rTensor_eq_zero_iff_mem_smul {R A A' P : Type} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [AddCommGroup P] [Module R P] (π : A →ₐ[R] A')
    (hπ : Function.Surjective π) (w : A ⊗[R] P) :
    π.toLinearMap.rTensor P w = 0 ↔
      w ∈ (RingHom.ker π) • (⊤ : Submodule A (A ⊗[R] P)) := by
  constructor
  · intro hw
    have hex : Function.Exact ((RingHom.ker π).restrictScalars R).subtype π.toLinearMap := by
      intro a
      constructor
      · intro h
        exact ⟨⟨a, (RingHom.mem_ker (f := π)).mpr h⟩, rfl⟩
      · rintro ⟨k, rfl⟩
        exact (RingHom.mem_ker (f := π)).mp k.2
    obtain ⟨v, rfl⟩ := ((rTensor_exact P hex hπ) w).mp hw
    clear hw
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul k p =>
      rw [LinearMap.rTensor_tmul, Submodule.coe_subtype]
      have e : (k : A) ⊗ₜ[R] p = (k : A) • ((1 : A) ⊗ₜ[R] p) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e]
      exact Submodule.smul_mem_smul k.2 Submodule.mem_top
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · intro hw
    refine Submodule.smul_induction_on hw (fun k hk x _hx => ?_) ?_
    · clear _hx
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a p =>
        rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, smul_eq_mul,
          map_mul, (RingHom.mem_ker (f := π)).mp hk, MulZeroClass.zero_mul, TensorProduct.zero_tmul]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]

theorem lTensor_rTensor_apply {R A A' P P' : Type} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    (π : A →ₐ[R] A') (f : P →ₗ[R] P') (w : A ⊗[R] P) :
    f.lTensor A' (π.toLinearMap.rTensor P w) = π.toLinearMap.rTensor P' (f.lTensor A w) := by
  induction w with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a p => simp

private theorem lift_of_smallLift_lemma {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A) (t : A) :
    RingHom.ker ((Ideal.Quotient.mkₐ R (Ideal.span {Ideal.Quotient.mk J t})).comp (Ideal.Quotient.mkₐ R J)) =
      J ⊔ Ideal.span {t} := by
  ext x
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, ← Set.image_singleton, ← Ideal.map_span,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]

theorem lift_of_smallLift : ∀ (R P₀ P₁ P₂ A : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [CommRing A] [IsLocalRing A] [Algebra R A] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂), a₁ ∘ₗ a₀ = 0 → SmallLift a₀ a₁ → Lift (a₁.baseChange A) := by
  intro R P₀ P₁ P₂ A _ _ _ _ _ _ _ _ _ _ a₀ a₁ h01 hS
  intro J t hJ hJt z hz
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  set t' : A ⧸ J := Ideal.Quotient.mk J t with ht'
  set ρ : A →ₐ[R] (A ⧸ J) ⧸ Ideal.span {t'} :=
    (Ideal.Quotient.mkₐ R (Ideal.span {t'})).comp (Ideal.Quotient.mkₐ R J) with hρ
  have hρs : Function.Surjective ρ :=
    (Ideal.Quotient.mkₐ_surjective R _).comp (Ideal.Quotient.mkₐ_surjective R J)
  have hker : RingHom.ker ρ = J ⊔ Ideal.span {t} := lift_of_smallLift_lemma J t
  have hJs : Function.Surjective (Ideal.Quotient.mkₐ R J) := Ideal.Quotient.mkₐ_surjective R J
  have hkerJ : RingHom.ker (Ideal.Quotient.mkₐ R J) = J := Ideal.Quotient.mkₐ_ker R J
  have ht : ∀ x : A ⧸ J, ¬ IsUnit x → x * t' = 0 := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : x ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hx (hu.map _)
    rw [ht', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hJt x hx'
  set z' := ρ.toLinearMap.rTensor P₁ z with hz'
  have hz2 : (a₁.lTensor A) z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A (A ⊗[R] P₂)) := by
    rwa [LinearMap.baseChange_eq_ltensor] at hz
  have hz0 : a₁.lTensor _ z' = 0 := by
    rw [hz', lTensor_rTensor_apply, rTensor_eq_zero_iff_mem_smul ρ hρs, hker]
    exact hz2
  obtain ⟨xb, y, hx0, hxy⟩ := hS (A ⧸ J) t' ht z' hz0
  obtain ⟨x₁, rfl⟩ := LinearMap.rTensor_surjective P₁ (g := (Ideal.Quotient.mkₐ R J).toLinearMap) hJs xb
  obtain ⟨y₁, rfl⟩ := LinearMap.rTensor_surjective P₀ (g := ρ.toLinearMap) hρs y
  have hcomp : ρ.toLinearMap.rTensor P₁ x₁ = (Ideal.Quotient.mkₐ R (Ideal.span {t'})).toLinearMap.rTensor P₁
      ((Ideal.Quotient.mkₐ R J).toLinearMap.rTensor P₁ x₁) := by
    rw [hρ, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
  refine ⟨x₁ - a₀.lTensor A y₁, ?_, ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor, map_sub]
    have h0 : a₁.lTensor A (a₀.lTensor A y₁) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h01, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rw [h0, sub_zero, ← hkerJ, ← rTensor_eq_zero_iff_mem_smul _ hJs, ← lTensor_rTensor_apply]
    exact hx0
  · rw [← hker, ← rTensor_eq_zero_iff_mem_smul ρ hρs, map_sub, map_sub, ← lTensor_rTensor_apply, hcomp, ← hz',
      sub_right_comm, hxy, sub_self]

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_lift_base_change_local : ∀ (R P₀ P₁ P₂ A : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [CommRing A] [IsLocalRing A] [Algebra R A] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂), a₁ ∘ₗ a₀ = 0 → SmallLift a₀ a₁ → Lift (a₁.baseChange A) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.lift_of_smallLift
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_generalisedInverse_of_fibre_ker_span :
    ∀ (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [Module.Finite R P₀] [Module.Projective R P₀] [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁] (a₀ : P₀ →ₗ[R] P₁) (e : P₀), a₀ e = 0 → (∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e)) → ∃ t : P₁ →ₗ[R] P₀, a₀ ∘ₗ t ∘ₗ a₀ = a₀ := by
  intro R P₀ P₁ _ _ _ _ _ _ _ _ _ a₀ e he hker
  have hcomp : a₀ ∘ₗ LinearMap.toSpanSingleton R P₀ e = 0 := by
    ext
    simp [he]
  have hexact : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Exact (LinearMap.lTensor m.ResidueField (LinearMap.toSpanSingleton R P₀ e))
        (LinearMap.lTensor m.ResidueField a₀) := by
    intro m _ y
    constructor
    · intro hy
      obtain ⟨c, rfl⟩ := hker m.ResidueField y hy
      refine ⟨c ⊗ₜ[R] (1 : R), ?_⟩
      rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul,
        TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    · rintro ⟨z, rfl⟩
      rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨s, t, hst⟩ := GlobalTheory.exists_homotopy_of_forall_exact_residueField hcomp hexact
  refine ⟨t, LinearMap.ext fun x => ?_⟩
  have hx : LinearMap.toSpanSingleton R P₀ e (s x) + t (a₀ x) = x := LinearMap.congr_fun hst x
  have htx : t (a₀ x) = x - LinearMap.toSpanSingleton R P₀ e (s x) := eq_sub_of_add_eq' hx
  show a₀ (t (a₀ x)) = a₀ x
  rw [htx, map_sub, LinearMap.toSpanSingleton_apply, map_smul, he, smul_zero, sub_zero]

end GlobalTheory.CompanionTheory.PerfVB
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generalized_inverse_of_unit_kernel : ∀ (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [Module.Finite R P₀] [Module.Projective R P₀] [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁] (a₀ : P₀ →ₗ[R] P₁) (e : P₀), a₀ e = 0 → (∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e)) → ∃ t : P₁ →ₗ[R] P₀, a₀ ∘ₗ t ∘ₗ a₀ = a₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.exists_generalisedInverse_of_fibre_ker_span
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_contraction_onto_homology (R P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup P₀]
    [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂]
    (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (t : P₁ →ₗ[R] P₀) (s : P₂ →ₗ[R] P₁) :
    a₁ ∘ₗ a₀ = 0 → a₀ ∘ₗ t ∘ₗ a₀ = a₀ → a₁ ∘ₗ s ∘ₗ a₁ = a₁ →
    ∃ (j : Hc a₀ a₁ →ₗ[R] P₁) (π : P₁ →ₗ[R] Hc a₀ a₁) (h : P₁ →ₗ[R] P₀) (h' : P₂ →ₗ[R] P₁),
      π ∘ₗ j = LinearMap.id ∧ a₁ ∘ₗ j = 0 ∧ π ∘ₗ a₀ = 0 ∧
        j ∘ₗ π + a₀ ∘ₗ h + h' ∘ₗ a₁ = LinearMap.id := by
  intro h10 ht hs
  have h10' : ∀ y, a₁ (a₀ y) = 0 := fun y => LinearMap.congr_fun h10 y
  have ht' : ∀ y, a₀ (t (a₀ y)) = a₀ y := fun y => LinearMap.congr_fun ht y
  have hs' : ∀ x, a₁ (s (a₁ x)) = a₁ x := fun x => LinearMap.congr_fun hs x
  have hk : ∀ x, x - s (a₁ x) ∈ LinearMap.ker a₁ := fun x => by
    rw [LinearMap.mem_ker, map_sub, hs', sub_self]
  have hp : Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀) ≤
      LinearMap.ker ((LinearMap.id - a₀ ∘ₗ t) ∘ₗ (LinearMap.ker a₁).subtype) := by
    rintro ⟨z, hz⟩ hzN
    obtain ⟨y, rfl⟩ : ∃ y, a₀ y = z := LinearMap.mem_range.1 (Submodule.mem_comap.1 hzN)
    rw [LinearMap.mem_ker]
    change a₀ y - a₀ (t (a₀ y)) = 0
    rw [ht', sub_self]
  refine ⟨Submodule.liftQ _ ((LinearMap.id - a₀ ∘ₗ t) ∘ₗ (LinearMap.ker a₁).subtype) hp,
    (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)).mkQ ∘ₗ
      LinearMap.codRestrict (LinearMap.ker a₁) (LinearMap.id - s ∘ₗ a₁) hk,
    t - t ∘ₗ s ∘ₗ a₁, s, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)) q
    have hz' : a₁ z = 0 := LinearMap.mem_ker.1 hz
    have key : (⟨z - a₀ (t z) - s (a₁ (z - a₀ (t z))), hk _⟩ : LinearMap.ker a₁) - ⟨z, hz⟩ ∈
        Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀) := by
      refine Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨-t z, ?_⟩)
      change a₀ (-t z) = z - a₀ (t z) - s (a₁ (z - a₀ (t z))) - z
      rw [map_sub a₁, hz', h10', sub_self, map_zero, sub_zero, map_neg]
      abel
    exact (Submodule.Quotient.eq _).2 key
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)) q
    have hz' : a₁ z = 0 := LinearMap.mem_ker.1 hz
    change a₁ (z - a₀ (t z)) = 0
    rw [map_sub, hz', h10', sub_zero]
  · refine LinearMap.ext fun y => ?_
    change Submodule.Quotient.mk (p := Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀))
      (⟨a₀ y - s (a₁ (a₀ y)), hk _⟩ : LinearMap.ker a₁) = 0
    refine (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨y, ?_⟩))
    change a₀ y = a₀ y - s (a₁ (a₀ y))
    rw [h10', map_zero, sub_zero]
  · refine LinearMap.ext fun x => ?_
    change x - s (a₁ x) - a₀ (t (x - s (a₁ x))) + a₀ (t x - t (s (a₁ x))) + s (a₁ x) = x
    simp only [map_sub]
    abel

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_complex_homotopy_data : ∀ (R P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (t : P₁ →ₗ[R] P₀) (s : P₂ →ₗ[R] P₁), a₁ ∘ₗ a₀ = 0 → a₀ ∘ₗ t ∘ₗ a₀ = a₀ → a₁ ∘ₗ s ∘ₗ a₁ = a₁ → ∃ (j : Hc a₀ a₁ →ₗ[R] P₁) (π : P₁ →ₗ[R] Hc a₀ a₁) (h : P₁ →ₗ[R] P₀) (h' : P₂ →ₗ[R] P₁), π ∘ₗ j = LinearMap.id ∧ a₁ ∘ₗ j = 0 ∧ π ∘ₗ a₀ = 0 ∧ j ∘ₗ π + a₀ ∘ₗ h + h' ∘ₗ a₁ = LinearMap.id := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.exists_contraction_onto_homology
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.PerfVB.ContrBC

theorem nonempty_Hc_equiv_of_contraction {S A B C H : Type} [CommRing S] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module S A] [Module S B] [Module S C]
    [Module S H] (f : A →ₗ[S] B) (g : B →ₗ[S] C) (j : H →ₗ[S] B) (π : B →ₗ[S] H)
    (h : B →ₗ[S] A) (h' : C →ₗ[S] B) (hπj : π ∘ₗ j = LinearMap.id) (hgj : g ∘ₗ j = 0)
    (hπf : π ∘ₗ f = 0) (hc : j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id) :
    Nonempty (Hc f g ≃ₗ[S] H) := by
  have hgj' : ∀ y, j y ∈ LinearMap.ker g := fun y => LinearMap.mem_ker.2 (LinearMap.congr_fun hgj y)
  have hπj' : ∀ y, π (j y) = y := fun y => LinearMap.congr_fun hπj y
  have hπf' : ∀ x, π (f x) = 0 := fun x => LinearMap.congr_fun hπf x
  have hc' : ∀ b, j (π b) + f (h b) + h' (g b) = b := fun b => LinearMap.congr_fun hc b
  have hle : Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f) ≤
      LinearMap.ker (π ∘ₗ (LinearMap.ker g).subtype) := by
    rintro ⟨z, hz⟩ hzN
    obtain ⟨x, rfl⟩ : ∃ x, f x = z := LinearMap.mem_range.1 (Submodule.mem_comap.1 hzN)
    rw [LinearMap.mem_ker]
    exact hπf' x
  refine ⟨LinearEquiv.ofLinear (Submodule.liftQ _ (π ∘ₗ (LinearMap.ker g).subtype) hle)
    ((Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f)).mkQ ∘ₗ
      LinearMap.codRestrict (LinearMap.ker g) j hgj') ?_ ?_⟩
  · refine LinearMap.ext fun y => ?_
    exact hπj' y
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f)) q
    have hz' : g z = 0 := LinearMap.mem_ker.1 hz
    have e : z = j (π z) + f (h z) := by
      have := hc' z
      rw [hz', map_zero, add_zero] at this
      exact this.symm
    have key : (⟨j (π z), hgj' (π z)⟩ : LinearMap.ker g) - ⟨z, hz⟩ ∈
        Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f) := by
      refine Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨-h z, ?_⟩)
      change f (-h z) = j (π z) - z
      calc f (-h z) = -f (h z) := map_neg _ _
        _ = j (π z) - (j (π z) + f (h z)) := by abel
        _ = j (π z) - z := by rw [← e]
    exact (Submodule.Quotient.eq _).2 key

theorem nonempty_Hc_baseChange_equiv (R A B C H S : Type) [CommRing R] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module R A] [Module R B] [Module R C]
    [Module R H] [CommRing S] [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (j : H →ₗ[R] B)
    (π : B →ₗ[R] H) (h : B →ₗ[R] A) (h' : C →ₗ[R] B) (_hgf : g ∘ₗ f = 0)
    (hπj : π ∘ₗ j = LinearMap.id) (hgj : g ∘ₗ j = 0) (hπf : π ∘ₗ f = 0)
    (hc : j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id) :
    Nonempty (Hc (f.baseChange S) (g.baseChange S) ≃ₗ[S] S ⊗[R] H) := by
  refine nonempty_Hc_equiv_of_contraction (f.baseChange S) (g.baseChange S) (j.baseChange S)
    (π.baseChange S) (h.baseChange S) (h'.baseChange S) ?_ ?_ ?_ ?_
  · rw [← LinearMap.baseChange_comp, hπj, LinearMap.baseChange_id]
  · rw [← LinearMap.baseChange_comp, hgj, LinearMap.baseChange_zero]
  · rw [← LinearMap.baseChange_comp, hπf, LinearMap.baseChange_zero]
  · rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_add, ← LinearMap.baseChange_add, hc, LinearMap.baseChange_id]

end GlobalTheory.CompanionTheory.PerfVB.ContrBC
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopy_data_cohomology_base_change : ∀ (R A B C H S : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module R A] [Module R B] [Module R C] [Module R H] [CommRing S] [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (j : H →ₗ[R] B) (π : B →ₗ[R] H) (h : B →ₗ[R] A) (h' : C →ₗ[R] B), g ∘ₗ f = 0 → π ∘ₗ j = LinearMap.id → g ∘ₗ j = 0 → π ∘ₗ f = 0 → j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id → Nonempty (Hc (f.baseChange S) (g.baseChange S) ≃ₗ[S] S ⊗[R] H) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem rankAtStalk_eq_of_finrank_fibres :
    ∀ (R K : Type) [CommRing R] [AddCommGroup K] [Module R K] [Module.Finite R K]
      [Module.Projective R K] (g : ℕ),
      (∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] K) = g) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk K p = g := by
  intro R K _ _ _ _ _ g hg p
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] K) :=
    Module.free_of_flat_of_isLocalRing
  rw [Module.rankAtStalk_eq_finrank_tensorProduct,
    ← Module.finrank_baseChange (R := IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)),
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal)
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K).finrank_eq]
  exact hg _

end GlobalTheory.CompanionTheory.PerfVB
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_fibre_rank_stalk_rank : ∀ (R K : Type) [CommRing R] [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Projective R K] (g : ℕ), (∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] K) = g) → ∀ p : PrimeSpectrum R, Module.rankAtStalk K p = g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem lid_lTensor_unit {R A B : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A]
    [Module R B] (f : A →ₗ[R] B) (u : R ⊗[R] A) :
    TensorProduct.lid R B (f.lTensor R u) = f (TensorProduct.lid R A u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r a => simp

theorem d0_one {R C : Type} [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    d0 F (1 : C0 F) = 0 := by
  funext T T' φ
  simp [d0]

theorem unit_of_model : ∀ (R C P₀ P₁ P₂ : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂]
    (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F)
    (ψ₂ : P₂ →ₗ[R] C2 F), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → ∃ e : P₀, a₀ e = 0 ∧ ψ₀ e = 1 := by
  intro R C P₀ P₁ P₂ _ _ F _ _ _ _ _ _ a₀ a₁ ψ₀ ψ₁ ψ₂ h
  obtain ⟨-, -, -, hM⟩ := h
  obtain ⟨x, y, h1, h2⟩ := (hM (ModuleCat.of R R)).1.2 ((1 : R) ⊗ₜ[R] (1 : C0 F))
    (by simp [d0_one F])
  have h1' : a₀.lTensor R x = 0 := h1
  have h2' : ψ₀.lTensor R x - (1 : R) ⊗ₜ[R] (1 : C0 F) = 0 := by simpa using h2
  refine ⟨TensorProduct.lid R P₀ x, ?_, ?_⟩
  · rw [← lid_lTensor_unit, h1', map_zero]
  · rw [← lid_lTensor_unit, sub_eq_zero.mp h2']
    simp

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_complex_unit_element : ∀ (R C P₀ P₁ P₂ : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → ∃ e : P₀, a₀ e = 0 ∧ ψ₀ e = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.unit_of_model
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfVB

section Pi

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

def piS {I : Type} {M N : I → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (u : ∀ i, M i →ₛₗ[algebraMap R S] N i) :
    (∀ i, M i) →ₛₗ[algebraMap R S] (∀ i, N i) where
  toFun x i := u i (x i)
  map_add' x y := funext fun i ↦ map_add (u i) _ _
  map_smul' r x := funext fun i ↦ (u i).map_smulₛₗ r (x i)

theorem liftSemi_piS_bijective {I : Type} [Finite I] {M N : I → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (u : ∀ i, M i →ₛₗ[algebraMap R S] N i) (hu : ∀ i, Function.Bijective (liftSemi (u i))) :
    Function.Bijective (liftSemi (piS u)) := by
  classical
  haveI := Fintype.ofFinite I
  let e := TensorProduct.piRight R S S M
  have key : (liftSemi (piS u) : S ⊗[R] (∀ i, M i) → ∀ i, N i) =
      (Pi.map fun i ↦ liftSemi (u i)) ∘ e := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero =>
      funext i
      simp
    | add a b ha hb =>
      simp only [map_add, Function.comp_apply] at ha hb ⊢
      rw [ha, hb]
      funext i
      simp
    | tmul s x =>
      funext i
      simp [e, liftSemi_tmul, piS]
  rw [key]
  exact (Function.Bijective.piMap hu).comp e.bijective

end Pi

section Cochains

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

def cT (m : BC F F') (T : C) : F.obj T →ₛₗ[algebraMap R S] F'.obj T where
  toFun := m.α T
  map_add' := map_add (m.α T)
  map_smul' := m.smul T

theorem liftSemi_cT_bijective (m : BC F F') (T : C) : Function.Bijective (liftSemi (cT m T)) := by
  obtain ⟨e, he⟩ := m.bij T
  have key : (liftSemi (cT m T) : S ⊗[R] F.obj T → F'.obj T) = e := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s b =>
      have h1 : s ⊗ₜ[R] b = s • ((1 : S) ⊗ₜ[R] b) := by simp [TensorProduct.smul_tmul']
      rw [liftSemi_tmul, h1, map_smul, he]
      rfl
  rw [key]
  exact e.bijective

theorem comparison_degree_zero_bijective [Finite C] (m : BC F F') : Function.Bijective (th0 m) :=
  liftSemi_piS_bijective (fun T ↦ cT m T) fun T ↦ liftSemi_cT_bijective m T

theorem comparison_degree_one_bijective [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    Function.Bijective (th1 m) :=
  liftSemi_piS_bijective (fun T ↦ piS fun T' ↦ piS fun _ : T ⟶ T' ↦ cT m T') fun _ ↦
    liftSemi_piS_bijective _ fun T' ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_cT_bijective m T'

theorem comparison_degree_two_bijective [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    Function.Bijective (th2 m) :=
  liftSemi_piS_bijective
    (fun T ↦ piS fun T' ↦ piS fun T'' ↦ piS fun _ : T ⟶ T' ↦ piS fun _ : T' ⟶ T'' ↦ cT m T'')
    fun _ ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_piS_bijective _ fun T'' ↦
      liftSemi_piS_bijective _ fun _ ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_cT_bijective m T''

end Cochains

theorem th_bijective (R S P : Type) [CommRing R] [CommRing S] [Algebra R S] [SemilatticeInf P]
    [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F') :
    Function.Bijective (th0 m) ∧ Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
  haveI : Finite Pᵒᵖ := Finite.of_injective (Opposite.unop : Pᵒᵖ → P) Opposite.unop_injective
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun T T' ↦ inferInstance
  exact ⟨comparison_degree_zero_bijective m, comparison_degree_one_bijective m, comparison_degree_two_bijective m⟩

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_maps_bijective_finite : ∀ (R S P : Type) [CommRing R] [CommRing S] [Algebra R S] [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧ Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.th_bijective
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB.Cls

section Abstract

variable {S A₀ A₁ A₂ B₀ B₁ B₂ D₀ D₁ D₂ H : Type} [CommRing S]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [AddCommGroup H]
  [Module S A₀] [Module S A₁] [Module S A₂] [Module S B₀] [Module S B₁] [Module S B₂]
  [Module S D₀] [Module S D₁] [Module S D₂] [Module S H]

theorem homology_equiv (a₀ : A₀ →ₗ[S] A₁) (a₁ : A₁ →ₗ[S] A₂) (b₀ : B₀ →ₗ[S] B₁)
    (b₁ : B₁ →ₗ[S] B₂) (e₀ : D₀ →ₗ[S] D₁) (e₁ : D₁ →ₗ[S] D₂) (f₀ : A₀ →ₗ[S] B₀)
    (f₁ : A₁ →ₗ[S] B₁) (f₂ : A₂ →ₗ[S] B₂) (t₀ : B₀ →ₗ[S] D₀) (t₁ : B₁ →ₗ[S] D₁)
    (t₂ : B₂ →ₗ[S] D₂) (Z : Submodule S D₁) (q : Z →ₗ[S] H)
    (hZ : Z = LinearMap.ker e₁) (hq : Function.Surjective q)
    (hq0 : ∀ z : Z, q z = 0 ↔ ∃ g, e₀ g = z.1)
    (hf₁ : ∀ y, f₁ (a₀ y) = b₀ (f₀ y)) (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (ht₁ : ∀ y, t₁ (b₀ y) = e₀ (t₀ y)) (ht₂ : ∀ x, t₂ (b₁ x) = e₁ (t₁ x))
    (ht₀s : Function.Surjective t₀) (ht₁b : Function.Bijective t₁)
    (ht₂i : Function.Injective t₂)
    (hinj : ∀ x, a₁ x = 0 → (∃ y, b₀ y = f₁ x) → ∃ y, a₀ y = x)
    (hsurj : ∀ z, b₁ z = 0 → ∃ x y, a₁ x = 0 ∧ f₁ x - z = b₀ y) :
    ∃ e : Hc a₀ a₁ ≃ₗ[S] H, ∀ (x : A₁) (hx : x ∈ LinearMap.ker a₁),
      ∃ hw : t₁ (f₁ x) ∈ Z, e (Submodule.Quotient.mk ⟨x, hx⟩) = q ⟨_, hw⟩ := by
  have hmem : ∀ x : LinearMap.ker a₁, (t₁ ∘ₗ f₁ ∘ₗ (LinearMap.ker a₁).subtype) x ∈ Z := by
    rintro ⟨x, hx⟩
    rw [hZ, LinearMap.mem_ker]
    have hx' : a₁ x = 0 := hx
    change e₁ (t₁ (f₁ x)) = 0
    rw [← ht₂, ← hf₂, hx', map_zero, map_zero]
  let Φ : LinearMap.ker a₁ →ₗ[S] H :=
    q ∘ₗ (t₁ ∘ₗ f₁ ∘ₗ (LinearMap.ker a₁).subtype).codRestrict Z hmem
  have hΦ : ∀ x : LinearMap.ker a₁, Φ x = q ⟨t₁ (f₁ x.1), hmem x⟩ := fun x ↦ rfl
  have hs : Function.Surjective Φ := by
    intro c
    obtain ⟨w, rfl⟩ := hq c
    obtain ⟨w₀, hw₀⟩ := ht₁b.2 w.1
    have hker : ∀ d, d ∈ Z → e₁ d = 0 := fun d hd ↦ by
      rw [hZ] at hd
      exact hd
    have hw : e₁ w.1 = 0 := hker _ w.2
    have hd : b₁ w₀ = 0 := ht₂i (by rw [ht₂, hw₀, hw, map_zero])
    obtain ⟨x, y, hx, hxy⟩ := hsurj w₀ hd
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hΦ, ← sub_eq_zero, ← map_sub, hq0]
    refine ⟨t₀ y, ?_⟩
    change e₀ (t₀ y) = t₁ (f₁ x) - w.1
    rw [← ht₁, ← hxy, map_sub, hw₀]
  have hk : (LinearMap.range a₀).comap (LinearMap.ker a₁).subtype = LinearMap.ker Φ := by
    ext ⟨x, hx⟩
    have hx' : a₁ x = 0 := hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range, LinearMap.mem_ker]
    rw [hΦ, hq0]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨t₀ (f₀ y), by simp only [← ht₁, hf₁]⟩
    · rintro ⟨g, hg⟩
      obtain ⟨g₀, rfl⟩ := ht₀s g
      refine hinj x hx' ⟨g₀, ht₁b.1 ?_⟩
      rw [ht₁]
      exact hg
  refine ⟨(Submodule.quotEquivOfEq _ _ hk).trans (Φ.quotKerEquivOfSurjective hs), fun x hx ↦ ?_⟩
  exact ⟨hmem ⟨x, hx⟩, rfl⟩

end Abstract

variable {R S C : Type} [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

theorem comparison_degree_one_coboundary (m : BC F F') (x : S ⊗[R] C0 F) :
    th1 m ((d0 F).baseChange S x) = d0 F' (th0 m x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s g =>
    rw [LinearMap.baseChange_tmul, th1, th0, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' φ
    change m.α T' (g T' - mp F φ (g T)) = m.α T' (g T') - mp F' φ (m.α T (g T))
    rw [map_sub, m.naturality]

theorem comparison_degree_two_coboundary (m : BC F F') (x : S ⊗[R] C1 F) :
    th2 m ((d1 F).baseChange S x) = d1 F' (th1 m x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s g =>
    rw [LinearMap.baseChange_tmul, th2, th1, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' T'' φ ψ
    change m.α T'' (mp F ψ (g T T' φ) - g T T'' (φ ≫ ψ) + g T' T'' ψ) =
      mp F' ψ (m.α T' (g T T' φ)) - m.α T'' (g T T'' (φ ≫ ψ)) + m.α T'' (g T' T'' ψ)
    rw [map_add, map_sub, m.naturality]

theorem model_comparison_degree_zero_bijective (R S C P₀ P₁ P₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁)
    (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F)
    (m : BC F F') : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) →
      Function.Bijective (th1 m) → Function.Bijective (th2 m) →
      ∃ e : Hc (a₀.baseChange S) (a₁.baseChange S) ≃ₗ[S] H1 F',
        ∀ (x : S ⊗[R] P₁) (hx : x ∈ LinearMap.ker (a₁.baseChange S)),
          ∃ hw : th1 m (ψ₁.baseChange S x) ∈ Z1 F',
            e (Submodule.Quotient.mk ⟨x, hx⟩) = H1.mk F' ⟨_, hw⟩ := by
  rintro ⟨-, hc0, hc1, hq⟩ b0 b1 b2
  obtain ⟨-, hq2⟩ := hq (ModuleCat.of R S)
  refine homology_equiv (a₀.baseChange S) (a₁.baseChange S) ((d0 F).baseChange S)
    ((d1 F).baseChange S) (d0 F') (d1 F') (ψ₀.baseChange S) (ψ₁.baseChange S) (ψ₂.baseChange S)
    (th0 m) (th1 m) (th2 m) (Z1 F') (H1.mk F') (commAlgFunctorCocyclesOne_eq_ker F') (H1.mk_surjective F')
    (fun z ↦ H1.mk_eq_zero) ?_ ?_ (comparison_degree_one_coboundary m) (comparison_degree_two_coboundary m) b0.2 b1 b2.1 hq2.1 hq2.2
  · intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc0, LinearMap.baseChange_comp,
      LinearMap.comp_apply]
  · intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc1, LinearMap.baseChange_comp,
      LinearMap.comp_apply]

end GlobalTheory.CompanionTheory.PerfVB.Cls
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_comparison_degree_one_bijective : ∀ (R S C P₀ P₁ P₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F'), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Function.Bijective (th1 m) → Function.Bijective (th2 m) → ∃ e : Hc (a₀.baseChange S) (a₁.baseChange S) ≃ₗ[S] H1 F', ∀ (x : S ⊗[R] P₁) (hx : x ∈ LinearMap.ker (a₁.baseChange S)), ∃ hw : th1 m (ψ₁.baseChange S x) ∈ Z1 F', e (Submodule.Quotient.mk ⟨x, hx⟩) = H1.mk F' ⟨_, hw⟩ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.Cls.model_comparison_degree_zero_bijective
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem comparison_degree_one_tensor_coboundary {R k C : Type} [CommRing R] [CommRing k] [Algebra R k] [Category.{0} C]
    {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} k} (m : BC F F') (y : k ⊗[R] C0 F) :
    th1 m ((d0 F).lTensor k y) = d0 F' (th0 m y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s f =>
    rw [LinearMap.lTensor_tmul, th1, th0, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' φ
    change m.α T' (d0 F f T T' φ) = d0 F' (c0 m f) T T' φ
    rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, m.naturality]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem const_on_fibre : ∀ (R k C P₀ P₁ P₂ : Type) [CommRing R] [Field k] [Algebra R k] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} k) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F') (e : P₀), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Stein F' → a₀ e = 0 → ψ₀ e = 1 → ∀ x : k ⊗[R] P₀, a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
  intro R k C P₀ P₁ P₂ _ _ _ _ F F' _ _ _ _ _ _ a₀ a₁ ψ₀ ψ₁ ψ₂ m e hM hb hS ha he x hx
  obtain ⟨-, h2, -, hQ⟩ := hM
  have hx1 : (d0 F).lTensor k (ψ₀.lTensor k x) = ψ₁.lTensor k (a₀.lTensor k x) := by
    have h := congrArg (LinearMap.lTensor k) h2
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp] at h
    exact (LinearMap.congr_fun h x).symm
  have hv : d0 F' (th0 m (ψ₀.lTensor k x)) = 0 := by
    rw [← comparison_degree_one_tensor_coboundary, hx1, hx, map_zero, map_zero]
  obtain ⟨c, hc⟩ := (hS.1 _).1 hv
  have hone : c0 m (1 : C0 F) = 1 := funext fun T ↦ map_one (m.α T)
  have hce : th0 m (ψ₀.lTensor k (c • ((1 : k) ⊗ₜ[R] e))) = th0 m (ψ₀.lTensor k x) := by
    rw [← hc, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, LinearMap.lTensor_tmul, he, th0,
      liftSemi_tmul, hone, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
  have hψ : ψ₀.lTensor k (x - c • ((1 : k) ⊗ₜ[R] e)) = 0 := by
    rw [map_sub, hb.1 hce, sub_self]
  have ha' : a₀.lTensor k (x - c • ((1 : k) ⊗ₜ[R] e)) = 0 := by
    rw [map_sub, hx, TensorProduct.smul_tmul', LinearMap.lTensor_tmul, ha, TensorProduct.tmul_zero,
      sub_zero]
  obtain ⟨y, hy⟩ := (hQ (ModuleCat.of R k)).1.1 _ ha' ⟨0, by rw [map_zero]; exact hψ.symm⟩
  refine ⟨c, sub_eq_zero.1 ?_⟩
  rw [← hy]
  rfl

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_stein_of_comparison : ∀ (R k C P₀ P₁ P₂ : Type) [CommRing R] [Field k] [Algebra R k] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} k) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F') (e : P₀), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Stein F' → a₀ e = 0 → ψ₀ e = 1 → ∀ x : k ⊗[R] P₀, a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.const_on_fibre
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_bc_comp (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S')
    (m : BC F F') (n : BC F' F'') :
    ∃ l : BC F F'', ∀ T b, l.α T b = n.α T (m.α T b) := by
  obtain ⟨α, hα₁, hα₂, hα₃⟩ := m
  obtain ⟨β, hβ₁, hβ₂, hβ₃⟩ := n
  refine ⟨⟨fun T => (β T).comp (α T), ?_, ?_, ?_⟩, fun T b => rfl⟩
  · intro T T' φ b
    simp only [RingHom.comp_apply, hα₁, hβ₁]
  · intro T r b
    simp only [RingHom.comp_apply, hα₂, hβ₂, ← IsScalarTower.algebraMap_apply]
  · intro T
    obtain ⟨e₁, he₁⟩ := hα₃ T
    obtain ⟨e₂, he₂⟩ := hβ₃ T
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' (F.obj T)).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S' S') e₁).trans e₂), fun b => ?_⟩
    simp only [LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, he₁, he₂,
      RingHom.comp_apply]

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_map_composition : ∀ (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S') (m : BC F F') (n : BC F' F''), ∃ l : BC F F'', ∀ T b, l.α T b = n.α T (m.α T b) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfVB

theorem bc_self (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    ∃ l : BC F F, ∀ T b, l.α T b = b :=
  ⟨⟨fun _ => RingHom.id _, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ => ⟨TensorProduct.lid R _, fun b => by simp [TensorProduct.lid_tmul]⟩⟩, fun _ _ => rfl⟩

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_map_identity : ∀ (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∃ l : BC F F, ∀ T b, l.α T b = b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.bc_self
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem comparison_degree_one_tower (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S')
    (m : BC F F') (n : BC F' F'') (l : BC F F'')
    (h : ∀ T b, l.α T b = n.α T (m.α T b)) (x : S ⊗[R] C1 F) :
    th1 l ((IsScalarTower.toAlgHom R S S').toLinearMap.rTensor (C1 F) x) = c1 n (th1 m x) := by
  have hcomp : ∀ f : GlobalTheory.CatCoh.C1 F,
      GlobalTheory.CompanionTheory.PerfVB.c1 l f =
        GlobalTheory.CompanionTheory.PerfVB.c1 n (GlobalTheory.CompanionTheory.PerfVB.c1 m f) := by
    intro f
    simp only [GlobalTheory.CompanionTheory.PerfVB.c1, LinearMap.coe_mk, AddHom.coe_mk, h]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s f =>
    simp only [GlobalTheory.CompanionTheory.PerfVB.th1, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', GlobalTheory.CompanionTheory.PerfVB.liftSemi_tmul, LinearMap.map_smulₛₗ, hcomp]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_degree_one_tower_formula : ∀ (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S') (m : BC F F') (n : BC F' F'') (l : BC F F''), (∀ T b, l.α T b = n.α T (m.α T b)) → ∀ x : S ⊗[R] C1 F, th1 l ((IsScalarTower.toAlgHom R S S').toLinearMap.rTensor (C1 F) x) = c1 n (th1 m x) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem form_mem_of_mem_smul_top {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (J : Ideal A) (φ : N →ₗ[A] A) {n : N} (h : n ∈ J • (⊤ : Submodule A N)) : φ n ∈ J := by
  refine Submodule.smul_induction_on h ?_ ?_
  · intro r hr n _
    rw [map_smul, smul_eq_mul]
    exact J.mul_mem_right _ hr
  · intro x y hx hy
    rw [map_add]
    exact J.add_mem hx hy

theorem exists_step_of_sup_span {A : Type} [CommRing A] (K I : Ideal A) (S : Finset A)
    (hS : K ⊔ Ideal.span (S : Set A) = I) (hne : K ≠ I) :
    ∃ (J : Ideal A) (t : A), K ≤ J ∧ J ≠ I ∧ J ⊔ Ideal.span {t} = I := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact absurd (by simpa using hS) hne
  | insert a S' _ ih =>
    by_cases h : K ⊔ Ideal.span (S' : Set A) = I
    · exact ih h
    · refine ⟨K ⊔ Ideal.span (S' : Set A), a, le_sup_left, h, ?_⟩
      rw [← hS, Finset.coe_insert, Ideal.span_insert, sup_assoc, sup_comm (Ideal.span {a})]

theorem eq_zero_of_lift_of_mem_maximalIdeal_smul (A Q N : Type) [CommRing A] [IsLocalRing A]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N) (hL : Lift b)
    (hb : ∀ q, b q ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A N)) : b = 0 := by
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A Q).FG)
  let v := Module.finBasis A N
  let g : Fin (Module.finrank A N) × S → A := fun p ↦ v.coord p.1 (b p.2)
  let I : Ideal A := Ideal.span (Set.range g)
  have hIfg : I.FG := ⟨(Set.finite_range g).toFinset, by simp [I]⟩

  have hcoord : ∀ q i, v.coord i (b q) ∈ I := by
    intro q
    have hq : q ∈ Submodule.span A (S : Set Q) := by rw [hS]; trivial
    induction hq using Submodule.span_induction with
    | mem x hx =>
      intro i
      exact Ideal.subset_span ⟨(i, ⟨x, hx⟩), rfl⟩
    | zero => intro i; simp
    | add x y _ _ hx hy =>
      intro i
      rw [map_add, map_add]
      exact I.add_mem (hx i) (hy i)
    | smul r x _ hx =>
      intro i
      rw [map_smul, map_smul, smul_eq_mul]
      exact I.mul_mem_left _ (hx i)

  have hval : ∀ q, b q ∈ I • (⊤ : Submodule A N) := by
    intro q
    rw [← v.sum_repr (b q)]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hcoord q i) trivial
  have hIm : I ≤ IsLocalRing.maximalIdeal A := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨p, rfl⟩
    exact form_mem_of_mem_smul_top _ _ (hb p.2)
  have hI : I = ⊥ := by
    by_contra hI
    set m := IsLocalRing.maximalIdeal A with hm
    have hjac : m ≤ Ideal.jacobson (⊥ : Ideal A) := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    have hne : m * I ≠ I := by
      intro h
      exact hI (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m I hIfg
        (by rw [smul_eq_mul, h]) hjac)
    obtain ⟨T, hT⟩ := hIfg
    have hsup : m * I ⊔ Ideal.span (T : Set A) = I := by
      have hT' : Ideal.span (T : Set A) = I := hT
      rw [hT']
      exact sup_eq_right.2 (Ideal.mul_le_right : m * I ≤ I)
    obtain ⟨J, t, hKJ, hJI, hJt⟩ := exists_step_of_sup_span (m * I) I T hsup hne
    have hJle : J ≤ I := hJt ▸ le_sup_left
    have htI : t ∈ I := by
      rw [← hJt]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)
    have hJtop : J ≠ ⊤ := fun h ↦ by
      have : (1 : A) ∈ m := hIm (hJle (h ▸ Submodule.mem_top))
      exact (Ideal.ne_top_iff_one m).1 (IsLocalRing.maximalIdeal.isMaximal A).ne_top this
    have hxt : ∀ x ∈ IsLocalRing.maximalIdeal A, x * t ∈ J :=
      fun x hx ↦ hKJ (Ideal.mul_mem_mul hx htI)

    have hstep : ∀ y ∈ I • (⊤ : Submodule A Q), b y ∈ J • (⊤ : Submodule A N) := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr q _
        rw [map_smul]
        have h1 : r • b q ∈ I • m • (⊤ : Submodule A N) :=
          Submodule.smul_mem_smul hr (hb q)
        have h2 : I • m • (⊤ : Submodule A N) ≤ J • (⊤ : Submodule A N) := by
          rw [← Submodule.mul_smul, mul_comm]
          exact Submodule.smul_mono_left hKJ
        exact h2 h1
      · intro x y hx hy
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    have hzJ : ∀ z, b z ∈ J • (⊤ : Submodule A N) := by
      intro z
      obtain ⟨x, hx, hxz⟩ := hL J t hJtop hxt z (by rw [hJt]; exact hval z)
      rw [hJt] at hxz
      have h := Submodule.sub_mem _ hx (hstep _ hxz)
      rwa [← map_sub, sub_sub_cancel] at h
    apply hJI
    refine le_antisymm hJle (Ideal.span_le.2 ?_)
    rintro _ ⟨p, rfl⟩
    exact form_mem_of_mem_smul_top _ _ (hzJ p.2)
  ext q
  apply v.repr.injective
  ext i
  have := hcoord q i
  rw [hI, Ideal.mem_bot] at this
  simpa using this

end GlobalTheory.CompanionTheory.PerfVB
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_reduction_zero_of_maximal : ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N), Lift b → (∀ q, b q ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A N)) → b = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB.GenInv

variable {A : Type} [CommRing A] {M M' : Type} [AddCommGroup M] [Module A M]
  [AddCommGroup M'] [Module A M']

noncomputable def proj (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) : M →ₗ[A] LinearMap.ker σ :=
  LinearMap.codRestrict _ (LinearMap.id - σ.smulRight v) (fun x => by
    simp [LinearMap.mem_ker, h])

theorem proj_coe (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) (x : M) :
    (proj σ v h x : M) = x - σ x • v := rfl

theorem proj_ker (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) (x : LinearMap.ker σ) :
    proj σ v h x = x :=
  Subtype.ext (by simp [proj_coe, LinearMap.mem_ker.1 x.2])

theorem apply_mem_smul_top (f : M →ₗ[A] M') (I : Ideal A) {x : M}
    (hx : x ∈ I • (⊤ : Submodule A M)) : f x ∈ I • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem ker_finite [Module.Finite A M] (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) :
    Module.Finite A (LinearMap.ker σ) :=
  Module.Finite.of_surjective (proj σ v h) (fun x => ⟨x, proj_ker σ v h x⟩)

theorem ker_free [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (σ : M →ₗ[A] A) (v : M)
    (h : σ v = 1) : Module.Free A (LinearMap.ker σ) := by
  haveI := ker_finite σ v h
  haveI : Module.Projective A (LinearMap.ker σ) :=
    Module.Projective.of_split (LinearMap.ker σ).subtype (proj σ v h)
      (LinearMap.ext fun x => proj_ker σ v h x)
  haveI : Module.FinitePresentation A (LinearMap.ker σ) :=
    Module.finitePresentation_of_projective _ _
  exact Module.free_of_flat_of_isLocalRing

noncomputable def kerEquiv (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) :
    M ≃ₗ[A] A × LinearMap.ker σ :=
  LinearEquiv.ofLinear (σ.prod (proj σ v h))
    (LinearMap.coprod (LinearMap.toSpanSingleton A M v) (LinearMap.ker σ).subtype)
    (by
      ext x
      · simp [h]
      · simp [proj_coe, h]
      · simp [LinearMap.mem_ker.1 x.2]
      · simp [proj_coe, LinearMap.mem_ker.1 x.2])
    (by
      ext x
      simp [proj_coe])

theorem finrank_ker [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (σ : M →ₗ[A] A) (v : M)
    (h : σ v = 1) : Module.finrank A M = 1 + Module.finrank A (LinearMap.ker σ) := by
  haveI := ker_finite σ v h
  haveI := ker_free σ v h
  rw [(kerEquiv σ v h).finrank_eq, Module.finrank_prod, Module.finrank_self]

theorem exists_form [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (y : M)
    (hy : y ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :
    ∃ σ : M →ₗ[A] A, σ y = 1 := by
  classical
  let e := Module.Free.chooseBasis A M
  by_cases h : ∀ i, e.repr y i ∈ IsLocalRing.maximalIdeal A
  · refine absurd ?_ hy
    rw [← e.sum_repr y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have hu : IsUnit (e.repr y i) := by
      by_contra hn
      exact hi ((IsLocalRing.mem_maximalIdeal _).2 hn)
    obtain ⟨u, hu⟩ := hu
    refine ⟨((↑u⁻¹ : A)) • e.coord i, ?_⟩
    simp [← hu]

noncomputable def restr (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) :
    LinearMap.ker (σ ∘ₗ b) →ₗ[A] LinearMap.ker σ :=
  b.restrict (fun x hx => by simpa using hx)

theorem restr_coe (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x : LinearMap.ker (σ ∘ₗ b)) :
    (restr b σ x : M') = b x := rfl

theorem restr_proj (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x₀ : M) (h : σ (b x₀) = 1) (q : M) :
    restr b σ (proj (σ ∘ₗ b) x₀ h q) = proj σ (b x₀) h (b q) :=
  Subtype.ext (by simp [restr_coe, proj_coe])

theorem lift_restr [IsLocalRing A] (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x₀ : M)
    (h : σ (b x₀) = 1) (hb : Lift b) : Lift (restr b σ) := by
  intro J t hJ ht z hz
  obtain ⟨x, hx, hxz⟩ := hb J t hJ ht z (apply_mem_smul_top (LinearMap.ker σ).subtype _ hz)
  refine ⟨proj (σ ∘ₗ b) x₀ h x, ?_, ?_⟩
  · rw [restr_proj]
    exact apply_mem_smul_top (proj σ (b x₀) h) _ hx
  · have e : proj (σ ∘ₗ b) x₀ h x - z = proj (σ ∘ₗ b) x₀ h (x - z) := by
      rw [map_sub, proj_ker]
    rw [e]
    exact apply_mem_smul_top _ _ hxz

theorem generalized_inverse_of_lift_rank [IsLocalRing A] : ∀ (n : ℕ) (Q N : Type) [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N] (b : Q →ₗ[A] N), Module.finrank A N = n → Lift b →
    ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q N _ _ _ _ _ _ _ _ b hn hb
    by_cases h : ∀ q, b q ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)
    · refine ⟨0, ?_⟩
      rw [GlobalTheory.T.lift_reduction_zero_of_maximal A Q N b hb h]
      simp
    · push_neg at h
      obtain ⟨x₀, hx₀⟩ := h
      obtain ⟨σ, hσ⟩ := exists_form _ hx₀
      have hσ' : (σ ∘ₗ b) x₀ = 1 := hσ
      haveI := ker_finite σ (b x₀) hσ
      haveI := ker_free σ (b x₀) hσ
      haveI := ker_finite (σ ∘ₗ b) x₀ hσ'
      haveI := ker_free (σ ∘ₗ b) x₀ hσ'
      have hlt : Module.finrank A (LinearMap.ker σ) < n := by
        have := finrank_ker σ (b x₀) hσ
        omega
      obtain ⟨s₁, hs₁⟩ := ih _ hlt (LinearMap.ker (σ ∘ₗ b)) (LinearMap.ker σ) (restr b σ) rfl
        (lift_restr b σ x₀ hσ hb)
      refine ⟨σ.smulRight x₀ + (LinearMap.ker (σ ∘ₗ b)).subtype ∘ₗ s₁ ∘ₗ proj σ (b x₀) hσ, ?_⟩
      ext q
      have h1 : restr b σ (s₁ (restr b σ (proj (σ ∘ₗ b) x₀ hσ' q))) =
          restr b σ (proj (σ ∘ₗ b) x₀ hσ' q) := LinearMap.congr_fun hs₁ _
      rw [restr_proj] at h1
      have h2 := congrArg (Subtype.val) h1
      rw [restr_coe, proj_coe] at h2
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, map_add,
        map_smul, Submodule.subtype_apply]
      rw [h2]
      abel

end GlobalTheory.CompanionTheory.PerfVB.GenInv

theorem GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift :
    ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
      [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N]
      (b : Q →ₗ[A] N), Lift b → ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b :=
  fun A Q N _ _ _ _ _ _ _ _ _ _ b hb =>
    GenInv.generalized_inverse_of_lift_rank (A := A) _ Q N b rfl hb
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalized_inverse_of_lift_local : ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N), Lift b → ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PerfVB

theorem vb_of_equiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) {g : ℕ} (h : VB R M g) : VB R N g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Module.Finite.equiv E, Module.Projective.of_equiv E, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E]
  exact h3 p

theorem vb_pure {R P₀ P₁ P₂ : Type} [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [Module.Finite R P₀]
    [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] [Module.Finite R P₂]
    [Module.Projective R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (hc : a₁ ∘ₗ a₀ = 0) (g : ℕ)
    (e : P₀) (he : a₀ e = 0)
    (hE : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 →
      ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e))
    (hG : ∀ (k : Type) [Field k] [Algebra R k],
      Module.finrank k (Hc (a₀.baseChange k) (a₁.baseChange k)) = g)
    (hL : SmallLift a₀ a₁) : VB R (Hc (a₀.baseChange R) (a₁.baseChange R)) g := by
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_generalized_inverse_of_unit_kernel R P₀ P₁ a₀ e he hE
  obtain ⟨s, hs⟩ := GlobalTheory.T.local_splitting_global_generalized_inverse R P₁ P₂ a₁ (fun m _ => by
    haveI : Module.Free (Localization.AtPrime m) (TensorProduct R (Localization.AtPrime m) P₁) :=
      Module.free_of_flat_of_isLocalRing
    haveI : Module.Free (Localization.AtPrime m) (TensorProduct R (Localization.AtPrime m) P₂) :=
      Module.free_of_flat_of_isLocalRing
    exact GlobalTheory.T.generalized_inverse_of_lift_local _ _ _ _ (GlobalTheory.T.small_lift_base_change_local R P₀ P₁ P₂ _ a₀ a₁ hc hL))
  obtain ⟨j, π, h, h', hπj, haj, hπa, hsum⟩ := GlobalTheory.T.split_complex_homotopy_data R P₀ P₁ P₂ a₀ a₁ t s hc ht hs
  have hP := Module.Projective.of_split j π hπj
  have hsurj : Function.Surjective π := fun x => ⟨j x, by simpa using LinearMap.congr_fun hπj x⟩
  have hF := Module.Finite.of_surjective π hsurj
  obtain ⟨eR⟩ := GlobalTheory.T.homotopy_data_cohomology_base_change R P₀ P₁ P₂ _ R a₀ a₁ j π h h' hc hπj haj hπa hsum
  refine vb_of_equiv (eR.trans (TensorProduct.lid R _)).symm ⟨hF, hP, GlobalTheory.T.constant_fibre_rank_stalk_rank R _ g ?_⟩
  intro k _ _
  obtain ⟨ek⟩ := GlobalTheory.T.homotopy_data_cohomology_base_change R P₀ P₁ P₂ _ k a₀ a₁ j π h h' hc hπj haj hπa hsum
  rw [← ek.finrank_eq]
  exact hG k

theorem small_lift {R C P₀ P₁ P₂ : Type} [CommRing R] [Category.{0} C]
    (hbij : ∀ (S : Type) [CommRing S] [Algebra R S] (F : C ⥤ CommAlgCat.{0} R)
      (F' : C ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧
        Function.Bijective (th1 m) ∧ Function.Bijective (th2 m))
    (F : C ⥤ CommAlgCat.{0} R) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀]
    [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F)
    (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (hM : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂)
    (hs : ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (t : B),
      (∀ x, ¬ IsUnit x → x * t = 0) →
      ∃ (F' : C ⥤ CommAlgCat.{0} B) (_ : BC F F') (F'' : C ⥤ CommAlgCat.{0} (B ⧸ Ideal.span {t}))
        (m : BC F' F''), Function.Surjective m.coef.pull1) : SmallLift a₀ a₁ := by
  intro B _ _ _ t ht z hz
  obtain ⟨F', m0, F'', m, hsurj⟩ := hs B t ht
  obtain ⟨l, hl⟩ := GlobalTheory.T.base_change_map_composition R B (B ⧸ Ideal.span {t}) C F F' F'' m0 m
  obtain ⟨b0', b1', b2'⟩ := hbij B F F' m0
  obtain ⟨b0'', b1'', b2''⟩ := hbij (B ⧸ Ideal.span {t}) F F'' l
  obtain ⟨e', he'⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R B C P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m0 hM b0' b1' b2'
  obtain ⟨e'', he''⟩ :=
    GlobalTheory.T.model_comparison_degree_one_bijective R (B ⧸ Ideal.span {t}) C P₀ P₁ P₂ F F'' a₀ a₁ ψ₀ ψ₁ ψ₂ l hM b0'' b1'' b2''
  have hmk : (Ideal.Quotient.mkₐ R (Ideal.span {t})) = IsScalarTower.toAlgHom R B (B ⧸ Ideal.span {t}) := by
    ext b
    rfl
  have hzk : z ∈ (LinearMap.baseChange (B ⧸ Ideal.span {t}) a₁).ker := LinearMap.mem_ker.2 hz
  obtain ⟨w, hw⟩ := hsurj (e'' (Submodule.Quotient.mk ⟨z, hzk⟩))
  obtain ⟨q, rfl⟩ := e'.surjective w
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hxk : LinearMap.lTensor B a₁ x = 0 := LinearMap.mem_ker.1 hx
  have hxbk : LinearMap.rTensor P₁ (IsScalarTower.toAlgHom R B (B ⧸ Ideal.span {t})).toLinearMap x ∈
      (LinearMap.baseChange (B ⧸ Ideal.span {t}) a₁).ker := by
    rw [LinearMap.mem_ker]
    change LinearMap.lTensor (B ⧸ Ideal.span {t}) a₁ _ = 0
    rw [GlobalTheory.CompanionTheory.PerfVB.lTensor_rTensor_apply, hxk, map_zero]
  have key : e'' (Submodule.Quotient.mk ⟨_, hxbk⟩) = e'' (Submodule.Quotient.mk ⟨z, hzk⟩) := by
    rw [← hw]
    obtain ⟨hw1, h1⟩ := he'' _ hxbk
    obtain ⟨hw2, h2⟩ := he' x hx
    rw [h1, h2]
    have hp : ∀ c, m.coef.pull1 (GlobalTheory.CatCoh.H1.mk F' c) = GlobalTheory.CatCoh.H1.mk F'' (m.coef.pullbackOneCocycle c) :=
      fun c => rfl
    rw [hp]
    congr 1
    apply Subtype.ext
    show th1 l _ = c1 m (th1 m0 _)
    rw [← GlobalTheory.T.comparison_degree_one_tower_formula R B (B ⧸ Ideal.span {t}) C F F' F'' m0 m l hl]
    congr 1
    exact GlobalTheory.CompanionTheory.PerfVB.lTensor_rTensor_apply _ _ _
  have hq := (Submodule.Quotient.eq _).1 (e''.injective key)
  rw [Submodule.mem_comap] at hq
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hq
  refine ⟨x, y, hxk, ?_⟩
  rw [hmk]
  rw [map_sub, Submodule.subtype_apply, Submodule.subtype_apply] at hy
  exact hy.symm

theorem perfVB : PerfVBSt := by
  unfold MainStatements.Hodge.PerfVBSt MainStatements.Hodge.AllFin
  intro R _ P _ _ F g hPerf hSt hfib hsm
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f0, p0⟩, ⟨f1, p1⟩, ⟨f2, p2⟩, ⟨f3, p3⟩, h10, h21, hψ1, hψ2,
    ⟨ψ₃, hψ3⟩, hQ⟩ := hPerf
  have hMod : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ := ⟨h10, hψ1, hψ2, fun M => ⟨(hQ M).1, (hQ M).2.1⟩⟩
  obtain ⟨e, he, hψe⟩ := GlobalTheory.T.model_complex_unit_element R Pᵒᵖ P₀ P₁ P₂ F a₀ a₁ ψ₀ ψ₁ ψ₂ hMod
  have hbij : ∀ (S : Type) [CommRing S] [Algebra R S] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
      (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧
        Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
    intro S _ _ F F' m
    exact GlobalTheory.T.comparison_maps_bijective_finite R S P F F' m
  have hE : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 →
      ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
    intro k _ _ x hx
    obtain ⟨F', m, hS⟩ := hSt k
    exact GlobalTheory.T.model_stein_of_comparison R k Pᵒᵖ P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m e hMod (hbij k F F' m).1 hS he hψe x hx
  have hG : ∀ (k : Type) [Field k] [Algebra R k],
      Module.finrank k (Hc (a₀.baseChange k) (a₁.baseChange k)) = g := by
    intro k _ _
    obtain ⟨F', m, hm⟩ := hfib k
    obtain ⟨b0, b1, b2⟩ := hbij k F F' m
    obtain ⟨ek, -⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R k Pᵒᵖ P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m hMod b0 b1 b2
    rw [ek.finrank_eq]
    exact hm
  have hL : SmallLift a₀ a₁ := small_lift hbij F a₀ a₁ ψ₀ ψ₁ ψ₂ hMod (fun B _ _ _ t ht => hsm B t ht)
  haveI := f0
  haveI := p0
  haveI := f1
  haveI := p1
  haveI := f2
  haveI := p2
  have hv := vb_pure a₀ a₁ h10 g e he hE hG hL
  obtain ⟨l, -⟩ := GlobalTheory.T.base_change_map_identity R Pᵒᵖ F
  obtain ⟨c0, c1, c2⟩ := hbij R F F l
  obtain ⟨eR, -⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R R Pᵒᵖ P₀ P₁ P₂ F F a₀ a₁ ψ₀ ψ₁ ψ₂ l hMod c0 c1 c2
  exact vb_of_equiv eR hv

end GlobalTheory.CompanionTheory.PerfVB
end
end
