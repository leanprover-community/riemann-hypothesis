import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHenselRootResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonUnramifiedExtension
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsGlobalConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftFiniteCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationDataNormalRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSymmetricSquareRoot
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsTwoTorsionTranslateSameLambdaBundle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnifPolarizationSquareIso

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_element_unramified : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], ((residue R).comp φ).Finite → ((residue R).comp φ).FormallyUnramified → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  first | exact @GlobalTheory.exists_hensel_generator_of_residue_finite_unramified | exact GlobalTheory.exists_hensel_generator_of_residue_finite_unramified | (intros; apply GlobalTheory.exists_hensel_generator_of_residue_finite_unramified <;> assumption)
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_unramified_extension : ∀ {k K L : Type} [Field k] [Field K] [Field L] (i : k →+* K) (j : k →+* L), i.Finite → i.FormallyUnramified → ∃ (M : Type) (_ : Field M) (u : K →+* M) (v : L →+* M), u.comp i = v.comp j ∧ v.Finite ∧ v.FormallyUnramified := by
  first | exact @GlobalTheory.compositum_finite_formallyUnramified | exact GlobalTheory.compositum_finite_formallyUnramified | (intros; apply GlobalTheory.compositum_finite_formallyUnramified <;> assumption)
end

section
section
open IsLocalRing GlobalTheory.LN Polynomial

namespace GlobalTheory.UnramExt

theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have hle : (I • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) I :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_finite_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) [hI : IsAdicComplete I R] :
    IsAdicComplete I M := by
  have htop : ∀ k : ℕ, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hx n
    rw [SModEq.zero, mem_smul_top_iff_repr b] at this
    rw [SModEq.zero, htop]
    exact this i
  have hP' : IsPrecomplete I M := by
    rw [isPrecomplete_iff]
    intro F hF
    have hP := hI.toIsPrecomplete
    rw [isPrecomplete_iff] at hP
    have hc : ∀ i, ∃ L : R, ∀ k, b.repr (F k) i ≡ L [SMOD (I ^ k • ⊤ : Submodule R R)] := by
      intro i
      refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
      have := hF hmn
      rw [SModEq.sub_mem, mem_smul_top_iff_repr b] at this
      rw [SModEq.sub_mem, htop]
      simpa using this i
    choose L hL using hc
    refine ⟨∑ i, L i • b i, fun k => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    intro i
    have := hL i k
    rw [SModEq.sub_mem, htop] at this
    have hr : b.repr (∑ j, L j • b j) i = L i := by
      have h := congrFun (b.equivFun.apply_symm_apply L) i
      rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
    rw [map_sub, Finsupp.sub_apply, hr]
    exact this
  exact { toIsHausdorff := hH, toIsPrecomplete := hP' }

theorem exists_unit_mul_pow {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {π : V} (hπ : maximalIdeal V = Ideal.span {π}) (x : V) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : V), IsUnit u ∧ x = u * π ^ n := by
  classical
  have hK : ⨅ n : ℕ, (maximalIdeal V) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top
  have hex : ∃ n, x ∉ (maximalIdeal V) ^ n := by
    by_contra h
    push_neg at h
    apply hx
    have : x ∈ ⨅ n : ℕ, (maximalIdeal V) ^ n := (Submodule.mem_iInf _).2 h
    rwa [hK] at this
  have hspec := Nat.find_spec hex
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0, pow_zero, Ideal.one_eq_top] at hspec
    exact hspec Submodule.mem_top
  have hmem : x ∈ (maximalIdeal V) ^ k := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    simpa using this
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine ⟨k, u, ?_, hu.symm⟩
  by_contra hnu
  have hu' : u ∈ maximalIdeal V := (mem_maximalIdeal u).2 hnu
  apply hspec
  rw [hk, ← hu, hπ, Ideal.span_singleton_pow, pow_succ]
  rw [hπ] at hu'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu'
  exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩

theorem isDomain_of_maximalIdeal_eq_span {V : Type} [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] {π : V} (hπ : maximalIdeal V = Ideal.span {π}) (hn : ∀ n : ℕ, π ^ n ≠ 0) :
    IsDomain V := by
  have : NoZeroDivisors V := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_pow hπ a h.1
    obtain ⟨m, w, hw, rfl⟩ := exists_unit_mul_pow hπ b h.2
    have : (u * w) * π ^ (n + m) = 0 := by rw [← hab]; ring
    exact hn (n + m) ((hu.mul hw).mul_right_eq_zero.1 this)
  exact NoZeroDivisors.to_isDomain V

end GlobalTheory.UnramExt

open GlobalTheory.UnramExt in

theorem GlobalTheory.exists_unramified_ext_residue : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ {L : Type} [Field L] (v : ResidueField W →+* L), v.Finite → v.FormallyUnramified → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (τ : L →+* ResidueField V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ (∀ ϖ : W, Irreducible ϖ → Irreducible (f ϖ)) ∧ ∀ w : W, τ (v (residue W w)) = residue V (f w) := by
  intro W _ _ _ hW L _ v hfin hfu
  obtain ⟨hdvr, hcomp, hchar⟩ := (cDvr_iff W).1 hW
  letI : Algebra (ResidueField W) L := v.toAlgebra
  haveI : Module.Finite (ResidueField W) L := hfin
  haveI : Algebra.FormallyUnramified (ResidueField W) L := hfu
  haveI : Algebra.IsSeparable (ResidueField W) L := Algebra.FormallyUnramified.isSeparable _ _
  let pb : PowerBasis (ResidueField W) L := Field.powerBasisOfFiniteOfSeparable _ L
  set gb := minpoly (ResidueField W) pb.gen with hgb
  have hgb_mon : gb.Monic := minpoly.monic pb.isIntegral_gen
  have hgb_irr : Irreducible gb := minpoly.irreducible pb.isIntegral_gen
  have hgb_deg : 0 < gb.natDegree := minpoly.natDegree_pos pb.isIntegral_gen
  have hlift : gb ∈ lifts (residue W) :=
    (lifts_iff_coeff_lifts gb).2 fun n => residue_surjective _
  obtain ⟨g, hgmap, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic hlift hgb_mon
  have hgdeg' : g.degree ≠ 0 := by
    rw [degree_eq_natDegree hgmon.ne_zero, hgdeg]
    exact_mod_cast hgb_deg.ne'
  let V := AdjoinRoot g
  let f : W →+* V := algebraMap W V
  have hfof : f = AdjoinRoot.of g := AdjoinRoot.algebraMap_eq g
  have hfinj : Function.Injective f := by
    rw [hfof]; exact AdjoinRoot.of.injective_of_degree_ne_zero hgdeg'
  let pbV : PowerBasis W V := AdjoinRoot.powerBasis' hgmon
  haveI : Module.Finite W V := pbV.finite
  haveI : Algebra.IsIntegral W V := inferInstance
  haveI : IsNoetherianRing V := isNoetherian_of_tower W (inferInstance : IsNoetherian W V)
  set mW := maximalIdeal W with hmWdef
  set M : Ideal V := Ideal.map f mW with hMdef

  have hirr : Irreducible (g.map (Ideal.Quotient.mk mW)) := by
    have := hgb_irr
    rw [← hgmap] at this
    exact this
  haveI hmWmax : mW.IsMaximal := maximalIdeal.isMaximal W
  letI : Field (W ⧸ mW) := Ideal.Quotient.field mW
  have hM : M.IsMaximal := by
    have h1 := PrincipalIdealRing.isMaximal_of_irreducible hirr
    have h2 := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 h1
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    have e := AdjoinRoot.quotEquivQuotMap g mW
    rw [hMdef, hfof]
    exact MulEquiv.isField h2 e.toRingEquiv.toMulEquiv
  have huniq : ∀ P : Ideal V, P.IsMaximal → P = M := by
    intro P hP
    have h1 : (P.comap (algebraMap W V)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    have h2 : P.comap f = mW := IsLocalRing.eq_maximalIdeal h1
    have h3 : M ≤ P := Ideal.map_le_iff_le_comap.2 h2.ge
    exact (hM.eq_of_le hP.ne_top h3).symm
  haveI : IsLocalRing V := IsLocalRing.of_unique_max_ideal ⟨M, hM, fun P hP => huniq P hP⟩
  have hmV : maximalIdeal V = M := huniq _ (maximalIdeal.isMaximal V)
  have hspan : ∀ ϖ : W, Irreducible ϖ → maximalIdeal V = Ideal.span {f ϖ} := by
    intro ϖ hϖ
    rw [hmV, hMdef, hmWdef, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hpow : ∀ n : ℕ, f ϖ₀ ^ n ≠ 0 := by
    intro n h
    rw [← map_pow, ← map_zero f] at h
    exact pow_ne_zero n hϖ₀.ne_zero (hfinj h)
  haveI hdom : IsDomain V := isDomain_of_maximalIdeal_eq_span (hspan ϖ₀ hϖ₀) hpow
  have hirrV : Irreducible (f ϖ₀) := by
    have hprime : (Ideal.span {f ϖ₀}).IsPrime := by
      rw [← hspan ϖ₀ hϖ₀]; exact (maximalIdeal.isMaximal V).isPrime
    have hne : f ϖ₀ ≠ 0 := by simpa using hpow 1
    exact ((Ideal.span_singleton_prime hne).1 hprime).irreducible
  haveI hdvrV : IsDiscreteValuationRing V := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨f ϖ₀, hirrV, ?_⟩
    intro x hx
    obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_pow (hspan ϖ₀ hϖ₀) x hx
    exact ⟨n, hu.unit, by simp [mul_comm]⟩
  haveI hloc : IsLocalHom f := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : f a ∈ maximalIdeal V := by
      rw [hmV]; exact Ideal.mem_map_of_mem f ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 this ha
  haveI : IsAdicComplete mW W := hcomp
  have hcompV : IsAdicComplete (maximalIdeal V) V := by
    rw [hmV, hMdef]
    exact (IsAdicComplete.map_algebraMap_iff mW V).2 (isAdicComplete_of_finite_basis pbV.basis mW)
  haveI : CharZero W := hchar
  have hcharV : CharZero V := charZero_of_injective_ringHom hfinj

  letI : Algebra (ResidueField W) (ResidueField V) := (ResidueField.map f).toAlgebra
  have hroot : aeval (residue V (AdjoinRoot.root g)) gb = 0 := by
    rw [aeval_def, ← hgmap, eval₂_map]
    change eval₂ ((ResidueField.map f).comp (residue W)) _ g = 0
    rw [ResidueField.map_comp_residue, ← hom_eval₂, hfof, AdjoinRoot.eval₂_root, map_zero]
  let τ : L →ₐ[ResidueField W] ResidueField V := pb.lift _ hroot
  refine ⟨V, inferInstance, hdom, inferInstance, f, τ.toRingHom, (cDvr_iff V).2 ⟨hdvrV, hcompV, hcharV⟩,
    hfinj, hloc, fun ϖ hϖ => ?_, fun w => ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer (f ϖ)).2 (hspan ϖ hϖ)
  · have := τ.commutes (residue W w)
    exact this.trans (ResidueField.map_residue f w)
end

open IsLocalRing GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_residue_lift_irreducible : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ {L : Type} [Field L] (v : ResidueField W →+* L), v.Finite → v.FormallyUnramified → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (τ : L →+* ResidueField V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ (∀ ϖ : W, Irreducible ϖ → Irreducible (f ϖ)) ∧ ∀ w : W, τ (v (residue W w)) = residue V (f w) := by
  atlas_forward_decl GlobalTheory.exists_unramified_ext_residue
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitLift

theorem eq_of_stalkClosedPointTo' {X : Scheme.{0}} {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (ξ : Sp R ⟶ X) (χ : Sp W ⟶ X) (h : ξ (closedPoint R) = χ (closedPoint W))
    (ψ : R →+* V) (f : W →+* V)
    (hc : ψ.comp (Scheme.stalkClosedPointTo ξ).hom =
      f.comp ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ).hom) :
    spMap f ≫ χ = spMap ψ ≫ ξ := by
  have key : ∀ (x y : X) (hxy : x = y) (g : X.presheaf.stalk y ⟶ CommRingCat.of V),
      Spec.map ((X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ g) ≫ X.fromSpecStalk x =
        Spec.map g ≫ X.fromSpecStalk y := by
    intro x y hxy g
    subst hxy
    simp
  have hc' : Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom ψ =
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ ≫ CommRingCat.ofHom f := by
    ext a
    exact congrArg (fun g : _ →+* V => g a) hc
  conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ]
  conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  rw [hc', key _ _ h]

theorem exists_lift : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ X), χ (closedPoint W) = ξ (closedPoint R) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : R →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ Irreducible (f ϖ) ∧ spMap f ≫ χ = spMap ψ ≫ ξ := by
  intro X R _ _ _ ξ hR hξ hur W _ _ _ hW ϖ hϖ χ hχ
  obtain ⟨-, -, hRc, -⟩ := hR
  haveI := hRc
  have hpt : ξ (closedPoint R) = χ (closedPoint W) := hχ.symm
  let φ : X.presheaf.stalk (ξ (closedPoint R)) →+* R := (Scheme.stalkClosedPointTo ξ).hom
  let α : X.presheaf.stalk (ξ (closedPoint R)) →+* W :=
    ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ Scheme.stalkClosedPointTo χ).hom
  haveI : IsLocalHom α := by
    simp only [α, CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom φ := Scheme.isLocalHom_stalkClosedPointTo' ξ
  obtain ⟨hflat, hmax, hfin⟩ := hξ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hur' : (ResidueField.map φ).FormallyUnramified := by
    rw [← ResidueField.map_comp_residue] at hur
    exact RingHom.FormallyUnramified.of_comp hur
  obtain ⟨θ, q, hqm, hqθ, hqd, hgen, hind⟩ := GlobalTheory.T.exists_primitive_element_unramified φ hfin hur
  obtain ⟨M, _, u, v, huv, hvf, hvu⟩ := GlobalTheory.T.exists_common_unramified_extension (ResidueField.map φ) (ResidueField.map α) hfin' hur'
  obtain ⟨V, _, _, _, f, τ, hV, hfinj, hfloc, hirr, hτ⟩ := GlobalTheory.T.exists_dvr_residue_lift_irreducible W hW v hvf hvu
  haveI := hV.2.1
  let σ : ResidueField R →+* ResidueField V := τ.comp u
  have hσ : ∀ a, σ (residue R (φ a)) = residue V ((f.comp α) a) := by
    intro a
    have h1 := congrArg (fun g => g (residue _ a)) huv
    simp only [RingHom.comp_apply, ResidueField.map_residue] at h1
    simp only [σ, RingHom.comp_apply, h1, hτ]
  obtain ⟨η, hη, -⟩ := GlobalTheory.T.exists_hensel_root_residue φ (f.comp α) σ hσ θ q hqm hqθ hqd
  have hgp := GlobalTheory.T.polynomial_approx_pow_maximal φ hmax θ hgen
  have hip := GlobalTheory.T.polynomial_approx_uniqueness φ hflat hmax θ q hqm hqθ hgp hind
  obtain ⟨ψ, hψ, hψl⟩ := GlobalTheory.T.hensel_roots_compatible φ (f.comp α) inferInstance θ η q hqm hqθ hη hgp hip
  exact ⟨V, inferInstance, inferInstance, inferInstance, f, ψ, hV, hfinj, hfloc, hψl, hirr ϖ hϖ,
    eq_of_stalkClosedPointTo' ξ χ hpt ψ f hψ⟩

end GlobalTheory.TraitLift
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.PolOrdPull

theorem idlAlong_pull {X Y : Scheme.{0}} (D : GlobalTheory.EffCartierData X) (π : Y ⟶ X) (h : D.KeepsRegular π)
    {A : Type} [CommRing A] [IsLocalRing A] (y : Sp A ⟶ Y) :
    idlAlong (D.pull π h).idealSheaf y = idlAlong D.idealSheaf (y ≫ π) := by
  obtain ⟨k, hk⟩ := D.exists_mem ((y ≫ π) (closedPoint A))
  have hk' : ⊤ ≤ (y ≫ π) ⁻¹ᵁ D.U k := (Scheme.preimage_eq_top_of_closedPoint_mem _ hk).ge
  have hk'' : ⊤ ≤ y ⁻¹ᵁ (D.pull π h).U k := hk'
  rw [GlobalTheory.TraitGen.idlAlong_idealSheaf_eq (D.pull π h) y k hk'', GlobalTheory.TraitGen.idlAlong_idealSheaf_eq D (y ≫ π) k hk']
  congr 2

end GlobalTheory.PolOrdPull

open GlobalTheory.PolOrdPull in
theorem GlobalTheory.TorRef.isPhiDiv_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (X : Model Xo c β) (Z : Model Xo c β') (π : Z.X ⟶ X.X) (ψ : InvFun (𝓞 E)) (DX : GlobalTheory.EffCartierData X.X) (h : DX.KeepsRegular π), Z.j ≫ π = X.j → Nonempty (SABMap Z.t X.t π) → IsPhiDiv ψ X DX → IsPhiDiv ψ Z (DX.pull π h) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' X Z π ψ DX h hj ⟨n⟩ hX
  intro W _ _ _ hW ϖ hϖ χ t m P hgen be hbe hmon
  obtain ⟨m₂, -⟩ := GlobalTheory.LevelCover.sab_comp m n rfl
  have hgen' : Set.range (jK W ≫ χ ≫ π) ⊆ Set.range X.j := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := hgen ⟨w, rfl⟩
    refine ⟨z, ?_⟩
    rw [← hj, Scheme.Hom.comp_apply, hz]
    rfl
  obtain ⟨k, hk, hI⟩ := hX W hW ϖ hϖ (χ ≫ π) t m₂ P hgen' be hbe hmon
  exact ⟨k, hk, (idlAlong_pull DX π h χ).trans hI⟩
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_lift_finite_cover : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ψ : R →+* V, IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (ψ' : R' →+* V'), CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ' ∧ ψ'.comp ρ = f.comp ψ := by
  first | exact @GlobalTheory.LocExt.exists_cDvr_ext_of_finite | exact GlobalTheory.LocExt.exists_cDvr_ext_of_finite | (intros; apply GlobalTheory.LocExt.exists_cDvr_ext_of_finite <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.SiegLoc.PelUnif

theorem isUnifOf_pel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g n : ℕ) (R : Type) [CommRing R] (ω : R →+* c.F) (F : SFam g n (zetaAway n))
    (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left)
    (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), IsDedFrac ω → IsSiegPull s j G e κ C π →
    ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (χ : Sp W ⟶ C.X) (t : SAB H (Sp W)) (_ : SABMap t C.t χ)
      (P : PELUnif I t), Set.range (jK W ≫ χ) ⊆ Set.range C.j → ∃ π' : t.G.left ⟶ G.left, IsUnifOf F j e (χ ≫ π) π' P.U := by
  intro E _ _ _ H D l Xo c g n R _ ω F S s j G _ e κ C π hω hS W _ _ I χ t m P hr
  obtain ⟨mu, y, α, α₂, -, -, hμ, hy, hα, hsq, hlam, hφ⟩ := hS

  obtain ⟨⟨_, _⟩, _, _⟩ := hω
  letI : Algebra R c.F := ω.toAlgebra
  obtain ⟨-, -, -, hpre, hfl, -, -⟩ :=
    GlobalTheory.genericPart_dense_proOpen R c.F C.X (Xo.XF c) C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  haveI : IsPreimmersion C.j := hpre
  haveI : Flat C.j := hfl
  obtain ⟨y₀, hy₀⟩ := HomExt.exists_lift_of_range_subset C.j (jK W ≫ χ) hr

  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A t.G (jK W) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso P.U.gen.symm).comp
      (isGrpPullback_pullback t.G (jK W))).congr (Category.id_comp _) rfl
  have hA := gpG.comp m.cart
  let ψ : P.A.A.left ⟶ C.t.G.left := (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W)) ≫ m.φ
  have hw : ψ ≫ C.t.G.hom = (P.A.A.hom ≫ y₀) ≫ (C.jQ ≫ pullback.fst _ _) := by
    rw [hA.1.w]
    simp only [Category.assoc]
    rw [← hy₀]
    rfl
  let α₀ : P.A.A.left ⟶ C.oF.t.G.left := C.m.cart.1.lift ψ (P.A.A.hom ≫ y₀) hw
  have hα₀ : α₀ ≫ C.m.φ = ψ := C.m.cart.1.lift_fst _ _ _
  have hα₀' : α₀ ≫ C.oF.t.G.hom = P.A.A.hom ≫ y₀ := C.m.cart.1.lift_snd _ _ _
  have hB : IsGrpPullback P.A.A C.oF.t.G y₀ α₀ :=
    C.m.cart.cancel (hA.congr (hy₀.symm) hα₀.symm) hα₀'

  have hB' : IsGrpPullback P.A.A F.univ.A (y₀ ≫ y) (α₀ ≫ α) := hB.comp hα
  let U := lift (pushPt hB.1.w (fst P.A.A P.A.A)) (pushPt hB.1.w (snd P.A.A P.A.A))
  have hU₁ : U.left ≫ (fst C.oF.t.G C.oF.t.G).left = (fst P.A.A P.A.A).left ≫ α₀ := by
    rw [← Over.comp_left]
    exact congrArg (fun z => z.left) (lift_fst (pushPt hB.1.w (fst P.A.A P.A.A)) (pushPt hB.1.w (snd P.A.A P.A.A)))
  have hU₂ : U.left ≫ (snd C.oF.t.G C.oF.t.G).left = (snd P.A.A P.A.A).left ≫ α₀ := by
    rw [← Over.comp_left]
    exact congrArg (fun z => z.left) (lift_snd (pushPt hB.1.w (fst P.A.A P.A.A)) (pushPt hB.1.w (snd P.A.A P.A.A)))
  have hsq' : Geo.Tor.IsSquare (α₀ ≫ α) (U.left ≫ α₂) :=
    ⟨by rw [Category.assoc, hsq.1, ← Category.assoc, hU₁, Category.assoc],
     by rw [Category.assoc, hsq.2, ← Category.assoc, hU₂, Category.assoc]⟩

  have i₁ : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have i₀ : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have ext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK W))) := P.bundle ▸ P.U.ext
  have h₁ : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W))) :=
    LBIso.chartPull (chartPullSec P.A.L P.U.gen.hom.left P.U.gen.inv.left i₁)
      (chartPullSame t.PP.L (fun _ : PUnit => P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W))
        (fun _ => pullback.fst t.G.hom (jK W)) (fun _ => 1) P.U.gen.inv.left fun _ => rfl) ext
  have hm : LBIso t.PP.L (C.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hc : LBIso C.oF.t.PP.L (C.t.PP.L.pull C.m.φ) := by
    obtain ⟨w, hw, -⟩ := C.m.lin
    exact ⟨w, hw⟩
  have h₂ : LBIso (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W))) (C.t.PP.L.pull ψ) :=
    LBIso.chartPull (chartPullPull t.PP.L _)
      (chartPullSame C.t.PP.L (fun _ : PUnit => ψ) (fun _ => m.φ) (fun _ => 1) _ fun _ => rfl) hm
  have h₃ : LBIso (C.oF.t.PP.L.pull α₀) (C.t.PP.L.pull ψ) :=
    LBIso.chartPull (chartPullPull C.oF.t.PP.L α₀)
      (chartPullSame C.t.PP.L (fun _ : PUnit => ψ) (fun _ => C.m.φ) (fun _ => 1) α₀ fun _ => hα₀.symm) hc
  have hL : LBIso P.A.L (C.oF.t.PP.L.pull α₀) :=
    LBIso.trans P.A.isLB (pull_isLB C.t.PP.isLB _) (pull_isLB C.oF.t.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB C.t.PP.isLB _) h₁ h₂) h₃.symm
  have hΛ₁ : LBIso (abelian₂ P.A.A P.A.L) (abelian₂ P.A.A (C.oF.t.PP.L.pull α₀)) :=
    GlobalTheory.PelPrim.lbIso_linComb hL _ _
  have hΛ₂ : LBIso (abelian₂ P.A.A (C.oF.t.PP.L.pull α₀)) (F.univ.P.pull (U.left ≫ α₂)) :=
    LBIso.chartPull
      (chartPullLinComb C.oF.t.PP.L α₀ _ _ _ U.left fun I => psum_push hB _ _ U (fun i => by
        fin_cases i
        · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact hU₁.symm)
        · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact hU₂.symm)) I.down)
      (chartPullSame F.univ.P (fun _ : PUnit => U.left ≫ α₂) (fun _ => α₂) (fun _ => 1) U.left fun _ => rfl) hlam
  have hΛ : LBIso (abelian₂ P.A.A P.A.L) (F.univ.P.pull (U.left ≫ α₂)) :=
    LBIso.trans (LB.isLB_linComb P.A.isLB _ _) (LB.isLB_linComb (pull_isLB C.oF.t.PP.isLB _) _ _)
      (pull_isLB F.univ.isLB _) hΛ₁ hΛ₂
  refine ⟨m.φ ≫ mu, m.cart.comp hμ, y₀ ≫ y, α₀ ≫ α, U.left ≫ α₂, ?_, hB', hsq', hΛ, ?_⟩
  · rw [Category.assoc, hy, ← Category.assoc, hy₀, Category.assoc]
  · rw [Category.assoc, ← hφ, ← Category.assoc α₀, hα₀]
    simp only [ψ, Category.assoc]
    rw [← Category.assoc P.U.gen.hom.left, i₀, Category.id_comp]

end GlobalTheory.SiegLoc.PelUnif
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_pullback_dvr_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g n : ℕ) (R : Type) [CommRing R] (ω : R →+* c.F) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), IsDedFrac ω → IsSiegPull s j G e κ C π → ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (χ : Sp W ⟶ C.X) (t : SAB H (Sp W)) (_ : SABMap t C.t χ) (P : PELUnif I t), Set.range (jK W ≫ χ) ⊆ Set.range C.j → ∃ π' : t.G.left ⟶ G.left, IsUnifOf F j e (χ ≫ π) π' P.U := by
  atlas_forward_decl GlobalTheory.SiegLoc.PelUnif.isUnifOf_pel
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_data_normal_ring : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), IsGrpPullback F.univ.A G j e → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (I : Ideal R) (ξ : Sp R ⟶ S) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : Unif I D A G'), IsUnifOf F j e ξ π U → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R) (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (β : B.left ⟶ G'.left) (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), y ≫ j = x ≫ ξ → IsGrpPullback B G' x β → IsGrpPullback B F.univ.A y α → α ≫ e = β ≫ π → IsSquare α α₂ → LBIso (abelian₂ B (U.LG.L.pull β)) (F.univ.P.pull α₂) := by
  first | exact @GlobalTheory.UnifLamFibre.lam_pull_eq_univ | exact GlobalTheory.UnifLamFibre.lam_pull_eq_univ | (intros; apply GlobalTheory.UnifLamFibre.lam_pull_eq_univ <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigSymBaseChange

theorem rigidified_and_sym_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  intro S S' f G _ B _ β gp L σ hσ
  refine ⟨PolBaseChange.rigidified_pull gp ⟨L.rig, L.rigGen⟩, fun _ => ⟨⊤, trivial, ?_⟩⟩
  refine gen_chartPull (chartPullLinComb L.L β (K := Fin 2) _
    ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1] ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) fun k => ?_) σ hσ
  fin_cases k
  · show ((B.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : B ⟶ B).left) ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ (GrpObj.inv : G ⟶ G).left
    rw [Category.assoc, PolBaseChange.inv_comm gp, Category.assoc]
  · show (B.hom ⁻¹ᵁ ⊤).ι ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ 𝟙 G.left
    rw [Category.comp_id]

end GlobalTheory.RigSymBaseChange
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  atlas_forward_decl GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SiegFibrePol

theorem polAV_of_lam_univ : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (K : Type) [Field K] (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A y α → IsSquare α α₂ → ∀ L : LB B.left, L.IsLB → Rigidified B L → Out.Sym B L → LBIso (abelian₂ B L) (F.univ.P.pull α₂) → IsAbelianScheme B ∧ RelAmple B L ∧ KTriv B L := by
  intro o _ ζ g n F K _ y B _ α α₂ hpb hsq L hL hrig hsym hΛ
  open GlobalTheory.CechPic GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw in
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hpb
  have := hB.comm
  have laws : Out.Laws := GlobalTheory.allSixLaws.1
  haveI : IsProper F.univ.A.hom := F.univ.ab.proper
  have hP' : (F.univ.P.pull α₂).IsLB := pull_isLB F.univ.isLB α₂
  have hrefl : LBIso (F.univ.P.pull α₂) (F.univ.P.pull α₂) := (GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl
  have hn := GlobalTheory.SiegelPull.nondeg_pull hpb hsq F.univ.isLB hP' hrefl F.princ.2
  have hM0 : (F.univ.diag.pull α).IsLB := pull_isLB (pull_isLB F.univ.isLB _) α
  have hamp0 : Out.RelAmple B (F.univ.diag.pull α) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback (pull_isLB F.univ.isLB _) F.princ.1 hpb.1
  have hd : ((F.univ.P.pull α₂).pull (lift (𝟙 B) (𝟙 B)).left).IsLB := pull_isLB hP' _
  have hdiag := GlobalTheory.SiegelPull.diag_iso hsq hrefl
  have eM0 : GlobalTheory.CechPic.cls _ hM0 = GlobalTheory.CechPic.cls _ hd := ((GlobalTheory.CechPic.cls_eq_iff hd hM0).2 hdiag).symm
  have hp : IsProjBy B.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B _ hB hM0 hamp0 K (𝟙 _) _ (𝟙 _) B.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ := GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy laws K B hB hp L hL
  have s₁ := GlobalTheory.SameLam.pull_inv_cls hL hsym
  have e₀ : GlobalTheory.CechPic.cls _ hP' = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (fst B B) (snd B B) :=
    ((GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) hP').2 hΛ).symm.trans
      (GlobalTheory.CechPic.cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  have hη : GlobalTheory.CechPic.pull (η[B] : 𝟙_ _ ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [← GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)]
    exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hL _)).2 hrig
  have h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp, hη, map_zero]
  have e₃ : GlobalTheory.CechPic.cls _ hd = 2 • GlobalTheory.CechPic.cls L hL := by
    refine (GlobalTheory.CechPic.cls_pull hP' _ _).trans ?_
    rw [e₀, GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd, GlobalTheory.SymRoot.lam_diag hL hΘ s₁, GlobalTheory.SymRoot.rigCls, h1, sub_zero]
  have f : IsFinite (𝟙 B : B ⟶ B).left := by rw [Over.id_left]; infer_instance
  have iso : LBIso (F.univ.diag.pull α) (lbPow L 2) :=
    (GlobalTheory.CechPic.cls_eq_iff hM0 (isLB_lbPow hL 2)).1 (eM0.trans (e₃.trans (cls_lbPow hL 2 _).symm))
  have hamp : Out.RelAmple B L :=
    (GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) L 2 two_pos hB hB hL f).2.1.1
      ((GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) _ 2 two_pos hB hB hM0 f).2.2.2 _ (isLB_lbPow hL 2) iso hamp0)
  exact ⟨hB, hamp, GlobalTheory.ThetaExtend.kTriv_of_lam hL hP' e₀ hn⟩

end GlobalTheory.SiegFibrePol
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (K : Type) [Field K] (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A y α → IsSquare α α₂ → ∀ L : LB B.left, L.IsLB → Rigidified B L → Out.Sym B L → LBIso (abelian₂ B L) (F.univ.P.pull α₂) → IsAbelianScheme B ∧ RelAmple B L ∧ KTriv B L := by
  atlas_forward_decl GlobalTheory.SiegFibrePol.polAV_of_lam_univ
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN R → IsCN V → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (W : Set (Sp R)), IsOpen W → (∀ y, PsiUnitOn D.toPre y W) → (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap ψ) β → IsAbelianScheme ((Over.pullback (jK V)).obj G') → Rigidified ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → Out.Sym ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → RelAmple ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → KTriv ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (ε : D'.toPre.X ≃+ D.toPre.X), LBIso (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) (U'.LG.L.pull (pullback.fst G'.hom (jK V))) ∧ ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  first | exact @GlobalTheory.UnifCoordPull.exists_unif_psiCoord | exact GlobalTheory.UnifCoordPull.exists_unif_psiCoord | (intros; apply GlobalTheory.UnifCoordPull.exists_unif_psiCoord <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_line_bundle_unif_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (L L' : LB ((Over.pullback (jK R)).obj G).left), L.IsLB → L'.IsLB → LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso L' (U'.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (abelian₂ ((Over.pullback (jK R)).obj G) L') → LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) := by
  first | exact @GlobalTheory.squares_iso_of_lam_generic | exact GlobalTheory.squares_iso_of_lam_generic | (intros; apply GlobalTheory.squares_iso_of_lam_generic <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unif_polarization_square_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ ε : D'.toPre.X ≃+ D.toPre.X, ∀ y r r', PsiCoord D.toPre (ε y) r → PsiCoord D'.toPre y r' → Associated (r ^ 2) (r' ^ 2) := by
  first | exact @GlobalTheory.SqUnifCoord.main | exact GlobalTheory.SqUnifCoord.main | (intros; apply GlobalTheory.SqUnifCoord.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLoc.TraitOrd

section Specialise

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S} [IsOpenImmersion j]
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}

theorem isSemiAbelian_of_isGrpPullback {T : Scheme.{0}} {f : T ⟶ S} {G' : Over T} [GrpObj G'] [IsCommMonObj G']
    {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

theorem exists_pull (hG : IsSemiAbelian G) (he : IsGrpPullback F.univ.A G j e) {R V : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (hR : IsCN R) (hV : IsCN V) (ψ : R →+* V) (hψ : IsLocalHom ψ)
    {ξ : Sp R ⟶ S} {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {π : G'.left ⟶ G.left} {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {U : Unif (maximalIdeal R) D A G'} (hU : IsUnifOf F j e ξ π U) (W : Set (Sp R))
    (hW : IsOpen W) (hψW : ∀ y, PsiUnitOn D.toPre y W)
    (hk : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W)
    (G'' : Over (Sp V)) [GrpObj G''] [IsCommMonObj G''] (π'' : G''.left ⟶ G.left) (ξ'' : Sp V ⟶ S) (hξ : ξ'' = spMap ψ ≫ ξ)
    (h'' : IsGrpPullback G'' G ξ'' π'') (y : Sp (FractionRing V) ⟶ F.X) (hy : y ≫ j = jK V ≫ ξ'')
    (α : ((Over.pullback (jK V)).obj G'').left ⟶ F.univ.A.left)
    (α₂ : (G2 ((Over.pullback (jK V)).obj G'')).left ⟶ (G2 F.univ.A).left)
    (hα : IsGrpPullback ((Over.pullback (jK V)).obj G'') F.univ.A y α) (hαe : α ≫ e = pullback.fst G''.hom (jK V) ≫ π'')
    (hα₂ : IsSquare α α₂) :
    ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'')
      (ε : D'.toPre.X ≃+ D.toPre.X) (L : LB ((Over.pullback (jK V)).obj G'').left), L.IsLB ∧
      LBIso L (U'.LG.L.pull (pullback.fst G''.hom (jK V))) ∧
      LBIso (abelian₂ ((Over.pullback (jK V)).obj G'') L) (F.univ.P.pull α₂) ∧
      ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  subst hξ
  have w : π'' ≫ G.hom = (G''.hom ≫ spMap ψ) ≫ ξ := by rw [Category.assoc]; exact h''.1.w
  obtain ⟨β, hβ₁, hβ₂⟩ : ∃ β : G''.left ⟶ G'.left, β ≫ π = π'' ∧ β ≫ G'.hom = G''.hom ≫ spMap ψ :=
    ⟨hU.1.1.lift _ _ w, hU.1.1.lift_fst _ _ _, hU.1.1.lift_snd _ _ _⟩
  have gβ : IsGrpPullback G'' G' (spMap ψ) β := hU.1.cancel (h''.congr rfl hβ₁.symm) hβ₂
  have gB := (isGrpPullback_pullback G'' (jK V)).comp gβ
  have hΛ := GlobalTheory.T.degeneration_data_normal_ring o ζ g n F S j G e he R hR.1 hR.2.1 _ ξ G' π D A U hU _ (jK V ≫ spMap ψ) y _ _ α α₂
    (hy.trans (Category.assoc _ _ _).symm) gB hα (by rw [hαe, Category.assoc, hβ₁]) hα₂
  obtain ⟨hr, hs⟩ := GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback _ _ _ G' _ _ gB U.LG U.symG U.symG_gen
  obtain ⟨ha, hamp, hkt⟩ := GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre o ζ g n F _ y _ α α₂ hα hα₂ _ (pull_isLB U.LG.isLB _) hr hs hΛ
  obtain ⟨D', A', U', ε, hL, hc⟩ := GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates R V hR hV ψ hψ G' (isSemiAbelian_of_isGrpPullback hU.1 hG) D A U W hW hψW hk
    G'' β gβ ha hr hs hamp hkt
  exact ⟨D', A', U', ε, _, pull_isLB U.LG.isLB _, hL, hΛ, hc⟩

theorem exists_generic (he : IsGrpPullback F.univ.A G j e) {V : Type} [CommRing V] [IsDomain V]
    (G'' : Over (Sp V)) [GrpObj G''] (π'' : G''.left ⟶ G.left) (ξ'' : Sp V ⟶ S)
    (h'' : IsGrpPullback G'' G ξ'' π'') (hr : Set.range (jK V ≫ ξ'') ⊆ Set.range j) :
    ∃ (y : Sp (FractionRing V) ⟶ F.X) (α : ((Over.pullback (jK V)).obj G'').left ⟶ F.univ.A.left)
      (α₂ : (G2 ((Over.pullback (jK V)).obj G'')).left ⟶ (G2 F.univ.A).left), y ≫ j = jK V ≫ ξ'' ∧
      IsGrpPullback ((Over.pullback (jK V)).obj G'') F.univ.A y α ∧ α ≫ e = pullback.fst G''.hom (jK V) ≫ π'' ∧
      IsSquare α α₂ := by
  have hy := IsOpenImmersion.lift_fac j (jK V ≫ ξ'') hr
  set y := IsOpenImmersion.lift j (jK V ≫ ξ'') hr
  have gB := ((isGrpPullback_pullback G'' (jK V)).comp h'').congr hy.symm rfl
  set B := (Over.pullback (jK V)).obj G''
  have w : (pullback.fst G''.hom (jK V) ≫ π'') ≫ G.hom = (B.hom ≫ y) ≫ j := by rw [Category.assoc]; exact gB.1.w
  obtain ⟨α, h₁, h₂⟩ : ∃ α : B.left ⟶ F.univ.A.left, α ≫ e = pullback.fst G''.hom (jK V) ≫ π'' ∧
      α ≫ F.univ.A.hom = B.hom ≫ y := ⟨he.1.lift _ _ w, he.1.lift_fst _ _ _, he.1.lift_snd _ _ _⟩
  refine ⟨y, α, pullback.map B.hom B.hom F.univ.A.hom F.univ.A.hom α α y h₂.symm h₂.symm, hy,
    he.cancel (gB.congr rfl h₁.symm) h₂, h₁, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem exists_compare (hG : IsSemiAbelian G) (he : IsGrpPullback F.univ.A G j e) {R₁ R₂ V : Type}
    [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂]
    [CommRing V] [IsDomain V] [IsLocalRing V] (hR₁ : IsCN R₁) (hR₂ : IsCN R₂) (hV : IsCN V)
    (ψ₁ : R₁ →+* V) (hψ₁ : IsLocalHom ψ₁) (ψ₂ : R₂ →+* V) (hψ₂ : IsLocalHom ψ₂)
    {ξ₁ : Sp R₁ ⟶ S} {G₁ : Over (Sp R₁)} [GrpObj G₁] [IsCommMonObj G₁] {π₁ : G₁.left ⟶ G.left}
    {D₁ : DegData R₁ (maximalIdeal R₁)} {A₁ : PolAV (Sp (FractionRing R₁))} {U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁}
    (hU₁ : IsUnifOf F j e ξ₁ π₁ U₁) (W₁ : Set (Sp R₁)) (hW₁ : IsOpen W₁) (hψW₁ : ∀ y, PsiUnitOn D₁.toPre y W₁)
    (hk₁ : (⟨RingHom.ker ψ₁, RingHom.ker_isPrime ψ₁⟩ : PrimeSpectrum R₁) ∈ W₁)
    {ξ₂ : Sp R₂ ⟶ S} {G₂ : Over (Sp R₂)} [GrpObj G₂] [IsCommMonObj G₂] {π₂ : G₂.left ⟶ G.left}
    {D₂ : DegData R₂ (maximalIdeal R₂)} {A₂ : PolAV (Sp (FractionRing R₂))} {U₂ : Unif (maximalIdeal R₂) D₂ A₂ G₂}
    (hU₂ : IsUnifOf F j e ξ₂ π₂ U₂) (W₂ : Set (Sp R₂)) (hW₂ : IsOpen W₂) (hψW₂ : ∀ y, PsiUnitOn D₂.toPre y W₂)
    (hk₂ : (⟨RingHom.ker ψ₂, RingHom.ker_isPrime ψ₂⟩ : PrimeSpectrum R₂) ∈ W₂)
    (hc : spMap ψ₁ ≫ ξ₁ = spMap ψ₂ ≫ ξ₂) (hr : Set.range (jK V ≫ spMap ψ₁ ≫ ξ₁) ⊆ Set.range j) :
    ∃ ε : D₁.toPre.X ≃+ D₂.toPre.X, ∀ y r₁ r₂, PsiCoord D₁.toPre y r₁ → PsiCoord D₂.toPre (ε y) r₂ →
      Associated (ψ₁ r₁ ^ 2) (ψ₂ r₂ ^ 2) := by
  let G'' := (Over.pullback (spMap ψ₁)).obj G₁
  have h'' := (isGrpPullback_pullback G₁ (spMap ψ₁)).comp hU₁.1
  obtain ⟨y, α, α₂, hy, hα, hαe, hα₂⟩ := exists_generic he G'' _ _ h'' hr
  obtain ⟨E₁, B₁, T₁, ε₁, L₁, l₁, i₁, m₁, c₁⟩ := exists_pull hG he hR₁ hV ψ₁ hψ₁ hU₁ W₁ hW₁ hψW₁ hk₁ G'' _ _ rfl h'' y hy
    α α₂ hα hαe hα₂
  obtain ⟨E₂, B₂, T₂, ε₂, L₂, l₂, i₂, m₂, c₂⟩ := exists_pull hG he hR₂ hV ψ₂ hψ₂ hU₂ W₂ hW₂ hψW₂ hk₂ G'' _ _ hc h'' y hy
    α α₂ hα hαe hα₂
  have hs := isSemiAbelian_of_isGrpPullback h'' hG
  have hΛ : LBIso (abelian₂ _ L₂) (abelian₂ _ L₁) :=
    LBIso.trans (DVR.linComb_isLB _ l₂ _ _) (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ l₁ _ _) m₂ m₁.symm
  obtain ⟨ε, hε⟩ := GlobalTheory.T.unif_polarization_square_iso V hV G'' hs E₂ E₁ B₂ B₁ T₂ T₁ (GlobalTheory.T.polarization_line_bundle_unif_iso V hV G'' hs E₂ E₁ B₂ B₁ T₂ T₁ L₂ L₁ l₂ l₁ i₂ i₁ hΛ)
  refine ⟨(ε₁.symm.trans ε).trans ε₂, fun z r₁ r₂ h₁ h₂ => ?_⟩
  obtain ⟨u₁, k₁⟩ := c₁ (ε₁.symm z) r₁ (by rwa [AddEquiv.apply_symm_apply])
  obtain ⟨u₂, k₂⟩ := c₂ (ε (ε₁.symm z)) r₂ h₂
  have := hε _ _ _ k₂ k₁
  rw [mul_pow, mul_pow] at this
  exact ((associated_unit_mul_left _ _ (u₁.isUnit.pow 2)).symm.trans this.symm).trans
    (associated_unit_mul_left _ _ (u₂.isUnit.pow 2))

end Specialise

theorem mul_evalZ_eq (φ : InvFun ℤ) {X X' : Type} [AddCommGroup X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Finite ℤ X']
    (ε : X ≃+ X') {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X'} (hγ : IsCone id φ γ) (n : ℕ) (be : LinearMap.BilinForm ℤ X)
    (hbe : ∀ y z, be y z = be z y) {r : ℕ} (hr : r ≠ 0) (w : Fin m → ℕ)
    (h : ∀ y, (r : ℤ) * be y y = ∑ i, (w i : ℤ) * (n * γ i (ε y) (ε y))) :
    r * φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((n : ℤ) • γ i) := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  let εZ : X ≃ₗ[ℤ] X' := ε.toIntLinearEquiv
  let B₂ : LinearMap.BilinForm ℤ X := ∑ i, ((w i : ℤ) * n) • (γ i).compl₁₂ εZ.toLinearMap εZ.toLinearMap
  have hB₂ : ∀ y z, B₂ y z = ∑ i, (w i : ℤ) * (n * γ i (ε y) (ε z)) := by
    intro y z
    simp [B₂, εZ, LinearMap.sum_apply, mul_assoc]
  have hfull : ∀ y z, (r : ℤ) * be y z = ∑ i, (w i : ℤ) * (n * γ i (ε y) (ε z)) := by
    intro y z
    have := GlobalTheory.GenFan.PhiOrder.eq_of_diag ((r : ℤ) • be) B₂ (fun y z => by simp [hbe y z])
      (fun y z => by rw [hB₂, hB₂]; exact Finset.sum_congr rfl fun i _ => by rw [(hγ.mem i).1])
      (fun y => by rw [hB₂, ← h y]; simp) y z
    rw [hB₂] at this
    simpa using this
  have hφbe : φ.evalZ be = ∑ i, ((w i : ℝ) / r) * φ.evalZ ((n : ℤ) • γ i) := by
    rw [← hγ.linearOn_smul n (fun i => (w i : ℝ) / r) (fun i => by positivity), ← φ.eval_equiv εZ]
    unfold InvFun.evalZ
    congr 1
    funext y z
    have h := congrArg (fun n : ℤ => (n : ℝ)) (hfull y z)
    push_cast at h
    rw [eq_comm, ← mul_right_inj' hr', Finset.mul_sum, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [εZ, LinearMap.smul_apply, smul_eq_mul, AddEquiv.coe_toIntLinearEquiv]
    push_cast
    field_simp
  rw [hφbe, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem eq_of_associated_pow {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (hϖ : Irreducible ϖ) {a b : ℕ}
    (h : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)

theorem isCN_of_cdvr {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (h : CDvr V) : IsCN V := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨inferInstance, inferInstance, h₂, h₃⟩

open GlobalTheory.TraitChartForm in

theorem isPhiDiv_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (φ φs : InvFun ℤ) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S) (h : BD.KeepsRegular π), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → AgreesPsd (Module.finrank ℚ E / 2 * (D.p + D.q)) φs φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → SiegData (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n F S s j G e BD d N → (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) → IsSiegPull s j G e κ C π → IsPhiDiv (comb 0 (resInt (𝓞 E) φs) d (resInt (𝓞 E) φs)) C (BD.pull π h) := by
  intro E _ _ _ H D l Xo c n R _ b ω φ φs F S s j _ G _ e BD d N κ C π h _ _ _ _ _ hag hded _ _ hS _ hP
  intro W _ _ _ hW ϖ hϖ χ t mχ P hr be hbe hmon
  obtain ⟨-, -, -, -, hG, -, he, -, -, hch, -⟩ := hS
  obtain ⟨A, _, _, bA, ξ, m, τ, A', _, _, _, ρ, r, G', _, _, π', Dg, B, U, γ, a, ⟨hAc, -, hx, hEt, hFU⟩, ⟨-, -, hj⟩,
    ⟨hA', hA0, hρ, hρf, -, hrt⟩, ⟨hU, hX, hγ, hmonC⟩, ha, hid⟩ := hch ((χ ≫ π) (closedPoint W))
  obtain ⟨_, hAi⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing A
  have hCN : IsCN A := ⟨inferInstance, hAi, hAc, RingHom.charZero ρ⟩
  have hCN' : IsCN A' := ⟨hA'.1, hA'.2.2.1, hA'.2.2.2, hA0⟩
  obtain ⟨V₀, _, _, _, f₀, ψ₀, hV₀, hf₀, hf₀l, hψ₀l, -, hc₀⟩ :=
    GlobalTheory.TraitLift.exists_lift S A ξ hCN hEt hFU W hW ϖ hϖ (χ ≫ π) hx.symm
  obtain ⟨V, _, _, _, f₁, ψ, hV, hf₁, hf₁l, hψl, hψ⟩ := GlobalTheory.T.exists_dvr_lift_finite_cover A A' ρ hρ hρf V₀ hV₀ ψ₀ hψ₀l
  obtain ⟨πP, hUP⟩ := GlobalTheory.T.siegel_pullback_dvr_extension E H D l Xo c _ n R ω F S s j G e κ C π hded hP W _ χ t mχ P hr
  let f := f₁.comp f₀
  have hf : Function.Injective f := hf₁.comp hf₀
  have hfl : IsLocalHom f := inferInstance
  have hc : spMap f ≫ χ ≫ π = spMap ψ ≫ spMap ρ ≫ ξ := by
    rw [spMap_comp, Category.assoc, hc₀, ← Category.assoc, ← spMap_comp, ← hψ, spMap_comp, Category.assoc]
  have := hW.1
  have := hV.1
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfϖ : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hf (h.trans (map_zero f).symm))
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ hϖ'
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact hϖ.not_isUnit (isUnit_of_map_unit f ϖ (hu ▸ u.isUnit))

  have hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective f hf)
  have hgen : (spMap f ≫ χ ≫ π) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ Set.range j := by
    obtain ⟨-, y, -, -, hy, -⟩ := hUP
    let p : Sp (FractionRing W) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))
    refine ⟨y p, ?_⟩
    rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply, jK_apply_eq_bot W p, ← hfbot]
    rfl
  have hrV : Set.range (jK V ≫ spMap f ≫ χ ≫ π) ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply, jK_apply_eq_bot V p]
    exact hgen
  have hτ : ∀ i, ψ (ρ (τ i)) = ψ (r i) ^ 2 := fun i => by rw [← hrt, map_pow]
  have hψr : ∀ i, ψ (r i) ≠ 0 := by
    rw [hc] at hgen
    have hp : ∏ i, τ i ∉ ((spMap ψ ≫ spMap ρ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)).asIdeal := (hj _).1 hgen
    have hp' : ψ (ρ (∏ i, τ i)) ≠ 0 := fun h => hp (by
      show ψ (ρ (∏ i, τ i)) ∈ (⊥ : Ideal V)
      rw [h]; exact Ideal.zero_mem _)
    rw [map_prod, map_prod] at hp'
    exact fun i h => Finset.prod_ne_zero_iff.1 hp' i (Finset.mem_univ i) (by rw [hτ, h]; simp)
  choose nn vv hvv using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hψr i) hϖ'

  obtain ⟨ε, hε⟩ := exists_compare hG he (isCN_of_cdvr hW) hCN' (isCN_of_cdvr hV) f hfl ψ hψl hUP
    {p | ϖ ∉ p.asIdeal} (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
    (fun y => hmon.psiUnitOn y fun p hp => by simpa using hp) (fun h => hfϖ (RingHom.mem_ker.1 h)) hU
    {p | ∏ i, r i ∉ p.asIdeal} (PrimeSpectrum.isOpen_basicOpen (a := ∏ i, r i))
    (fun y => hmonC.psiUnitOn y fun p hp => hp) (fun h => by
      have h' : ψ (∏ i, r i) = 0 := RingHom.mem_ker.1 h
      rw [map_prod] at h'
      exact Finset.prod_ne_zero_iff.2 (fun i _ => hψr i) h') hc hrV
  have hprod : ∀ x : Fin m → ℕ, Associated (∏ i, ψ (r i) ^ x i) (ϖ' ^ ∑ i, nn i * x i) := fun x => by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Associated.prod _ _ _ fun i _ => ?_
    rw [hvv, pow_mul]
    exact (associated_unit_mul_left _ _ (vv i).isUnit).pow_pow
  have hpow : ∀ x : ℕ, Associated (f ϖ ^ x) (ϖ' ^ (k * x)) := fun x => by
    rw [hu, pow_mul]
    exact (associated_unit_mul_left _ _ u.isUnit).pow_pow
  have hform : ∀ y, (k : ℤ) * be y y = ∑ i, ((2 * nn i : ℕ) : ℤ) * (n * γ i (ε y) (ε y)) := fun y => by
    obtain ⟨u₁, n₁, hn₁, c₁⟩ := hmon y
    obtain ⟨u₂, n₂, hn₂, c₂⟩ := hmonC (ε y)
    have a₁ : Associated (f (u₁ * ∏ i, ![ϖ] i ^ n₁ i)) (ϖ' ^ (k * n₁ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]
      exact (associated_unit_mul_left _ _ (u₁.isUnit.map f)).trans (hpow _)
    have a₂ : Associated (ψ (u₂ * ∏ i, r i ^ n₂ i)) (ϖ' ^ ∑ i, nn i * n₂ i) := by
      rw [map_mul, map_prod]
      simp_rw [map_pow]
      exact (associated_unit_mul_left _ _ (u₂.isUnit.map ψ)).trans (hprod _)
    have a₃ := (a₁.pow_pow (n := 2)).symm.trans ((hε y _ _ c₁ c₂).trans (a₂.pow_pow (n := 2)))
    rw [← pow_mul, ← pow_mul] at a₃
    have e₁ : k * n₁ 0 = ∑ i, nn i * n₂ i := by have := eq_of_associated_pow hϖ' a₃; omega
    have h0 : be y y = 2 * n₁ 0 := by simpa using hn₁ 0
    have h1 : ∀ i, (n : ℤ) * γ i (ε y) (ε y) = n₂ i := fun i => by
      have := hn₂ i
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      linarith
    simp_rw [h1]
    rw [h0]
    have e₂ := congrArg (fun x : ℕ => (x : ℤ)) e₁
    push_cast at e₂ ⊢
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← e₂]
    ring
  have hval := mul_evalZ_eq φ ε hγ n be hbe.1 hk _ hform

  have hmapf : (idlAlong BD.idealSheaf (χ ≫ π)).map f = Ideal.span {ϖ' ^ ∑ i, nn i * (2 * a i)} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hc, GlobalTheory.TraitOrder.idlAlong_comp, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span,
      Set.image_singleton, Ideal.map_span, Set.image_singleton, map_prod, map_prod]
    simp_rw [map_pow, hτ, ← pow_mul]
    exact Ideal.span_singleton_eq_span_singleton.2 (hprod _)
  have hne : idlAlong BD.idealSheaf (χ ≫ π) ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmapf
    exact pow_ne_zero _ hϖ'.ne_zero (Ideal.span_singleton_eq_bot.1 hmapf.symm)
  obtain ⟨n₀, hn₀⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hrN : k * n₀ = ∑ i, nn i * (2 * a i) := by
    rw [hn₀, Ideal.map_span, Set.image_singleton, map_pow] at hmapf
    exact eq_of_associated_pow hϖ' ((hpow _).symm.trans (Ideal.span_singleton_eq_span_singleton.1 hmapf))
  refine ⟨n₀, ?_, (GlobalTheory.PolOrdPull.idlAlong_pull BD π h χ).trans hn₀⟩
  have hres : (resInt (𝓞 E) φs).evalZ be = φs.evalZ be := by
    obtain ⟨q, x, hx⟩ := Module.Finite.exists_fin' (𝓞 E) P.D.toPre.X
    unfold InvFun.evalZ
    rw [InvFun.eval_eq _ hx]
    exact φs.eval_comp (r := x.restrictScalars ℤ) hx fun a b => (be a b : ℝ)
  have hagr : φs.evalZ be = φ.evalZ be := by
    rw [← evalR_toReal, ← evalR_toReal]
    refine hag _ (ε.toIntLinearEquiv.finrank_eq.trans_le hX) _
      (TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hbe.1) fun y => by simpa using hmon.nonneg 0 y)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [GlobalTheory.GenFan.PhiOrder.comb_evalZ, hres, hagr, ← mul_right_inj' hk', mul_left_comm, hval, Finset.mul_sum]
  have e₃ := congrArg (fun x : ℕ => (x : ℝ)) hrN
  push_cast at e₃ ⊢
  rw [e₃]
  exact Finset.sum_congr rfl fun i _ => by rw [ha]; ring

end GlobalTheory.SiegLoc.TraitOrd
end
end
