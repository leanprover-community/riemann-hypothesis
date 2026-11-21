import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormBaseChangeDvr

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef.BalancedTrait

theorem le_of_pow_dvd {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {m k : ℕ}
    (h : ϖ ^ m ∣ ϖ ^ k) : m ≤ k := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc⟩ := h
  have h0 : ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hm : ϖ ^ m = ϖ ^ k * ϖ ^ (m - k) := by rw [← pow_add]; congr 1; omega
  rw [hm, mul_assoc] at hc
  have h1 : ϖ ^ (m - k) * c = 1 := by
    have := mul_left_cancel₀ h0 (hc.symm.trans (mul_one _).symm)
    exact this
  have hu : IsUnit (ϖ ^ (m - k)) := ⟨⟨ϖ ^ (m - k), c, h1, (mul_comm _ _).trans h1⟩, rfl⟩
  exact hϖ.not_isUnit ((isUnit_pow_iff (by omega)).1 hu)

theorem pow_eq_of_associated {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {m k : ℕ}
    (h : Associated (ϖ ^ m) (ϖ ^ k)) : m = k :=
  le_antisymm (le_of_pow_dvd hϖ h.dvd) (le_of_pow_dvd hϖ h.symm.dvd)

theorem two_mul_apply {X : Type} [AddCommGroup X] (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y)
    (y z : X) : 2 * be y z = be (y + z) (y + z) - be y y - be z z := by
  simp only [map_add, LinearMap.add_apply, hs z y]
  ring

theorem smul_left {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {O : Type} [Ring O] [StarRing O]
    (Dg : DegPre R) [Module O Dg.X] (ρ : Dg.OAct O) {W : Type} [CommRing W] [IsDomain W] {ϖ : W}
    (hϖ : Irreducible ϖ) (f : R →+* W) (be : LinearMap.BilinForm ℤ Dg.X) (hs : ∀ y z, be y z = be z y)
    (hF : FormAt Dg f ϖ be) (x : O) (y z : Dg.X) : be (x • y) z = be y (star x • z) := by
  choose r n hr hn ha using hF
  obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance Dg ρ x y z (hr (x • y + z)) (hr (x • y)) (hr z)
    (hr (y + star x • z)) (hr y) (hr (star x • z))
  have hA : Associated (f (r (x • y + z)) * f (r y) * f (r (star x • z)))
      (f (r (y + star x • z)) * f (r (x • y)) * f (r z)) := by
    refine ⟨(Units.map f.toMonoidHom u), ?_⟩
    have := congrArg f hu
    simp only [map_mul] at this
    rw [← this]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  have hP : Associated (ϖ ^ (n (x • y + z) + n y + n (star x • z))) (ϖ ^ (n (y + star x • z) + n (x • y) + n z)) := by
    simp only [pow_add]
    exact (((ha _).symm.mul_mul (ha _).symm).mul_mul (ha _).symm).trans
      (hA.trans (((ha _).mul_mul (ha _)).mul_mul (ha _)))
  have he := pow_eq_of_associated hϖ hP
  have h1 := two_mul_apply be hs (x • y) z
  have h2 := two_mul_apply be hs y (star x • z)
  rw [hn, hn, hn] at h1
  rw [hn, hn, hn] at h2
  have he' : ((n (x • y + z) : ℤ) + n y + n (star x • z)) = (n (y + star x • z) : ℤ) + n (x • y) + n z := by
    exact_mod_cast he
  omega

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → 0 < N → IsPhiDiv (comb 0 φ N φ) Z EX → IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ConeZ E φs P.D.toPre.X m γ → InCone P.D.toPre γ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W) (be : LinearMap.BilinForm ℤ P.D.toPre.X), (∀ y z, be y z = be z y) → FormAt P.D.toPre f ϖ be → be ∈ balForms H.bar P.D.toPre.X := by
  intro E _ _ _ H D l Xo c Z g φs 𝒩 φ EX N R _ _ _ ξ t _ P m γ _ _ _ _ _ _ _ _ _ _ _ W _ _ _ _ ϖ hϖ f be hs hF
  letI := H.starRing
  exact ⟨hs, fun a y z => smul_left P.D.toPre P.oD hϖ f be hs hF a y z⟩

end GlobalTheory.TorRef.BalancedTrait
end
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ResLift

open ReciprocityTheory.ChartRestriction.G.Semi.Nb

theorem irreducible_adjoinRoot {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : V[X])
    (hf : f.Monic) (hg : Irreducible (f.map (residue V))) [IsDomain (AdjoinRoot f)] [IsLocalRing (AdjoinRoot f)]
    [IsDiscreteValuationRing (AdjoinRoot f)] {ϖ : V} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap V (AdjoinRoot f) ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, maxEq f hf hg, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton]

theorem exists_lift (n : ℕ) : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (k'' : Type) [Field k''] [Algebra (ResidueField V) k'']
    [FiniteDimensional (ResidueField V) k''], Module.finrank (ResidueField V) k'' = n →
    ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'')
      (_ : IsAdicComplete (maximalIdeal V'') V'') (_ : Algebra V V''),
      Module.Finite V V'' ∧ Function.Injective (algebraMap V V'') ∧
      (∀ ϖ : V, Irreducible ϖ → Irreducible (algebraMap V V'' ϖ)) ∧
      ∃ (_ : IsLocalHom (algebraMap V V'')) (e : k'' ≃+* ResidueField V''),
        e.toRingHom.comp (algebraMap (ResidueField V) k'') =
          ResidueField.map (algebraMap V V'') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V' _ _ _ _ k'' _ _ _ hn
  by_cases hs : Function.Surjective (algebraMap (ResidueField V') k'')
  · have hb : Function.Bijective (algebraMap (ResidueField V') k'') :=
      ⟨(algebraMap (ResidueField V') k'').injective, hs⟩
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, Algebra.id V',
      Module.Finite.self V', Function.injective_id, fun ϖ h => h, ?_, (RingEquiv.ofBijective _ hb).symm, ?_⟩
    · change IsLocalHom (RingHom.id V'); infer_instance
    · ext x
      change _ = ResidueField.map (RingHom.id V') x
      rw [ResidueField.map_id]
      exact (RingEquiv.ofBijective _ hb).symm_apply_apply x
  · obtain ⟨α, hα⟩ : ∃ α : k'', α ∉ Set.range (algebraMap (ResidueField V') k'') := by
      by_contra h
      push_neg at h
      exact hs h
    have hint : IsIntegral (ResidueField V') α := .of_finite (ResidueField V') α
    have hmon := minpoly.monic hint
    have hirr := minpoly.irreducible hint
    obtain ⟨f, hfg, hdeg, hf⟩ := exists_monic_lift (minpoly (ResidueField V') α) hmon
    have hg : Irreducible (f.map (residue V')) := hfg ▸ hirr
    have := isDomain f hf hg
    have := isLocal f hf hg
    have := dvr f hf hg
    have := complete f hf hg
    have := locHom f hf hg
    have := finite f hf
    have haev : Polynomial.aeval α (f.map (residue V')) = 0 := by
      rw [hfg]; exact minpoly.aeval _ α
    let ψ : AdjoinRoot (f.map (residue V')) →ₐ[ResidueField V'] k'' :=
      AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) α (by rwa [Polynomial.aeval_def] at haev)
    letI : Algebra (ResidueField (AdjoinRoot f)) k'' :=
      (ψ.toRingHom.comp (resEquiv f hf hg).toRingHom).toAlgebra
    have : Fact (Irreducible (f.map (residue V'))) := ⟨hg⟩
    letI : Algebra (AdjoinRoot (f.map (residue V'))) k'' := ψ.toRingHom.toAlgebra
    have : IsScalarTower (ResidueField V') (AdjoinRoot (f.map (residue V'))) k'' :=
      IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
    have hL : Module.finrank (ResidueField V') (AdjoinRoot (f.map (residue V'))) =
        (minpoly (ResidueField V') α).natDegree := by
      rw [(AdjoinRoot.powerBasis hg.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hfg]
    have hd1 : (minpoly (ResidueField V') α).natDegree ≠ 1 := fun h =>
      hα (minpoly.natDegree_eq_one_iff.1 h)
    have hd0 : 0 < (minpoly (ResidueField V') α).natDegree := minpoly.natDegree_pos hint
    have : FiniteDimensional (AdjoinRoot (f.map (residue V'))) k'' :=
      Module.Finite.of_restrictScalars_finite (ResidueField V') _ k''
    have hmul := Module.finrank_mul_finrank (ResidueField V') (AdjoinRoot (f.map (residue V'))) k''
    have hAL : Module.finrank (ResidueField (AdjoinRoot f)) k'' =
        Module.finrank (AdjoinRoot (f.map (residue V'))) k'' :=
      Algebra.finrank_eq_of_equiv_equiv (resEquiv f hf hg) (RingEquiv.refl k'') rfl
    have hpos : 0 < Module.finrank (AdjoinRoot (f.map (residue V'))) k'' := Module.finrank_pos
    have : FiniteDimensional (ResidueField (AdjoinRoot f)) k'' :=
      Module.finite_of_finrank_pos (hAL ▸ hpos)
    have hlt : Module.finrank (ResidueField (AdjoinRoot f)) k'' < n := by
      rw [hAL, ← hn, ← hmul, hL]
      calc Module.finrank (AdjoinRoot (f.map (residue V'))) k''
          < 2 * Module.finrank (AdjoinRoot (f.map (residue V'))) k'' := by omega
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨V'', i1, i2, i3, i4, i5, hfin, hinj, hirr'', hloc, e2, he2⟩ :=
      ih _ hlt (AdjoinRoot f) k'' rfl
    letI : Algebra V' V'' := ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f))).toAlgebra
    have : IsScalarTower V' (AdjoinRoot f) V'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hlc : IsLocalHom (algebraMap V' V'') := by
      change IsLocalHom ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f)))
      infer_instance
    refine ⟨V'', i1, i2, i3, i4, inferInstance, Module.Finite.trans (AdjoinRoot f) V'',
      hinj.comp (inj f hf hg), fun ϖ hϖ => hirr'' _ (irreducible_adjoinRoot f hf hg hϖ), hlc, e2, ?_⟩
    have h1 : (algebraMap (ResidueField (AdjoinRoot f)) k'').comp
        (ResidueField.map (algebraMap V' (AdjoinRoot f))) = algebraMap (ResidueField V') k'' := by
      change ψ.toRingHom.comp ((resEquiv f hf hg).toRingHom.comp
        (ResidueField.map (algebraMap V' (AdjoinRoot f)))) = _
      rw [resEquiv_comp f hf hg, ← AdjoinRoot.algebraMap_eq]
      exact ψ.comp_algebraMap
    change e2.toRingHom.comp (algebraMap (ResidueField V') k'') =
      ResidueField.map ((algebraMap (AdjoinRoot f) V'').comp (algebraMap V' (AdjoinRoot f)))
    rw [ResidueField.map_comp, ← h1, ← RingHom.comp_assoc, he2]

end GlobalTheory.ResLift

namespace GlobalTheory.TorRef

theorem exists_unif_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ → ∀ (t : SAB H (Sp V)), PolAt t (jK V) →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap f)), Nonempty (PELUnif (maximalIdeal V') t') := by
  intro E _ _ _ H V _ _ _ hV ϖ hϖ t hp
  obtain ⟨hd, hc, hz⟩ := (cDvr_iff V).1 hV
  let Ω := AlgebraicClosure (ResidueField V)
  obtain ⟨s, hs, h⟩ := GlobalTheory.Ex.UnifModel.exists_finite_split (algebraMap (ResidueField V) Ω) t.G t.semi
  have := hs.to_subtype
  let k'' := IntermediateField.adjoin (ResidueField V) s
  have : FiniteDimensional (ResidueField V) k'' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨W, _, _, _, hcW, _, -, hinj, hirr, hloc, e, he⟩ :=
    GlobalTheory.ResLift.exists_lift _ V k'' rfl
  have : IsLocalRing W := inferInstance
  have hzW : CharZero W := charZero_of_injective_algebraMap hinj
  let β : ResidueField W →+* Ω := k''.val.toRingHom.comp e.symm.toRingHom
  have hβ : β.comp (ResidueField.map (algebraMap V W)) = algebraMap (ResidueField V) Ω := by
    rw [← he]
    ext x
    simp [β]
  have hsp := h W (algebraMap V W) β hβ fun x hx =>
    ⟨e ⟨x, IntermediateField.subset_adjoin _ _ hx⟩, by simp [β]⟩
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W _).comp hinj
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  have hW : CDvr W := (cDvr_iff W).2 ⟨inferInstance, hcW, hzW⟩
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW _ hp' hsp
  exact ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, hW, hinj, hloc, hirr ϖ hϖ, _, m, ⟨P⟩⟩

end GlobalTheory.TorRef
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_uniformisation_polarisedTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ → ∀ (t : SAB H (Sp V)), PolAt t (jK V) →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap f)), Nonempty (PELUnif (maximalIdeal V') t') := by
  atlas_forward_decl GlobalTheory.TorRef.exists_unif_unram
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitQuot

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R → P.TorsionIso →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
    ∀ ψ : R →+* V, Function.Injective ψ → ¬ IsLocalHom ψ →
    ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap (f.comp ψ))) (P' : PELUnif (maximalIdeal V') t')
        (be' : LinearMap.BilinForm ℤ P'.D.toPre.X) (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
        be' ∈ levelForms H 1 P'.D.toPre.X ∧ Function.Surjective ρ ∧ (∀ a b, be' (ρ a) (ρ b) = be a b) ∧
        IsMonomial P'.D.toPre ![f ϖ] ![be'] := by
  intro E _ _ _ H R _ _ _ t P hR hT V _ _ _ hV ϖ hϖ ψ hψ hnl be hbe hF
  obtain ⟨PP', cub, sym, adj, prim, mV, -⟩ := sabPull CubePf.cubePull (spMap ψ) t
  have j : Function.Injective ((algebraMap V (FractionRing V)).comp ψ) := (IsFractionRing.injective V _).comp hψ
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift j
  have e : spMap gK ≫ jK R = jK V ≫ spMap ψ :=
    (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm
  have hp := GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap gK) e
  obtain ⟨V', _, _, _, f, hV', hf, hfl, hfϖ, t', m', ⟨P'⟩⟩ := GlobalTheory.T.exists_unramified_uniformisation_polarisedTriple E H V hV ϖ hϖ _ hp
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mV m'
  have hsp : spMap f ≫ spMap ψ = spMap (f.comp ψ) := GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl
  have n' : SABMap t' t (spMap (f.comp ψ)) := hsp ▸ n
  obtain ⟨ρ, hρs, hρ⟩ := GlobalTheory.T.boundary_form_base_change_dvr E H R t P hR hT V' hV' (f.comp ψ) (hf.comp hψ)
    (fun hl => hnl ⟨fun a ha => hl.map_nonunit a (ha.map f)⟩) t' n' P'
  obtain ⟨hd, hc, hz⟩ := hV'
  obtain ⟨be', hbe', hmon, -⟩ := exists_periodForm P' hfϖ
  refine ⟨V', inferInstance, inferInstance, inferInstance, f, ⟨hd, hc, hz⟩, hf, hfl, hfϖ, t', n', P', be', ρ, hbe',
    hρs, ?_, hmon⟩
  have hdiag : ∀ y, be' (ρ y) (ρ y) = be y y := by
    intro y
    obtain ⟨r, k, hr, hk, ha⟩ := hF y
    obtain ⟨u, m, hm, hc⟩ := hmon (ρ y)
    have h1 := hρ y r _ hr hc
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, RingHom.comp_apply] at h1
    have h2 : Associated ((f ϖ) ^ k) ((f ϖ) ^ (m 0)) := by
      have h3 : Associated (f (ψ r)) ((f ϖ) ^ k) := by
        rw [← map_pow]; exact ha.map f
      exact h3.symm.trans (h1.trans (associated_unit_mul_left _ _ u.isUnit))
    have h4 := BalancedTrait.pow_eq_of_associated hfϖ h2
    have h5 := hm 0
    simp only [Matrix.cons_val_zero] at h5
    rw [h5, hk, h4]
  intro a b
  have s1 := BalancedTrait.two_mul_apply be (mem_levelForms.1 hbe).1 a b
  have s2 := BalancedTrait.two_mul_apply be' (mem_levelForms.1 hbe').1 (ρ a) (ρ b)
  rw [← map_add, hdiag, hdiag, hdiag] at s2
  omega

end GlobalTheory.TraitQuot
end
end
