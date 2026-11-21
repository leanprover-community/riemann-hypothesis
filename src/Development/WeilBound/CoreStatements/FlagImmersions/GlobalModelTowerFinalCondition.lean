import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfParts
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CptFlatInputsOfPropZ
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlatHermHodgeCptConst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProved
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeCmTypeWeightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbeddingStatement
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NearRecordOfValue
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSystemSplitFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermRootLineDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonemptyCptOverOfFlatPreimmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentOpenStalksDomain
import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceB
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RingOfIntegersHomInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriodStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevel
import Development.WeilBound.CoreStatements.FlagImmersions.UnitAtOfSpan
import Development.WeilBound.CoreStatements.VolumeEquality.PrimeIdealOfFromSpec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueValuationRingLift
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHom
import Development.WeilBound.CoreStatements.FlagImmersions.MemGenFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasisStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsIntProj
import Development.WeilBound.CoreStatements.FlagImmersions.LocalCmpOf
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.NormEqOneOfValuationEqOne
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelic
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminant
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChange
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SqrtDiscriminantBoundsCmField
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_map_factorisation {X : Scheme.{0}} {A A' B B' : CommRingCat.{0}} (u : A ⟶ B) [IsIso u] (r : A ⟶ A') (v : A' ⟶ B')
    (a : Spec A ⟶ X) (a' : Spec A' ⟶ X) (x : Spec B ⟶ X) (x' : Spec B' ⟶ X) (e : Spec.map u ≫ a = x)
    (e' : Spec.map v ≫ a' = x') (e₂ : Spec.map r ≫ a = a') : Spec.map (inv u ≫ r ≫ v) ≫ x = x' := by
  subst e e' e₂
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc]

theorem exists_factor {X : Scheme.{0}} {Ω₀ Ω₁ : Type} [Field Ω₀] [Field Ω₁] {ξ₀ : Sp Ω₀ ⟶ X} (ξ₁ : Sp Ω₁ ⟶ X)
    (h₀ : IsCptGen ξ₀) (h : genPt ξ₁ ⤳ genPt ξ₀) : ∃ i : Ω₀ →+* Ω₁, spMap i ≫ ξ₀ = ξ₁ := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
  refine ⟨(inv (Scheme.stalkClosedPointTo ξ₀) ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ₁).hom, ?_⟩
  exact spec_map_factorisation (Scheme.stalkClosedPointTo ξ₀) (X.presheaf.stalkSpecializes h) (Scheme.stalkClosedPointTo ξ₁) _ _ ξ₀ ξ₁
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₁)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)

theorem genPt_spMap {X : Scheme.{0}} {Ω₀ Ω₁ : Type} [Field Ω₀] [Field Ω₁] (i : Ω₀ →+* Ω₁) (ξ : Sp Ω₀ ⟶ X) :
    genPt (spMap i ≫ ξ) = genPt ξ :=
  congrArg (fun x => ξ x) (Subsingleton.elim (α := PrimeSpectrum Ω₀) _ _)

theorem int_frac (F : Type) [Field F] [NumberField F] : Function.Injective (algebraMap (𝓞 F) F) ∧ IsNoetherianRing (𝓞 F) ∧
    ∀ x : F, ∃ a b : 𝓞 F, algebraMap (𝓞 F) F b ≠ 0 ∧ x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
  refine ⟨IsFractionRing.injective _ _, inferInstance, fun x => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, this, div_mul_cancel₀ _ this⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem isGeom_of {l : Level H} {Xo : Moduli D l} {c : Coeff l} [NumberField c.F]
    {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {M : Top.RootModel (CMType H) (D.p + D.q)}
    {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
    (o : RootOrigin Y S M Fx) {U : Set (Xo.XF c)} (Z : CptOver Y U)
    (h : genPt o.𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j)) : Z.IsGeom := by
  have e1 : genPt Fx.ξf = genPt (Z.ξ₀ ≫ Y.j) := by
    rw [← h, ← genPt_spMap o.g Fx.ξf, ← o.g_over, ← genPt_spMap o.𝔐.fn o.𝔐.ξ₀]
    exact congrArg genPt o.𝔐.fn_over
  obtain ⟨i, hi⟩ := exists_factor Fx.ξf Z.gen (e1 ▸ specializes_rfl)
  have hb : (o.g.comp i).comp Z.inc = o.𝔐.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (spMap_inj ?_)
    rw [← o.𝔐.cst_over, ← Category.assoc, o.g_over, ← hi, spMap_comp', spMap_comp', spMap_comp', ← Z.over_inc,
      ← Y.jQ_over]
    simp only [Model.j, Category.assoc, pullback.condition]
  rintro x ⟨f, hf, hx⟩
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  haveI : Algebra.IsAlgebraic ℤ c.F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
  have h0 : IsAlgebraic c.F x := ⟨f, hf, hx⟩
  have h1 : IsAlgebraic ℤ x := h0.restrictScalars ℤ
  obtain ⟨b, hb'⟩ := o.g_const (i x) (h1.algHom i.toIntAlgHom)
  refine ⟨b, (o.g.comp i).injective ?_⟩
  rw [← hb] at hb'
  exact hb'

theorem exists_norms (hG : Top.Given) (hFD : FlatDegree) (hP : PeriodOf) (hχ : ChiEx) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) [NumberField c.F] (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (U : Set ((Xo l).XF c)) (Z : CptOver Y U) (τ : CMType H) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hp : 1 ≤ D.p)
    (hq : 1 ≤ D.q) (hU : IsClopen U) (hUi : IsIrreducible U) (hZ : Z.IsGeom) :
    ∃ (φ : FrameFn (Xo l) c) (N : LogNorms c.F), FlatOnModel Z τ.1 φ ∧ (∀ s, HasInfNorm U τ.1 φ s (N.inf s)) ∧
      (∀ s, N.inf (ComplexEmbedding.conjugate s) = N.inf s) ∧ (∀ p κ, HasFinNorm U τ.1 φ p κ (N.fin p κ)) ∧
      N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 *
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H) := by
  obtain ⟨g, ty, FU, i, hty, hper⟩ := hP hG E H D l (Xo l) c Y U Z hp hq hU hUi hZ
  obtain ⟨⟨hI, -⟩, -, -, -, hRes, -, -, hGa, -⟩ := hG
  have hpq : 1 ≤ D.p + D.q := by omega
  obtain ⟨φ, hl, hf, -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGa E H D l (Xo l) c _ _ Y U Z τ.1 (int_frac c.F) hpq τ.2 hZ
  obtain ⟨hinf, hfg⟩ := GlobalTheory.T.flat_first_from_resolution_and_gaga hRes hGa E H D l (Xo l) c _ _ Y U Z τ.1 φ (int_frac c.F) hpq τ.2 hZ hl hf
  have hφ : IsFlatGen U τ.1 φ FU i := hfg g ty FU i hty fun P y hPer hu hy => (hper y hy).2 ⟨P, hPer, hu⟩
  obtain ⟨φ', N', hφ', hN', -⟩ := GlobalTheory.T.flat_theorem_of_resolution_gaga hRes hGa hI E H D Xo l c U τ.1 g ty FU i hpq τ.2 hg hty hU hUi hper
  obtain ⟨a, ha, he⟩ := GlobalTheory.T.flat_gen_frame_complex_compat E H D l (Xo l) c U τ.1 φ' φ g ty FU i hty hφ' hφ fun y hy hr => (hper y hy).1 hr
  have hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ.1 φ p κ t := fun p κ =>
    ⟨_, TopA.hasFinNorm_of_eq hl ha he (hN'.2 p κ)⟩
  choose t ht ht' using hinf
  choose tf htf using hfin
  let N : LogNorms c.F := ⟨fun s => t (InfinitePlace.mk s).embedding, tf⟩
  have hN : ∀ s, HasInfNorm U τ.1 φ s (N.inf s) := fun s => by
    show HasInfNorm U τ.1 φ s (t (InfinitePlace.mk s).embedding)
    rcases InfinitePlace.embedding_mk_eq s with h | h
    · rw [h]; exact ht s
    · rw [h]
      have e : (starRingEnd ℂ).comp (ComplexEmbedding.conjugate s) = s := by
        ext x; simp [ComplexEmbedding.conjugate_coe_eq]
      have := ht' (ComplexEmbedding.conjugate s)
      rwa [e] at this
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  obtain ⟨χ, hχ1, hχ2⟩ := hχ E H
  obtain ⟨h1, h2⟩ := GlobalTheory.T.kronecker_character_period_formula hFD E H D l (Xo l) c g ty FU i U τ.1 φ N χ hχ1 hty τ.2 hφ hN htf
  refine ⟨φ, N, hf, hN, fun s => ?_, htf, h1, by rw [h2, hχ2]⟩
  show t _ = t _
  rw [InfinitePlace.mk_conjugate_eq]

end RootFieldNumerics.RF
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem tauIn_injective {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : Function.Injective (tauIn c τ) := by
  intro a b hab
  have h : τ (a : E) = τ (b : E) := by
    have := congrArg (fun x : c.F => (x : ℂ)) hab
    simpa [tauIn] using this
  exact RingOfIntegers.ext (τ.injective h)

set_option maxHeartbeats 1600000 in
theorem core (hSm : SmoothLine) (hLc : LocalCmp) (hNu : Numerics) (hF : HT.FarguesHodgeTate) {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} [NumberField c.F] {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {U : Set (Xo.XF c)}
    (Z : CptOver Y U) (φ : FrameFn Xo c) (τ : CMType H) (N : LogNorms c.F) {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω)
    (hx : CMType H × Fin (D.p + D.q) → HermLine J) (n : ℕ) (hflat : FlatOnModel Z τ.1 φ)
    (hinf : ∀ s, HasInfNorm U τ.1 φ s (N.inf s)) (hconj : ∀ s, N.inf (ComplexEmbedding.conjugate s) = N.inf s)
    (hfin : ∀ p κ, HasFinNorm U τ.1 φ p κ (N.fin p κ)) (had : N.IsAdelic)
    (hNdeg : N.deg = ((D.p : ℝ) - D.q) / 2 *
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H))
    (hgp : genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j)) (hbir : Birational y) (hvar : IsArithVar (mCoordIdeal y) n)
    (hroot : Fl.RootLines xdeg e) (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hxa : ∀ r, (hx r).a = xdeg r)
    (h2S : 2 ∈ S) (hdS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) (hfree : ∀ p ∈ S, HT.HTFree 𝔐 p)
    (hpq : 0 < D.p + D.q)
    (hnum : ∀ p : ℕ, p.Prime → p ∉ S → ∀ (a : ⋀[Ω]^D.p 𝔐.Li) (b : ⋀[Ω]^D.q 𝔐.Li), a ≠ 0 → b ≠ 0 →
      (∃ x f, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b x f) →
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b) (p : Ω)) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (ψ : F' →+* Ω) (A : HermLine J) (Sf : FlatHerm y ψ A),
      OverInt y ψ ∧ IsSmoothHerm A ∧ A.a = ∑ i, xdeg (τ, i) ∧
      (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), w ∈ mcPts (mCoordIdeal y) → CoordsAt 𝔐.ξ y z w →
        𝔐.Interior z → A.h w = ∏ i, (hx (τ, i)).h w) ∧
      NearRecord (D.p + D.q) S (hostRd E) (hostLval H) Sf.ht := by
  obtain ⟨F', _, _, ι, ψ, hψ, hcl⟩ := CptInputs.exists_constants hbir 𝔐.cst
  haveI : Nonempty K := hvar.1
  have hN : NormalCpt 𝔐.ξ := XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  obtain ⟨hφ, a, b, hgen, hrep⟩ := id hflat
  obtain ⟨i, j, hT⟩ := GlobalTheory.T.hodge_component_matches_model_component E H D l Xo c Y U Z S Ω K J y 𝔐 hgp
  obtain ⟨a', b', d₁, d₂, h₁, h₂, ha0, hb0, ha', hb', ea, eb⟩ :=
    GlobalTheory.T.flag_cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 Fl τ i j a b hT hgen
  have hdeg := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl xdeg e τ hroot
  have he : ∏ i, e (τ, i) ≠ 0 := hdeg.1
  have hchar : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hfr : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a' b' p 1 := by
    intro p hp
    obtain ⟨⟨x₀, hx₀, ex⟩, hs₁, hs₂⟩ := GlobalTheory.T.cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j hT p hp
    obtain ⟨hv₁, hv₂, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c _ _ Y U Z τ.1 (int_frac c.F) τ.2
    obtain ⟨W₁, hW₁, u₁, -, hu₁⟩ := hv₁ x₀ hx₀
    obtain ⟨W₂, hW₂, u₂, -, hu₂⟩ := hv₂ x₀ hx₀
    exact GlobalTheory.T.exterior_coeff_base_change_compat _ _ _ _ _ _ 𝔐.f i _ _ j _ _ _ _ D.p D.q a b a' b' p x₀ u₁ u₂ Z.gen 𝔐.tie.gen hT.1 hT.2.2.1 ex
      (hu₁ x₀ hx₀ hW₁) (hu₂ x₀ hx₀ hW₂) hs₁ hs₂ (hgen.2.2 x₀ hx₀) ha' hb'
  let x₀ : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  have hx₀ : x₀ ∈ genFibre ℤ 𝔐.ξ := fun o ho =>
    ⟨by simpa using ho, CoordBase.mem_regAt_gen 𝔐.tie.gen _, CoordBase.mem_regAt_gen 𝔐.tie.gen _⟩
  have haF : exteriorPower.ιMulti Ω _ (Fl.b (.inl τ)) ≠ 0 := fun h => ha0 (by
    have e2 : d₁ • (exteriorPower.ιMulti Ω (labelRk D (.inl τ)) (Fl.b (.inl τ))) = 0 := by rw [h, smul_zero]
    exact ea.trans e2)
  have hbF : exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)) ≠ 0 := fun h => hb0 (by
    have e2 : d₂ • (exteriorPower.ιMulti Ω (labelRk D (.inr τ)) (Fl.b (.inr τ))) = 0 := by rw [h, smul_zero]
    exact eb.trans e2)
  have hVA : (𝔐.V (.inl τ)).IsVB (labelRk D (.inl τ)) _ := 𝔐.vb (.inl τ)
  have hVB : (𝔐.V (.inr τ)).IsVB (labelRk D (.inr τ)) _ := 𝔐.vb (.inr τ)
  have hco : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) p (d₁ / d₂)⁻¹ :=
    fun p hp => CptIn.isCoeffAt_of_smul h₁ h₂ ea eb (hfr p hp)
  obtain ⟨hL1, hL2, -⟩ := GlobalTheory.T.wedge_line_lattice_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.Li (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) _ _ _ _ Set.univ
    (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) hVA hVB haF hbF
    ⟨x₀, trivial, _, hco x₀ hx₀⟩
  have hd0 : d₁ / d₂ ≠ 0 := div_ne_zero h₁ h₂
  have hc₁ : (d₁ / d₂ / ∏ i, e (τ, i)) * ∏ i, e (τ, i) = d₁ / d₂ := div_mul_cancel₀ _ he
  have hgn : ∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p (d₁ / d₂) :=
    fun p hp => (hL2 p trivial _).2 ⟨hd0, hco p hp⟩
  have htriv : ∀ ℓ : ℕ, ℓ.Prime → TrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (ℓ : Ω) ∨
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (ℓ : Ω) := by
    intro ℓ hℓ
    by_cases hS : ℓ ∈ S
    · haveI : Fact ℓ.Prime := ⟨hℓ⟩
      refine Or.inl (GlobalTheory.T.wedge_line_lattice_trivial_mod 𝔐.X Ω 𝔐.ξ 𝔐.Li _ _ _ _ _ _ _ _ (ℓ : Ω) 𝔐.tie.gen (Nat.cast_ne_zero.2 hℓ.ne_zero)
        (fun q => ?_) hVA hVB haF hbF ⟨x₀, _, hco x₀ hx₀⟩
        (GlobalTheory.T.hodge_tate_free_cm_type_weight hF E H D l Xo c _ _ Y S Ω K J y 𝔐 ℓ hS hpq (hfree ℓ hS) τ))
      exact natCast_mem _ _
    · exact Or.inr (hnum ℓ hℓ hS _ _ haF hbF ⟨x₀, _, hco x₀ hx₀⟩)
  obtain ⟨r, hr⟩ := CptIn.exists_orders GlobalTheory.T.PropZ_proved ψ hcl 𝔐.all 𝔐.tie hN _ (d₁ / d₂) hL1 hgn htriv
  have hO : OverInt y ψ := overInt_of_normalCpt 𝔐.tie hN ψ
  obtain ⟨A, hAa, hAs, hAc, hAn, hAf⟩ := hSm 𝔐.X Ω 𝔐.ξ K J y F' ψ _ _ _ (d₁ / d₂ / ∏ i, e (τ, i))
    (fun σ => Real.exp (N.inf (σ.comp ι))) n 𝔐.all 𝔐.tie hN hO hbir hvar hdeg (by rw [hc₁]; exact hgn)
    (fun _ => Real.exp_pos _) (fun σ => congrArg Real.exp (hconj (σ.comp ι)))
  obtain ⟨-, Sf, hSf⟩ := exists_flatHerm_hodgeCpt_const E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl xdeg e τ F' ψ A
    (d₁ / d₂ / ∏ i, e (τ, i)) r (fun σ => Real.exp (N.inf (σ.comp ι))) hroot hAa hbir hAc (div_ne_zero hd0 he)
    (by rw [hc₁]; exact hgn) (by rw [hc₁]; exact hr) (fun _ => Real.exp_pos _) hAn
  refine ⟨F', inferInstance, inferInstance, ψ, A, Sf, hO, hAs, hAa, fun z w hw hz hint => ?_, ?_⟩
  · obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K J Ω F' y ψ hO w hw
    obtain ⟨g, h, dg, dh, hg, hh, hdg, hgh, hne⟩ := hAf w hw
    let A₀ : HermLine J := Top.combLine (fun i => hx (τ, i)) fun _ => 1
    have hA₀a : A₀.a = ∑ i, xdeg (τ, i) := by
      show ∑ i, (1 : ℤ) • (hx (τ, i)).a = _
      simp only [one_smul, hxa]
    have hA₀h : ∀ w', A₀.h w' = ∏ i, (hx (τ, i)).h w' := fun w' => by
      show ∏ i, (hx (τ, i)).h w' ^ (1 : ℤ) = _
      simp only [zpow_one]
    have hlies := GlobalTheory.T.point_over_number_field_value 𝔐.X Ω 𝔐.ξ K J y F' ψ σ z w hN 𝔐.tie hz hσ (𝔐.all _)
    have k1 := hAn σ w g h dg dh hσ hg hh (by rw [hAa]; exact hdg) hgh
    have k2 : ‖evC w g‖ = Real.exp (N.inf (σ.comp ι)) * A₀.h w * ‖evC w h‖ := by
      refine GlobalTheory.T.hermitian_norm_section_value 𝔐.X Ω 𝔐.ξ K J y z w A₀ (d₁ / d₂ / ∏ i, e (τ, i)) _ g h dg dh 𝔐.tie.gen hz ?_ hg hh
        (by rw [hA₀a]; exact hdg) hgh hne
      intro cc u hcc hu
      refine GlobalTheory.T.flag_weighted_degree_section E H D l Xo c Y S Ω K J y 𝔐 Fl xdeg e hx A₀ τ (N.inf (σ.comp ι)) (d₁ / d₂) z w hroot hhod hA₀a
        (fun w'' _ => hA₀h w'') hz hint hd0 ?_ cc u hcc (by rw [mul_comm, ← div_div]; exact hu)
      intro hc bp bq Γ Δ α κ u' h1 h2 h3 h4 h5 h6 h7 h8 h9
      refine GlobalTheory.T.cm_type_exterior_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j a b a' b' φ (σ.comp ι) _ z hc bp bq Γ Δ (d₁ * α) (d₂ * κ)
        u' hT hφ hgen hrep (hinf _) ha' hb' hint (fun a => ?_) h1 h2 h3 h4 h5 h6 ?_ ?_ ?_
      · rw [← hψ]
        exact hlies (ι a)
      · rw [mul_smul]
        exact ea.trans (congrArg (d₁ • ·) h7)
      · rw [mul_smul]
        exact eb.trans (congrArg (d₂ • ·) h8)
      · rw [← div_mul_div_comm, ← mul_div_assoc]
        exact h9
    rw [← hA₀h]
    exact mul_left_cancel₀ (Real.exp_pos _).ne' (mul_right_cancel₀ (norm_ne_zero_iff.2 hne) (k1.symm.trans k2))
  · rw [hSf]
    simp only [Real.log_exp]
    refine hNu E H D.p D.q c.F F' ι (tauIn c τ.1) N r S (tauIn_injective c τ.1) h2S 𝔐.S_prime had hNdeg ?_
    intro ℓ κ' v π hv hπ
    obtain ⟨m, k, hm, hk, hord⟩ := hr v π hπ
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hrv : (r v : ℝ) = (k : ℝ) / m := by
      have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
      have : (k : ℝ) = m * (r v : ℝ) := by exact_mod_cast hk
      rw [this]; field_simp
    obtain ⟨c1, c2⟩ := hLc E H D l Xo c Y U Z S Ω K J y 𝔐 Fl τ i j a b a' b' d₁ d₂ φ F' ι ψ ℓ κ' π m k _ hgp hT hφ hgen
      hrep ha' hb' h₁ h₂ ea eb ha0 hb0 hψ hπ0 hm (fun x hx => hord x fun u hu => hx u ((hv u).1 hu)) (hfin ℓ _)
    rw [hrv]
    refine ⟨fun hS => c1 hS fun hd => hS (hdS ℓ ℓ.2 hd), fun hS => ?_⟩
    obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c _ _ Y S Ω K J y 𝔐 ℓ hS hpq (hfree ℓ hS)
    exact c2 hS (hfree ℓ hS) κ hκ1 hκ2

end RootFieldNumerics.RF
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem sum_Iic_step {M : Type} [AddCommGroup M] {N : ℕ} (f : Fin N → M) (i : Fin N) :
    f i + -∑ k ∈ Finset.Iic i, f k =
      if h : 0 < (i : ℕ) then -∑ k ∈ Finset.Iic (⟨i - 1, by omega⟩ : Fin N), f k else 0 := by
  rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
  split_ifs with h
  · have : Finset.Iio i = Finset.Iic (⟨i - 1, by omega⟩ : Fin N) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
      omega
    rw [this]; abel
  · have : Finset.Iio i = ∅ := by
      ext k
      simp only [Finset.mem_Iio, Fin.lt_def, Finset.notMem_empty, iff_false]
      omega
    rw [this]; simp

theorem rootFlatOnHodge_of (h1 : CptEx) (h2 : PeriodOf) (h3 : SmoothLine) (h4 : LocalCmp) (h5 : ChiEx) (h6 : Numerics)
    (hFD : FlatDegree) (hG : Top.Given) : RootFlatOnHodge := by
  intro E _ _ _ _ H D Xo l c Y bad M Sys Fx o hY hp hq hbad hom τ
  classical
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨Yl, hg, hYl, -, -, hdom⟩ := hY
  obtain ⟨U, Z, hU, hUi, hgp⟩ := h1 E H D l (Xo l) c Y bad M.Ω M.K M.ι M.y o.𝔐
  obtain ⟨φ, N, k1, k2, k3, k4, k5, k6⟩ := exists_norms hG hFD h2 h5 Xo l c Y U Z τ hg hp hq hU hUi (isGeom_of o Z hgp)
  have hdS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ bad := fun p hp hd =>
    (hbad p).2 ⟨hp, (hd.mul_left 2).mul_right _⟩
  obtain ⟨-, -, -, -, -, -, hF, -, -, hIn, -⟩ := hG
  obtain ⟨F', _, _, ψ, A, Sf, hO, hAs, hAa, hAh, hnr⟩ := core h3 h4 h6 hF Z φ τ N o.𝔐 o.Fl M.xdeg o.e o.sing _ k1 k2 k3
    k4 k5 k6 hgp M.birational M.arith o.lines o.hodge o.sing_deg
    ((hbad 2).2 ⟨Nat.prime_two, by exact_mod_cast (dvd_mul_right (2 : ℤ) _).mul_right _⟩) hdS hom (by omega)
    (fun p hp hS => GlobalTheory.T.local_system_split_fibres E H D Xo Yl (fun p W hp hW i => ⟨((hYl p W hp hW).2 i).1, ((hYl p W hp hW).2 i).2.1⟩)
      l c hg Y hdom bad M.Ω M.K M.ι M.y o.𝔐 p hp hS (fun hd => hS (hdS p hp hd)) τ)
  let i₀ : Fin (D.p + D.q) := ⟨D.p + D.q - 1, by omega⟩
  have hi₀ : Finset.Iic i₀ = Finset.univ := by
    ext k
    simp only [Finset.mem_Iic, Fin.le_def, Finset.mem_univ, iff_true, i₀]
    omega
  obtain ⟨R, hR⟩ := GlobalTheory.T.flat_herm_root_line_degree hIn (CMType H) (D.p + D.q) M Sys o.Re τ i₀ F' ψ A Sf hO hAs
    (by show D.p + D.q - 1 + 1 = _; omega) (Sys.reg none).1 hAa (fun σ i => by
      rw [o.fund_deg, sum_Iic_step (fun k => M.xdeg (σ, k)) i]
      split_ifs with h
      · rw [o.fund_deg]
      · rfl) (fun t ht ht' σ i z hz => by
      have p1 := (M.x t (σ, i)).pos z hz.1
      have p2 := (o.Re.line (some (σ, i)) t).pos z hz.1
      have e := sum_Iic_step (fun k => Real.log ((M.x t (σ, k)).h z)) i
      rw [← o.fund_reg σ i t ht ht' z hz, ← Real.log_mul p1.ne' p2.ne'] at e
      split_ifs at e ⊢ with h
      · rw [← o.fund_reg σ _ t ht ht' z hz] at e
        exact Real.log_injOn_pos (mul_pos p1 p2) ((o.Re.line _ t).pos z hz.1) e
      · exact Real.log_injOn_pos (mul_pos p1 p2) (Set.mem_Ioi.2 one_pos) (e.trans Real.log_one.symm)) (fun x hx => by
      have hw : o.Re.R.lift x x ∈ mcPts (mCoordIdeal M.y) := o.Re.R.mem x x (o.Re.R.mem_U x)
      obtain ⟨z, -, hz⟩ := SheetDecomposition.ChartForm.exists_point o.𝔐.tie (o.Re.R.lift x x)
        (fun k => (hw.1 k).imp fun _ h => Ne.isUnit h) fun g hg => by
          have := hw.2 g hg
          rwa [MvPolynomial.eval_map] at this
      rw [o.fund_sing τ i₀ x hx, hi₀, hAh z _ hw hz ((o.interior x z hz).2 hx),
        Real.log_prod fun i _ => ((o.sing (τ, i)).pos _ hw.1).ne'])
  exact ⟨R, hR ▸ hnr⟩

end RootFieldNumerics.RF
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

private theorem noetherianSpace_projectiveSpectrum {A σ : Type} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] [IsNoetherianRing A] : TopologicalSpace.NoetherianSpace (ProjectiveSpectrum 𝒜) := by
  let f : ProjectiveSpectrum 𝒜 → PrimeSpectrum A := fun p => ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
  have hf : Topology.IsInducing f := by
    refine ⟨TopologicalSpace.ext_iff_isClosed.2 fun s => ?_⟩
    rw [isClosed_induced_iff, ProjectiveSpectrum.isClosed_iff_zeroLocus]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨PrimeSpectrum.zeroLocus t, PrimeSpectrum.isClosed_zeroLocus t, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).1 ht
      refine ⟨u, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  exact hf.noetherianSpace

theorem cptEx : CptEx := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐
  have hfr : ∀ x : ↥c.F, ∃ (a b : 𝓞 ↥c.F), (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 ∧ x * (algebraMap (𝓞 ↥c.F) ↥c.F) b = (algebraMap (𝓞 ↥c.F) ↥c.F) a := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥c.F) x
    have hb' : (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩
  have hinj : Function.Injective (algebraMap (𝓞 ↥c.F) ↥c.F) := IsFractionRing.injective _ _
  obtain ⟨hpre, hflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.spMap_flat_preimmersion (algebraMap (𝓞 ↥c.F) ↥c.F) hinj hfr
  obtain ⟨jpre, jflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.j_flat_preimmersion Y hinj hfr
  haveI := hpre
  haveI := jpre
  haveI := Y.jQ_open
  haveI : TopologicalSpace.NoetherianSpace Y.X := by
    obtain ⟨N, i, hi, -⟩ := Y.proj
    have : TopologicalSpace.NoetherianSpace (PSpace (𝓞 ↥c.F) N) := by
      unfold PSpace
      letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := 𝓞 ↥c.F)
      exact noetherianSpace_projectiveSpectrum _
    exact i.isClosedEmbedding.isInducing.noetherianSpace
  have hfx : 𝔐.f (genPt 𝔐.ξ) = genPt 𝔐.ξ₀ := GlobalTheory.CompanionTheory.Ar.Dominates.map_genPt 𝔐.fn_over
  have hsx : Y.s (genPt 𝔐.ξ₀) ∈ Set.range (spMap (algebraMap (𝓞 ↥c.F) ↥c.F)) := by
    refine ⟨spMap 𝔐.cst (IsLocalRing.closedPoint Ω), ?_⟩
    have h2 := congrArg (fun g => g (IsLocalRing.closedPoint Ω)) 𝔐.cst_over
    have h3 : spMap (𝔐.cst.comp (algebraMap (𝓞 ↥c.F) ↥c.F)) = spMap 𝔐.cst ≫ spMap (algebraMap (𝓞 ↥c.F) ↥c.F) := by
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [h3] at h2
    simp only [Scheme.Hom.comp_apply] at h2
    rw [← hfx]
    exact h2.symm
  have hsx2 : genPt 𝔐.ξ₀ ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))) := by
    rw [Scheme.Pullback.range_fst]
    exact hsx
  obtain ⟨x', hx'⟩ := hsx2
  have hgen : ∀ {p z : ↥Y.X}, genPt 𝔐.ξ₀ ⤳ p → z ⤳ p → genPt 𝔐.ξ₀ ⤳ z := fun hp hz =>
    GlobalTheory.CompanionTheory.Ar.Flat.genPt_specializes_of_specializes 𝔐.ξ₀ 𝔐.gen₀ hp hz
  have hopen : IsOpen (closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) := by
    refine GlobalTheory.CompanionTheory.Ar.Flat.isOpen_of_isClosed_of_generizing _ isClosed_closure ?_
    intro a b hab hb
    exact specializes_iff_mem_closure.1 (hgen (specializes_iff_mem_closure.2 hb) hab)
  have hV : IsOpen ((pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base ⁻¹' closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) :=
    hopen.preimage (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).continuous
  obtain ⟨q, hqV, u0, rfl⟩ := Y.jQ_dense.inter_open_nonempty _ hV
    ⟨x', by
      show (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base x' ∈ closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)
      rw [hx']
      exact subset_closure rfl⟩
  have hsp : x' ⤳ Y.jQ u0 := by
    rw [← (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).isEmbedding.isInducing.specializes_iff, hx']
    exact specializes_iff_mem_closure.2 hqV
  obtain ⟨u, hu⟩ := hsp.mem_open Y.jQ.isOpenEmbedding.isOpen_range ⟨u0, rfl⟩
  have hju : Y.j u = genPt 𝔐.ξ₀ := by
    show (Y.jQ ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base u = genPt 𝔐.ξ₀
    rw [Scheme.Hom.comp_apply, hu, hx']
  have hmin : ∀ z, z ⤳ u → z = u := by
    intro z hz
    have h1 : Y.j z ⤳ genPt 𝔐.ξ₀ := hju ▸ hz.map Y.j.continuous
    have h2 : genPt 𝔐.ξ₀ ⤳ Y.j z := hgen (specializes_refl _) h1
    exact Y.j.isEmbedding.injective ((h1.antisymm h2).eq.trans hju.symm)
  obtain ⟨U, hU, huU⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {u} isIrreducible_singleton
  obtain ⟨Z⟩ := GlobalTheory.CompanionTheory.Ar.Flat.nonempty_cptOver_of_fraction hinj hfr Y U hU
  have hZu : genPt Z.ξ₀ = u := hmin _ ((Z.closure u).1 (huU rfl))
  obtain ⟨U', hU', -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain E H D l Xo c (𝓞 ↥c.F) (algebraMap (𝓞 ↥c.F) ↥c.F) Y U Z
    ⟨hinj, inferInstance, hfr⟩
  refine ⟨U, Z, ⟨isClosed_of_mem_irreducibleComponents U hU, hU' ▸ U'.isOpen⟩, hU.1, ?_⟩
  have : genPt (Z.ξ₀ ≫ Y.j) = Y.j (genPt Z.ξ₀) := by
    unfold genPt
    exact Scheme.Hom.comp_apply _ _ _
  rw [this, hZu, hju]

end RootFieldNumerics.RF
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem chiEx : ChiEx := by
  intro E _ _ _ H _
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by
    have := H.d_mod
    omega
  refine ⟨(quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ), GlobalTheory.isKroneckerChar_quadraticChar h4, ?_⟩
  have hr : rootDiscr E = hostRd E := by
    simp [rootDiscr, hostRd, Int.cast_abs, one_div]
  have hpos : 0 < hostRd E := by
    unfold hostRd
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  simp only [GlobalTheory.CM.logOm, hostLval]
  rw [Complex.sub_re, Complex.ofReal_re, hr, Real.log_div (by positivity) hpos.ne']
  ring

end RootFieldNumerics.RF
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem range_sub_iff {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : Set X) : Set.range y ⊆ U ↔ centre y ∈ U := by
  refine ⟨fun h => h ⟨_, rfl⟩, ?_⟩
  rintro h _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact h

theorem mem_of_period {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hty : IsTypeFn H D.p D.q ty) (j : c.F →+* ℂ) {U : Set (Xo.XF c)} (hU : IsClopen U) (i : Fin F.n)
    {P P' : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    {x x' : Sp ℂ ⟶ Xo.XF c} (hx1 : x ≫ pullback.fst _ _ = F.u i P) (hx2 : x ≫ pullback.snd _ _ = spMap j)
    (hx1' : x' ≫ pullback.fst _ _ = F.u i P') (hx2' : x' ≫ pullback.snd _ _ = spMap j) (hx : centre x ∈ U) :
    centre x' ∈ U := by
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  by_contra hn
  let W : (Xo.XF c).Opens := ⟨U, hU.isOpen⟩
  let W' : (Xo.XF c).Opens := ⟨Uᶜ, hU.compl.isOpen⟩
  obtain ⟨t, -, ht, ht'⟩ := hBc.isPreconnected _ _ (hhol W 0).1 (hhol W' 0).1
    (fun t ht => by
      by_cases h : centre (y t) ∈ U
      · exact Or.inl ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W from h)⟩
      · exact Or.inr ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W' from h)⟩)
    ⟨b, hb, hb, GagaRat.top_le_of_centre_mem (show centre (y b) ∈ W from e ▸ hx)⟩
    ⟨b', hb', hb', GagaRat.top_le_of_centre_mem (show centre (y b') ∈ W' from e' ▸ hn)⟩
  exact (GagaRat.centre_mem ht'.2 : centre (y t) ∈ W') (GagaRat.centre_mem ht.2 : centre (y t) ∈ W)

theorem over_const [NumberField c.F] {m : ℕ} {T : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.XF c)}
    (hTc : IsPreconnected T) (hy : IsHolTo T y) {b b' : Fin m → ℂ} (hb : b ∈ T) (hb' : b' ∈ T) :
    y b ≫ pullback.snd _ _ = y b' ≫ pullback.snd _ _ := by
  have hemb : ∀ p : Sp ℂ ⟶ Xo.XF c, ∃ κ : c.F →+* ℂ, p ≫ pullback.snd _ _ = spMap κ := fun p =>
    ⟨(Spec.preimage (p ≫ pullback.snd _ _)).hom, by
      unfold spMap
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  choose κ hκy using fun b => hemb (y b)
  have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T := fun r => by
    have h3 := (GagaRat.isHolTo_comp (pullback.snd _ _) hy ⊤ ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv (r : c.F))).2
    have hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ pullback.snd _ _) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (r : c.F) = valAt' (y b ≫ pullback.snd _ _) ⊤ _
    rw [hκy b]
    exact (PullbackSections.valAt'_spMap (κ b) (r : c.F)).symm
  rw [hκy, hκy, GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected hTc κ hd hb hb']

theorem periodOf : PeriodOf := by
  intro hG E _ _ _ H D l Xo c _ Y U Z hp hq hU _ hgeom
  classical
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := hN E H D l Xo (algebraMap (KA l) ℂ) g ty (by omega) rfl hty
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hsm : SmoothOfRelativeDimension D.dim s :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D.dim).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have hsm' : Smooth s := SmoothOfRelativeDimension.smooth D.dim s
  haveI := Y.jQ_open
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  haveI : IsPreimmersion Y.j := by
    show IsPreimmersion (Y.jQ ≫ pullback.fst _ _)
    infer_instance
  have hξ : IsCptGen Z.ξ₀ := GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ Y.j s hsm' rfl Z.gen (Y.j.stalkMap_surjective _)
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  have hcl : ConstClosed c.F Z.Ω := by
    rintro a ⟨f, hf, hfa⟩
    obtain ⟨x, hx⟩ := hgeom a ⟨f, hf, hfa⟩
    exact ⟨x, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx.symm⟩
  have hover : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ s = spMap (algebraMap c.F ℂ) →
      under x ≫ Xo.s = spMap (algebraMap (KA l) ℂ) := by
    intro x hx
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [hx]
    exact GagaRat.spMap_comp _ _
  have hexF : ∀ x : Sp ℂ ⟶ Xo.XF c, ∃ r : ℂ, (x ≫ s ≠ spMap (algebraMap c.F ℂ) → r = 0) ∧
      (x ≫ s = spMap (algebraMap c.F ℂ) → ∀ k P, IsPeriod (FU.Di k) ty P → FU.u k P = under x → r = ((k : ℕ) : ℂ)) := by
    intro x
    by_cases hx : x ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover x hx)
      exact ⟨((k : ℕ) : ℂ), fun h => absurd hx h, fun _ k' P' hP' e' => by rw [FU.disj k k' P P' hP hP' (e.trans e'.symm)]⟩
    · exact ⟨0, fun _ => rfl, fun h => absurd h hx⟩
  choose F hF0 hF using hexF
  have hconst := SheetDecomposition.One.const_of_hol (algebraMap c.F ℂ) s Z.ξ₀ ⊤ F D.dim hsm Z.over_inc hξ hcl (by
    intro m T y hT hc hy _ b₁ hb₁ b₂ hb₂
    have hall : ∀ b ∈ T, y b ≫ s = y b₁ ≫ s := fun b hb => over_const hc hy hb hb₁
    by_cases h : y b₁ ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨i, hi⟩ := GlobalTheory.T.family_uniformisation_local_period E H D l Xo _ g ty FU m T (fun b => under (y b)) hT hc ⟨b₁, hb₁⟩
        (fun b hb => hover _ ((hall b hb).trans h)) (GagaRat.isHolTo_comp _ hy)
      have key : ∀ b ∈ T, F (y b) = ((i : ℕ) : ℂ) := fun b hb => by
        obtain ⟨B', P, -, m1, -, hP, e⟩ := hi b hb
        exact hF _ ((hall b hb).trans h) i (P b) (hP.1 b m1) (e b m1)
      rw [key b₁ hb₁, key b₂ hb₂]
    · rw [hF0 _ h, hF0 _ (by rw [hall b₂ hb₂]; exact h)])
  obtain ⟨x, hx, hxU⟩ := SheetDecomposition.One.exists_point (algebraMap c.F ℂ) s ⟨U, hU.isOpen⟩ (q := genPt Z.ξ₀) Z.genPt_mem
  have hxU' : centre x ∈ U := GagaRat.centre_mem hxU
  obtain ⟨i, P₀, hP₀, e₀⟩ := FU.onto _ (hover x hx)
  refine ⟨g, ty, FU, i, hty, fun y hy => ?_⟩
  rw [range_sub_iff]
  constructor
  · intro hyU
    obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover y hy)
    have := hconst y x hy hx le_top le_top ((Z.closure _).1 hyU) ((Z.closure _).1 hxU')
    rw [hF _ hy k P hP e, hF _ hx i P₀ hP₀ e₀] at this
    obtain rfl : k = i := Fin.ext (Nat.cast_injective this)
    exact ⟨P, hP, e.symm⟩
  · rintro ⟨P, hP, e⟩
    exact mem_of_period FU hty _ hU i hP₀ hP e₀.symm hx e hy hxU'

end RootFieldNumerics.RF
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

namespace Pt

theorem numberField_of (L : Type) [Field L] (f : ℚ →+* L) (hf : f.FiniteType) : NumberField L := by
  haveI : CharZero L := charZero_of_injective_ringHom f.injective
  have e : f = algebraMap ℚ L := Subsingleton.elim _ _
  haveI : Algebra.FiniteType ℚ L := RingHom.finiteType_algebraMap.1 (e ▸ hf)
  exact { to_finiteDimensional := finite_of_finite_type_of_isJacobsonRing ℚ L }

theorem exists_quot (B : Type) [CommRing B] [Nontrivial B] [Algebra ℚ B] [Algebra.FiniteType ℚ B] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L), Nonempty (B →+* L) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  have h1 : (algebraMap ℚ B).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  haveI : NumberField (B ⧸ m) := numberField_of _ ((Ideal.Quotient.mk m).comp (algebraMap ℚ B))
    (RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) h1)
  exact ⟨B ⧸ m, inferInstance, inferInstance, ⟨Ideal.Quotient.mk m⟩⟩

theorem exists_numberField {A Ω κ : Type} [CommRing A] [Field Ω] [CharZero Ω] [Finite κ] (e : A →+* Ω) (t : κ → Ω)
    (he : ∀ a, e a ∈ Algebra.adjoin ℤ (Set.range t)) (s : A) (hs : e s ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ε : A →+* L), ε s ≠ 0 := by
  classical
  let B : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (e s)⁻¹ (Set.range t))
  have hB : ∀ x ∈ Algebra.adjoin ℤ (Set.range t), x ∈ B := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
    | algebraMap r => simpa using intCast_mem B r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  haveI : Algebra.FiniteType ℚ B := by
    refine (Subalgebra.fg_iff_finiteType _).1 ⟨((Set.finite_range t).insert (e s)⁻¹).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset]
  obtain ⟨L, _, _, ⟨g⟩⟩ := exists_quot B
  let e' : A →+* B := e.codRestrict B fun a => hB _ (he a)
  refine ⟨L, inferInstance, inferInstance, g.comp e', ?_⟩
  have h1 : e' s * ⟨(e s)⁻¹, Algebra.subset_adjoin (Set.mem_insert _ _)⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hs)
  exact ((IsUnit.of_mul_eq_one _ h1).map g).ne_zero

theorem exists_point {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    [Finite κ] {x : κ → Ω} (hT : CoordTie ℤ ξ x) (W : X.Opens) (hW : genPt ξ ∈ W) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (z : Spec (CommRingCat.of L) ⟶ X), centre z ∈ W := by
  obtain ⟨c, hc⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨U, hU, hg, -, -, hr⟩ := SheetDecomposition.BBase.chart hT c hc.1
  obtain ⟨s, hsW, hsη⟩ := hU.exists_basicOpen_le (V := W) ⟨genPt ξ, hW⟩ hg
  have h0 : SheetDecomposition.BBase.ev ξ U hg s ≠ 0 :=
    (((Scheme.mem_basicOpen X s _ hg).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  obtain ⟨L, _, _, ε, hε⟩ := exists_numberField (SheetDecomposition.BBase.ev ξ U hg) _ (fun a => (hr _).1 ⟨a, rfl⟩) s h0
  let φ : Γ(X, U) ⟶ CommRingCat.of L := CommRingCat.ofHom ε
  have hz : centre (Spec.map φ ≫ hU.fromSpec) ∈ U := by
    change _ ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨L, inferInstance, inferInstance, Spec.map φ ≫ hU.fromSpec, hsW ?_⟩
  have h1 := congrArg (fun g => g.hom s) (SheetDecomposition.ChartForm.germ_point hU φ hz)
  refine (Scheme.mem_basicOpen X s _ hz).2
    (isUnit_of_map_unit (Scheme.stalkClosedPointTo (Spec.map φ ≫ hU.fromSpec)).hom _ (IsUnit.mk0 _ ?_))
  intro h
  exact hε (h1.symm.trans h)

def primeOf {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) : Ideal (𝓞 F) :=
  { carrier := {b | ‖κ (b : F)‖ < 1}
    add_mem' := fun {a b} ha hb => by
      have := IsUltrametricDist.norm_add_le_max (κ (a : F)) (κ (b : F))
      show ‖κ ((a + b : 𝓞 F) : F)‖ < 1
      push_cast
      rw [map_add]
      exact this.trans_lt (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' := fun a b hb => by
      show ‖κ ((a * b : 𝓞 F) : F)‖ < 1
      have h1 : ‖κ (a : F)‖ ≤ 1 := by
        have := HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) κ a
        exact_mod_cast this
      push_cast
      rw [map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans_lt hb }

theorem norm_int_le {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) (a : 𝓞 F) :
    ‖κ (a : F)‖ ≤ 1 := by
  have := HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) κ a
  exact_mod_cast this

theorem norm_eq_one {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) {a : 𝓞 F}
    (h : a ∉ primeOf κ) : ‖κ (a : F)‖ = 1 := le_antisymm (norm_int_le κ a) (not_lt.1 h)

instance primeOf_isPrime {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) : (primeOf κ).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    show ¬ ‖κ ((1 : 𝓞 F) : F)‖ < 1
    simp
  mem_or_mem' := fun {a b} h => by
    by_contra hn
    rw [not_or] at hn
    have h' : ‖κ ((a * b : 𝓞 F) : F)‖ < 1 := h
    push_cast at h'
    rw [map_mul, norm_mul, norm_eq_one κ hn.1, norm_eq_one κ hn.2] at h'
    simp at h'

theorem primeOf_ne_bot {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) : primeOf κ ≠ ⊥ := by
  intro h
  have h1 : ((p : ℕ) : 𝓞 F) ∈ primeOf κ := by
    show ‖κ (((p : ℕ) : 𝓞 F) : F)‖ < 1
    have : κ (((p : ℕ) : 𝓞 F) : F) = algebraMap ℚ_[p] ℂ_[p] ((p : ℕ) : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rw [h, Ideal.mem_bot] at h1
  exact p.2.ne_zero (by exact_mod_cast h1)

theorem exists_frac {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) {a : F} (ha : ‖κ a‖ ≤ 1) :
    ∃ u s : 𝓞 F, s ∉ primeOf κ ∧ a = (u : F) * (s : F)⁻¹ := by
  let V := Localization.subalgebra.ofField F (primeOf κ).primeCompl (primeOf κ).primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) (primeOf_ne_bot κ) V
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨x, hx⟩ | ⟨x, hx⟩
  · obtain ⟨u, s, hs, e⟩ := x.2
    exact ⟨u, s, hs, hx.symm.trans e⟩
  · obtain ⟨u, s, hs, e⟩ := x.2
    have e' : a⁻¹ = (u : F) * (s : F)⁻¹ := hx.symm.trans e
    by_cases h0 : a = 0
    · exact ⟨0, 1, (primeOf κ).primeCompl.one_mem, by simp [h0]⟩
    refine ⟨s, u, fun hu => ?_, ?_⟩
    · have h1 : ‖κ (u : F)‖ < 1 := hu
      have h2 := congrArg (fun t => ‖κ t‖) e'
      simp only [map_inv₀, map_mul, norm_mul, norm_inv, norm_eq_one κ hs, inv_one, mul_one] at h2
      have h3 : 0 < ‖κ a‖ := norm_pos_iff.2 ((map_ne_zero κ).2 h0)
      have := one_le_inv₀ h3 |>.2 ha
      linarith
    · rw [← inv_inv a, e', mul_inv, inv_inv, mul_comm]

theorem exists_dvr {L : Type} [Field L] [NumberField L] {p : Nat.Primes} (j : L →+* ℂ_[p]) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra V L)
      (_ : IsFractionRing V L), ∀ a : L, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V L).range := by
  let V := Localization.subalgebra.ofField L (primeOf j).primeCompl (primeOf j).primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) (primeOf_ne_bot j) V
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨u, s, hs, e⟩ := exists_frac j ha
    exact ⟨⟨a, u, s, hs, e⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨u, s, hs, e⟩ := x.2
    have e' : algebraMap V L x = (u : L) * (s : L)⁻¹ := e
    rw [e', map_mul, map_inv₀, norm_mul, norm_inv, norm_eq_one j hs, inv_one, mul_one]
    exact norm_int_le j u

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem normalCpt_of_tie {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x)
    (hX : ∀ q : X, IsDomain (X.presheaf.stalk q) ∧ IsIntegrallyClosed (X.presheaf.stalk q)) : NormalCpt ξ := by
  intro p a ha
  have hξ := hT.gen
  obtain ⟨hd, hc⟩ := hX p.1
  letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk p.1) Ω) := hξ.inj p
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨c, hc⟩ := hT.cover p
    obtain ⟨U, hU, hg, hm, -, -⟩ := SheetDecomposition.BBase.chart hT c hc.1
    have hp : p.1 ∈ U := (hm _).2 ⟨p.2, hc⟩
    obtain ⟨s, t, ht, e⟩ := SheetDecomposition.BBase.exists_frac hU ⟨genPt ξ, specializes_rfl⟩ hg hg (SheetDecomposition.BBase.mem_regAt_gen hξ z)
    have h0 := ((SheetDecomposition.BBase.unitAt_ev_iff hξ hU ⟨genPt ξ, specializes_rfl⟩ hg hg t).2 ht).1
    refine ⟨X.presheaf.germ U p.1 hp s, X.presheaf.germ U p.1 hp t, ?_⟩
    show z = genMap ξ p _ / genMap ξ p _
    rw [SheetDecomposition.BBase.genMap_germ p U hp hg, SheetDecomposition.BBase.genMap_germ p U hp hg, ← e, mul_div_cancel_left₀ _ h0]
  letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
    Algebra.IsIntegral.of_surjective (R := X.presheaf.stalk p.1) (A := X.presheaf.stalk p.1)
      (Algebra.ofId _ _) (genMap ξ p).rangeRestrict_surjective
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk p.1) (K := Ω)).1
    (isIntegral_trans (R := X.presheaf.stalk p.1) (A := regAt ξ p) a ha)
  exact ⟨b, hb⟩

theorem int_reg (hN : NormalCpt ξ) {F : Type} [Field F] [NumberField F] (ψ : F →+* Ω) (q : Cpt ξ) (b : 𝓞 F) :
    ψ (b : F) ∈ regAt ξ q := hN q _ ((map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe b)).tower_top)

theorem inv_reg {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z)
    {a : Ω} {r : R} (hv : ValAt ξ z a r) (hr : IsUnit r) : a⁻¹ ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨h', g, rfl, rfl⟩ := hv
  obtain ⟨u, rfl⟩ : IsUnit g :=
    (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit g hr
  exact ⟨u⁻¹.val, map_units_inv _ u⟩

theorem exists_const (hξ : IsCptGen ξ) (hN : NormalCpt ξ) {F : Type} [Field F] [NumberField F] (ψ : F →+* Ω)
    {L : Type} [Field L] [CharZero L] (z : Spec (CommRingCat.of L) ⟶ X) (h : genPt ξ ⤳ centre z) :
    ∃ ψL : F →+* L, ∀ a, ValAt ξ z (ψ a) (ψL a) := by
  have hreg : ∀ a, ψ a ∈ regAt ξ ⟨centre z, h⟩ := by
    intro a
    have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
    haveI : CharZero Ω := charZero_of_injective_ringHom ψ.injective
    have h1 := int_reg hN ψ ⟨centre z, h⟩ ⟨n • a, hi⟩
    have h2 : ValAt ξ z (n : Ω) (n : L) := ⟨h, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩
    have h3 := inv_reg h h2 (IsUnit.mk0 _ (by exact_mod_cast hn))
    have e : ψ a = (n : Ω)⁻¹ * ψ (n • a) := by
      rw [zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ (by exact_mod_cast hn)]
    rw [e]
    exact mul_mem h3 h1
  let e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩ :=
    RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict
      ⟨fun a b hab => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val hab), (genMap ξ ⟨centre z, h⟩).rangeRestrict_surjective⟩
  refine ⟨(Scheme.stalkClosedPointTo z).hom.comp (e.symm.toRingHom.comp (ψ.codRestrict _ hreg)), fun a =>
    ⟨h, e.symm ⟨ψ a, hreg a⟩, congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hreg a⟩), rfl⟩⟩

theorem val_unique (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨_, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]

end Val

theorem exists_lift_genFibre {F L : Type} [Field F] [NumberField F] [Field L] [CharZero L] {W : Scheme.{0}}
    (s : W ⟶ Spec (CommRingCat.of (𝓞 F))) (z : Spec (CommRingCat.of L) ⟶ W) :
    ∃ u : Spec (CommRingCat.of L) ⟶ pullback s (spMap (algebraMap (𝓞 F) F)), u ≫ pullback.fst _ _ = z := by
  let r : 𝓞 F →+* L := (Spec.preimage (z ≫ s)).hom
  have hr : z ≫ s = spMap r := by
    simp [r, spMap]
  have hinj : Function.Injective r := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro n hn
    have h0 : r (algebraMap ℤ (𝓞 F) n) = 0 := hn
    have : (n : L) = 0 := by simpa using h0
    simpa using this
  have hr' : (IsFractionRing.lift (K := F) hinj : F →+* L).comp (algebraMap (𝓞 F) F) = r :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) hinj a
  refine ⟨pullback.lift z (spMap (IsFractionRing.lift (K := F) hinj)) ?_, pullback.lift_fst _ _ _⟩
  rw [hr]
  conv_lhs => rw [← hr']
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end Pt

open Pt in
theorem pointEx : PointEx := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 F' _ _ ψ p κ' hgen
  classical
  haveI : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hN : NormalCpt 𝔐.ξ := normalCpt_of_tie 𝔐.tie 𝔐.normal
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  have hind : Topology.IsInducing (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.isInducing
  have hopen : IsOpen (Set.range Y.jQ) := by
    haveI := Y.jQ_open
    exact Y.jQ.isOpenEmbedding.isOpen_range
  obtain ⟨C, hC, hCe⟩ := hind.isClosed_iff.1 hopen.isClosed_compl
  let W : 𝔐.X.Opens := ⟨(𝔐.f ⁻¹' C)ᶜ, (hC.preimage 𝔐.f.continuous).isOpen_compl⟩
  have hW : genPt 𝔐.ξ ∈ W := by
    change 𝔐.f (genPt 𝔐.ξ) ∉ C
    rw [CptIn.Intr.genPt_dominates 𝔐.fn_over, hgen]
    have h1 : genPt (Z.ξ₀ ≫ Y.j) = pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) (Y.jQ (genPt Z.ξ₀)) := by
      simp [genPt, Model.j, Scheme.Hom.comp_apply]
      rfl
    rw [h1]
    intro hin
    have : Y.jQ (genPt Z.ξ₀) ∈ (Set.range Y.jQ)ᶜ := by
      rw [← hCe]
      exact hin
    exact this ⟨_, rfl⟩
  obtain ⟨L, _, _, zL, hzW⟩ := exists_point 𝔐.tie W hW
  have hint : 𝔐.Interior zL := by
    refine (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre zL)).1 ?_
    obtain ⟨u, hu⟩ := exists_lift_genFibre Y.s (zL ≫ 𝔐.f)
    let u₀ := u (IsLocalRing.closedPoint (CommRingCat.of L))
    have hfu : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) u₀ = 𝔐.f (centre zL) := by
      have := congrArg (fun g => g (IsLocalRing.closedPoint (CommRingCat.of L))) hu
      exact this
    have hr : u₀ ∈ Set.range Y.jQ := by
      by_contra hn
      have : u₀ ∈ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' C := by
        rw [hCe]
        exact hn
      apply hzW
      rw [Set.mem_preimage, hfu] at this
      exact this
    rw [← Y.ab_gen] at hr
    rw [← hfu]
    exact hr
  obtain ⟨ψL, hψL⟩ := exists_const 𝔐.tie.gen hN ψ zL (𝔐.all _)
  obtain ⟨j, hj⟩ : ∃ j : L →+* ℂ_[p], j.comp ψL = κ' := by
    letI := ψL.toAlgebra
    letI := κ'.toAlgebra
    haveI : Algebra.IsAlgebraic F' L := Algebra.IsAlgebraic.tower_top (K := ℚ) F'
    let φ : L →ₐ[F'] ℂ_[p] := IsAlgClosed.lift
    exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩
  obtain ⟨V, _, _, _, _, _, hV⟩ := exists_dvr j
  obtain ⟨s₀, hft, hqc, -⟩ := ChartFType.main 𝔐.X Ω 𝔐.ξ _ _ 𝔐.all 𝔐.tie
  haveI : IsProper s₀ := LocModel.isProper_of_coordTie 𝔐.all 𝔐.tie s₀
  obtain ⟨z, ⟨hz, -⟩, -⟩ := existsUnique_valuationRing_lift ℤ V L (Int.castRingHom V) 𝔐.X s₀ zL
    (specZIsTerminal.hom_ext _ _)
  subst hz
  refine ⟨V, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    j, ψL, z, hV, hj, hint, hψL, fun a ha => ?_⟩
  obtain ⟨u, s, hs, rfl⟩ := exists_frac κ' ha
  rw [map_mul, map_inv₀]
  refine mul_mem (int_reg hN ψ _ u) ?_
  obtain ⟨g, hg⟩ := int_reg hN ψ ⟨centre z, 𝔐.all _⟩ s
  have hv : ValAt 𝔐.ξ z (ψ (s : F')) ((Scheme.stalkClosedPointTo z).hom g) := ⟨𝔐.all _, g, hg, rfl⟩
  refine inv_reg _ hv ?_
  have h1 := val_unique 𝔐.tie.gen
    (ChangeRing.valAt_change _ _ _ V L (algebraMap V L) z _ _ hv (𝔐.all _)) (hψL s)
  have h2 : ‖j (ψL s)‖ = 1 := by
    have : j (ψL s) = κ' s := by rw [← hj]; rfl
    rw [this]
    exact norm_eq_one κ' hs
  have h0 : ψL s ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at h2
    exact zero_ne_one h2
  obtain ⟨w, hw⟩ := (hV (ψL s)⁻¹).1 (by rw [map_inv₀, norm_inv, h2, inv_one])
  refine IsUnit.of_mul_eq_one w (IsFractionRing.injective V L ?_)
  rw [map_mul, map_one, hw]
  exact (congrArg (· * _) h1).trans (mul_inv_cancel₀ h0)

end RootFieldNumerics.RF
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open GlobalTheory.CompanionTheory.Ar.LieTangent

namespace RootFieldNumerics.RF.IntFr

section Gen

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

theorem exists_bc {R R' : Type} [CommRing R] [CommRing R'] {x : Spec (CommRingCat.of R) ⟶ X}
    {x' : Spec (CommRingCat.of R') ⟶ X} (φ : R →+* R') (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x')
    {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E)
    (M' : LieModel G x' E') : ∃ j : E →+ E', (∀ e, M'.pt (j e) = epsBase φ h ≫ M.pt e) ∧
      ∀ a e, j (a • e) = φ a • j e := by
  choose j hj using fun e => M'.onto _ (isTanAt_base φ h (M.tan e))
  refine ⟨AddMonoidHom.mk' j fun a b => M'.inj ?_, hj, fun a e => M'.inj ?_⟩
  · rw [M'.add, hj, hj, hj, M.add, MonObj.comp_mul]
  · show M'.pt (j (a • e)) = M'.pt (φ a • j e)
    rw [M'.pt_smul, hj, hj, M.pt_smul, ← Category.assoc, base_scale, Category.assoc]

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) := by
  rw [spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Em : Type} [AddCommGroup Em] [Module Ω Em]

theorem valAt_of_extends (M : LieModel G ξ Em) (hall : ∀ q : X, genPt ξ ⤳ q) {V L : Type} [CommRing V] [IsLocalRing V]
    [CommRing L] [IsLocalRing L] (φ : V →+* L) (z : Spec (CommRingCat.of V) ⟶ X) {e : Em}
    {v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G}
    (hv : M.Extends ⟨centre z, hall _⟩ e v) {w : epsAt (Spec.map (CommRingCat.ofHom φ) ≫ z) ⟶ G}
    (hw : w.left = Spec.map (CommRingCat.ofHom (dualMap
      (RingHom.comp (α := X.presheaf.stalk (centre z)) φ (Scheme.stalkClosedPointTo z).hom))) ≫ v.left) :
    M.ValAt (Spec.map (CommRingCat.ofHom φ) ≫ z) e w := by
  have hs := centre_specializes φ z
  let s : X.presheaf.stalk (centre z) →+* X.presheaf.stalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ z)) :=
    (X.presheaf.stalkSpecializes hs).hom
  have h1 : Spec.map (CommRingCat.ofHom s) ≫ X.fromSpecStalk (centre z) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ z)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs
  refine ⟨hall _, epsBase s h1 ≫ v, ⟨isTanAt_base s h1 hv.1, ?_⟩, ?_⟩
  · refine hv.2.trans ?_
    change _ = _ ≫ Spec.map (CommRingCat.ofHom (dualMap s)) ≫ v.left
    rw [← Category.assoc, dual_comp]
    congr 4
    exact RingHom.ext fun a => (genMap_specializes ⟨centre z, hall _⟩ (hall _) hs a).symm
  · refine hw.trans ?_
    change _ = _ ≫ Spec.map (CommRingCat.ofHom (dualMap s)) ≫ v.left
    rw [← Category.assoc, dual_comp]
    congr 4
    exact (congrArg (fun t => t.hom) (stalk_base φ z)).symm

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_coords {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Em : Type} [AddCommGroup Em] [Module Ω Em] (M : LieModel t.G ξ Em) (hall : ∀ q : X, genPt ξ ⤳ q)
    (hξ : IsCptGen ξ) (V L : Type) [CommRing V] [IsLocalRing V] [Field L] [Algebra V L]
    (z : Spec (CommRingCat.of V) ⟶ X) :
    ∃ (g : ℕ) (MV : LieModel t.G z (Fin g → V)) (ρV : 𝓞 E →+* Module.End V (Fin g → V))
      (MC : LieModel t.G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (Fin g → L))
      (ρC : 𝓞 E →+* Module.End L (Fin g → L)), MV.IsActOf t.act.act ρV ∧ MC.IsActOf t.act.act ρC ∧
      (∀ u, (MC.pt (algebraMap V L ∘ u)).left = spMap (dualMap (algebraMap V L)) ≫ (MV.pt u).left) ∧
      (∀ a u, ρC a (algebraMap V L ∘ u) = algebraMap V L ∘ ρV a u) ∧
      ∀ x, x ∈ M.fibAt M.lat z MC ↔ ∀ k, x k ∈ (algebraMap V L).range := by
  classical
  let R : Type := X.presheaf.stalk (centre z)
  let fV : R →+* V := (Scheme.stalkClosedPointTo z).hom
  obtain ⟨g, MR, ρR, -, hbc⟩ := GlobalTheory.T.lie_model_action_base_change E H X t R (X.fromSpecStalk (centre z))
  have hz : spMap fV ≫ X.fromSpecStalk (centre z) = z := spec_centre z
  obtain ⟨MV, ρV, aV, hV, -⟩ := hbc V fV z hz.symm
  obtain ⟨MC, ρC, aC, hC, -⟩ := hbc L ((algebraMap V L).comp fV) (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z)
    ((congrArg (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ ·) hz.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (spec_comp fV (algebraMap V L)))))
  obtain ⟨j, hj, hjs⟩ := exists_bc (algebraMap V L) rfl MV MC
  have sV : ∀ i : Fin g, (fV ∘ (Pi.single i 1 : Fin g → R)) = Pi.single i 1 := fun i => by
    ext k; by_cases h : k = i <;> simp [Pi.single_apply, h]
  have sC : ∀ i : Fin g, (((algebraMap V L).comp fV) ∘ (Pi.single i 1 : Fin g → R)) = Pi.single i 1 := fun i => by
    ext k; by_cases h : k = i <;> simp [Pi.single_apply, h]
  have hj1 : ∀ i : Fin g, j (Pi.single i 1) = Pi.single i 1 := fun i => MC.inj (Over.OverMorphism.ext (by
    rw [hj, ← sC, hC, ← sV]
    refine (congrArg (Spec.map (CommRingCat.ofHom (dualMap (algebraMap V L))) ≫ ·) (hV (Pi.single i 1))).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (MR.pt (Pi.single i 1)).left) (dual_comp _ _))))
  have hju : ∀ u, j u = algebraMap V L ∘ u := fun u => by
    have e : u = ∑ i, u i • (Pi.single i 1 : Fin g → V) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [e]
    rw [map_sum]
    simp only [hjs, hj1]
    ext k; simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  have hpt : ∀ u, MC.pt (algebraMap V L ∘ u) = epsBase (algebraMap V L) rfl ≫ MV.pt u := fun u => by
    rw [← hju, hj]
  refine ⟨g, MV, ρV, MC, ρC, aV, aC, fun u => congrArg (fun q => q.left) (hpt u), fun a u => MC.inj ?_, fun x => ?_⟩
  · rw [aC a, hpt, hpt, aV a, Category.assoc]
  · let Λ : Submodule V (Fin g → L) :=
      { carrier := {x | ∀ k, x k ∈ (algebraMap V L).range}
        add_mem' := fun ha hb k => add_mem (ha k) (hb k)
        zero_mem' := fun k => zero_mem _
        smul_mem' := fun a x hx k => by
          show a • x k ∈ _
          rw [Algebra.smul_def]
          exact mul_mem ⟨a, rfl⟩ (hx k) }
    constructor
    · intro hx
      refine (Submodule.span_le (p := Λ)).2 ?_ hx
      rintro w ⟨h, e, he, hv⟩
      obtain ⟨v, hv₀⟩ := (M.mem_lat_iff _ e).1 he
      obtain ⟨r, rfl⟩ := MR.onto v hv₀.1
      have h3 := valAt_of_extends M hall (algebraMap V L) z hv₀ (hC r)
      have e2 := MC.inj (LieModel.ValAt.unique hξ hv h3)
      intro k
      rw [e2]
      exact ⟨_, rfl⟩
    · intro hx
      choose v hv using hx
      have hsum : x = ∑ i, v i • (Pi.single i 1 : Fin g → L) := by
        ext k
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hv]
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      obtain ⟨e, he⟩ := M.onto _ (isTanAt_base (genMap ξ ⟨centre z, hall _⟩) (spec_genMap ξ ⟨centre z, hall _⟩)
        (MR.tan (Pi.single i 1)))
      have hex : M.Extends ⟨centre z, hall _⟩ e (MR.pt (Pi.single i 1)) :=
        (M.extends_iff _ _ _).2 ⟨MR.tan _, he⟩
      refine Submodule.subset_span ⟨hall _, e, (M.mem_lat_iff _ e).2 ⟨_, hex⟩, ?_⟩
      rw [← sC]
      exact valAt_of_extends M hall (algebraMap V L) z hex (hC _)

theorem exists_sab {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.proved_CubePullSt f t
  exact ⟨_, ⟨m₁⟩⟩

theorem transport {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (h : f = f')
    (m : SABMap t' t f) : ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

theorem act_iff {R : Type} [CommRing R] {X : Scheme.{0}} {t : SAB H X} {t₀ : SAB H (Sp R)} {x : Sp R ⟶ X}
    (m : SABMap t₀ t x) {W : Type} [AddCommGroup W] [Module R W] (M₀ : LieModel t₀.G (𝟙 _) W) (M : LieModel t.G x W)
    (h : ∀ e, (M₀.pt e).left ≫ m.φ = (M.pt e).left) (ρ : 𝓞 E →+* Module.End R W) :
    M₀.IsActOf t₀.act.act ρ ↔ M.IsActOf t.act.act ρ := by
  have key : ∀ a e, (M₀.pt e ≫ t₀.act.act a).left ≫ m.φ = (M.pt e ≫ t.act.act a).left := fun a e => by
    rw [Over.comp_left, Over.comp_left, ← h, Category.assoc, Category.assoc, m.act]
  refine ⟨fun h₀ a e => Over.OverMorphism.ext ?_, fun h₁ a e => Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_)⟩
  · rw [← h, h₀ a e, key]
  · rw [key, h, h₁ a e]
  · rw [Over.w, Over.w]

end RootFieldNumerics.RF.IntFr

namespace RootFieldNumerics.RF

open IntFr

theorem intFrames : IntFrames := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐 V L _ _ _ _ _ _ _ z y₀ hz
  obtain ⟨g, MV, ρV, MC, ρC, aV, aC, hVC, hρ, hfib⟩ := exists_coords 𝔐.t 𝔐.M 𝔐.all 𝔐.tie.gen V L z
  obtain ⟨T, ⟨mT⟩⟩ := IntFr.exists_sab z 𝔐.t
  obtain ⟨tK, ⟨m'⟩⟩ := IntFr.exists_sab (spMap (algebraMap V L)) T
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mT m'
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m n₁
  obtain ⟨n₃, hn₃⟩ := IntFr.transport hz n₂
  obtain ⟨m₃, hm₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n₃
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m₃
  obtain ⟨MK, hK⟩ := (LieMove.main L _ _ _ _ _ (Fin g → L) n₁.cart).1 MC
  obtain ⟨MU, hU⟩ := (LieMove.main L _ _ _ _ _ (Fin g → L) m.cart).2 MK
  obtain ⟨MT, hT⟩ := (LieMove.main V _ _ _ _ _ (Fin g → V) mT.cart).1 MV
  have aK := (act_iff n₁ MK MC hK ρC).2 aC
  have aT := (act_iff mT MT MV hT ρV).2 aV
  refine ⟨T, tK, m, m', g, MC, MU, ρC, aC, (act_iff m MK MU hU ρC).1 aK, fun e => ?_, hfib, ?_⟩
  · have w := Over.w (MK.pt e)
    refine ⟨Over.homMk ((MK.pt e).left ≫ n₃.φ) ?_, ⟨(MK.pt e).left ≫ m₃.φ, ?_, ?_, ?_⟩, ?_⟩
    · rw [Category.assoc, n₃.cart.1.w, ← Category.assoc, w]
      simp
    · rw [Category.assoc, m₃.cart.1.w, ← Category.assoc, w]
      simp
    · rw [Category.assoc, ← hm]; exact hU e
    · rw [Category.assoc]
      exact congrArg ((MK.pt e).left ≫ ·) hm₃.symm
    · show _ = (MK.pt e).left ≫ n₃.φ
      rw [hn₃, hn₂, ← Category.assoc]
      exact congrArg (· ≫ 𝔐.m.φ) (hK e).symm
  · intro σ n x hx hspan
    have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
    have hmem : ∀ k, x k ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V :=
      fun k => hspan ▸ Submodule.subset_span ⟨k, rfl⟩
    choose xV hxV using fun k => (hfib _).1 (hmem k).1
    have hxe : ∀ k, x k = algebraMap V L ∘ xV k := fun k => funext fun i => (hxV k i).symm
    have cinj : ∀ u u' : Fin g → V, algebraMap V L ∘ u = algebraMap V L ∘ u' → u = u' :=
      fun u u' h => funext fun i => hinj (congrFun h i)
    have heig : ∀ u : Fin g → V, u ∈ eigSp ρV σ ↔ algebraMap V L ∘ u ∈ eigSp ρC ((algebraMap V L).comp σ) := fun u => by
      simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero, hρ]
      refine forall_congr' fun a => ⟨fun h => ?_, fun h => cinj _ _ ?_⟩
      · rw [h]; ext i; simp
      · rw [h]; ext i; simp
    have hsum : ∀ cf : Fin n → V, algebraMap V L ∘ (∑ k, cf k • xV k) = ∑ k, cf k • x k := fun cf => by
      ext i; simp [Finset.sum_apply, hxe, Algebra.smul_def]
    refine ⟨σ, fun k => MT.pt (xV k), rfl, ?_, fun k => ⟨(MK.pt (x k)).left, hU _, ?_⟩⟩
    · refine (GlobalTheory.T.eigen_frame_iff_eigenspace_basis _ V T.G (𝟙 _) _ MT _ T.act ρV σ n xV aT).2 ⟨fun k => (heig _).2 (hxe k ▸ (hmem k).2), ?_⟩
      intro e he
      have h1 : algebraMap V L ∘ e ∈ Submodule.span V (Set.range x) := by
        rw [hspan]
        exact ⟨(hfib _).2 fun i => ⟨_, rfl⟩, (heig e).1 he⟩
      obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
      refine ⟨cf, cinj _ _ (by rw [hsum, hcf]), fun cf' h => ?_⟩
      have h2 : ∑ k, (algebraMap V L (cf' k) - algebraMap V L (cf k)) • x k = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, algebraMap_smul]
        rw [← hsum, ← h, hcf, sub_self]
      exact funext fun k => hinj (sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hx _ h2 k))
    · refine mT.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, ← hn₁, Category.assoc]
        refine (hK _).trans ?_
        rw [hxe, hVC]
        exact congrArg (_ ≫ ·) (hT _).symm
      · rw [Category.assoc, m'.cart.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
        simpa using (spec_dual_alg (algebraMap V L)).symm

end RootFieldNumerics.RF
end
end

section
noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

namespace Num

theorem value_bound (p q : ℕ) (l L : ℝ) (h7 : Real.log 7 / 2 ≤ l) :
    |((p : ℝ) - q) / 2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - l - L)| +
      ((p + q : ℕ) : ℝ) * Real.log 2 ≤ ((p + q : ℕ) : ℝ) * (3 / 2 * l + |L| / 2) := by
  have hc := OnHodge.const_le
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h70 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h4 : 2 * Real.log 2 ≤ Real.log (2 * Real.pi) := by
    have : Real.log (2 ^ 2) ≤ Real.log (2 * Real.pi) :=
      Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hL := le_abs_self L
  have hL' := neg_abs_le L
  have hp : (0 : ℝ) ≤ p := p.cast_nonneg
  have hq : (0 : ℝ) ≤ q := q.cast_nonneg
  set c := Real.eulerMascheroniConstant + Real.log (2 * Real.pi) with hcdef
  set b := 3 / 2 * l + |L| / 2 - Real.log 2 with hb
  have a1 : 0 ≤ b - (c - l - L) / 2 := by linarith
  have a2 : 0 ≤ b + (c - l - L) / 2 := by linarith
  have : |((p : ℝ) - q) / 2 * (c - l - L)| ≤ (p + q) * b :=
    abs_le.2 ⟨by nlinarith [mul_nonneg hp a2, mul_nonneg hq a1], by nlinarith [mul_nonneg hp a1, mul_nonneg hq a2]⟩
  push_cast
  nlinarith

theorem near_of (n : ℕ) (bad : Finset ℕ) (h2 : 2 ∈ bad) (rd L h₀ : ℝ) (d v : ℕ → ℝ)
    (hb : |h₀| + (n : ℝ) * Real.log 2 ≤ (n : ℝ) * (3 / 2 * Real.log rd + |L| / 2))
    (hd : ∀ r ∈ bad, 0 ≤ v r ∧ |d r| ≤ ((n : ℝ) * cP r + (n : ℝ) * v r) * Real.log r)
    (hv : ∑ r ∈ bad, v r * Real.log r ≤ Real.log rd) : NearRecord n bad rd L (h₀ + ∑ r ∈ bad, d r) := by
  set N : ℝ := (n : ℝ) with hN
  have hN0 : 0 ≤ N * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_pos one_lt_two).le
  obtain ⟨hv2, hd2⟩ := hd 2 h2
  have hv2' := mul_nonneg hN0 hv2
  simp only [cP, if_true, Nat.cast_ofNat] at hd2
  obtain ⟨e, he, he'⟩ : ∃ e : ℝ, |e| ≤ N * Real.log 2 ∧ |d 2 - e| ≤ (N + N * v 2) * Real.log 2 := by
    rw [abs_le] at hd2
    rcases le_total 0 (d 2) with h | h
    · exact ⟨N * Real.log 2, (abs_of_nonneg hN0).le, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
    · exact ⟨-(N * Real.log 2), by rw [abs_neg, abs_of_nonneg hN0], abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
  refine ⟨_ + e, fun r => d r - if r = 2 then e else 0, v, (abs_add_le _ _).trans ((add_le_add le_rfl he).trans hb), ?_,
    fun r hr => ⟨(hd r hr).1, ?_⟩, hv⟩
  · rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' bad 2, if_pos h2]; ring
  · by_cases h : r = 2
    · subst h
      have : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
      simp only [if_true, this, div_one]
      exact_mod_cast he'
    · have := (hd r hr).2
      simp only [cP, if_neg h] at this ⊢
      rwa [sub_zero, div_eq_mul_one_div]

def extP (g : Nat.Primes → ℝ) (n : ℕ) : ℝ := if h : n.Prime then g ⟨n, h⟩ else 0

theorem extendFromPrimes_coe (g : Nat.Primes → ℝ) (ℓ : Nat.Primes) : extP g ℓ = g ℓ := dif_pos ℓ.2

theorem exists_primes (bad : Finset ℕ) (hb : ∀ ℓ ∈ bad, ℓ.Prime) :
    ∃ B : Finset Nat.Primes, (∀ ℓ, ℓ ∈ B ↔ (ℓ : ℕ) ∈ bad) ∧ ∀ G : ℕ → ℝ, ∑ ℓ ∈ bad, G ℓ = ∑ ℓ ∈ B, G ℓ := by
  refine ⟨bad.preimage (fun ℓ : Nat.Primes => (ℓ : ℕ)) Subtype.val_injective.injOn, fun ℓ => Finset.mem_preimage,
    fun G => ?_⟩
  exact (Finset.sum_preimage (fun ℓ : Nat.Primes => (ℓ : ℕ)) bad Subtype.val_injective.injOn G
    fun x hx hn => absurd ⟨⟨x, hb x hx⟩, rfl⟩ hn).symm

theorem place_eq {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (κ : F →+* ℂ_[p])
    (v : HeightOneSpectrum (𝓞 F)) (h : ∀ a : F, v.valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1) : v = placeOf κ := by
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  rw [h, valuation_placeOf_le_one_iff]

theorem logIdeal_nonpos {E : Type} [Field E] [NumberField E] (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) :
    logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ≤ 0 := by
  obtain ⟨a, -, -, -, e⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
    (j.injective.comp RingOfIntegers.coe_injective) differentIdeal_ne_bot
  rw [e]
  refine Real.log_nonpos (norm_nonneg _) ?_
  exact (valuation_placeOf_le_one_iff j (a : E)).1 ((placeOf j).valuation_le_one a)

end Num

open Num in
theorem numerics : Numerics := by
  intro E _ _ _ H p q F F' _ _ _ _ ι σ N r bad hσ h2 hbp hAd hdeg hloc
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F') => v.valuation_exists_uniformizer F'
  let N' : LogNorms F' := ⟨fun s => N.inf (s.comp ι), fun ℓ κ' => (r (placeOf κ') : ℝ) * Real.log ‖κ' (π (placeOf κ'))‖⟩
  obtain ⟨hAd', hdeg'⟩ := deg_eq_places F' N' r (by
    intro ℓ κ' v π' hv hπ'
    obtain rfl := place_eq κ' v hv
    have h0 : π' ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have := log_norm_eq_of_valuation κ' (n := 1) (hπ _) hπ' h0
    show _ * _ = _
    rw [this]
    simp)
  have hgoal : ((r.sum fun v x => (x : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ s : F' →+* ℂ, N.inf (s.comp ι)) /
      (Module.finrank ℚ F' : ℝ) = N'.deg := hdeg'.symm
  rw [hgoal]
  obtain ⟨hext, hextA⟩ := GlobalTheory.T.logNorms_ext_degree_adelic F F' ι N
  have hAdx : (N.ext ι).IsAdelic := hextA.2 hAd
  have hl := fun (ℓ : Nat.Primes) (κ' : F' →+* ℂ_[ℓ]) =>
    hloc ℓ κ' (placeOf κ') (π _) (valuation_placeOf_le_one_iff κ') (hπ _)
  have hn' : (0 : ℝ) < Module.finrank ℚ F' := by exact_mod_cast Module.finrank_pos
  have hnE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  obtain ⟨B, hB, hBs⟩ := exists_primes bad hbp
  let f : E →+* F' := IsFractionRing.lift (A := 𝓞 E) (g := ι.comp σ) (ι.injective.comp hσ)
  have hf : ∀ a : 𝓞 E, f (algebraMap (𝓞 E) E a) = ι (σ a) := fun a => IsFractionRing.lift_algebraMap _ a
  let g : Nat.Primes → ℝ := fun ℓ => -(N'.finSum ℓ - (N.ext ι).finSum ℓ) / Module.finrank ℚ F'
  let w : Nat.Primes → ℝ := fun ℓ =>
    -∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
  have hw0 : ∀ ℓ, 0 ≤ w ℓ := fun ℓ => neg_nonneg.2 (Finset.sum_nonpos fun j _ => logIdeal_nonpos ℓ j)
  have hlog : ∀ ℓ : Nat.Primes, 0 < Real.log (ℓ : ℕ) := fun ℓ => Real.log_pos (by exact_mod_cast ℓ.2.one_lt)
  have hsupp : ∀ M : LogNorms F', M.IsAdelic → (Function.support M.finSum).Finite := fun M hM =>
    Set.Finite.subset hM fun ℓ hℓ => by
      by_contra hc
      simp only [Set.mem_setOf_eq, not_exists, not_not] at hc
      exact hℓ (by simp [LogNorms.finSum, hc])
  have hsplit : N'.deg = N.deg + ∑ ℓ ∈ bad, extP g ℓ := by
    rw [hBs, ← hext]
    simp only [extendFromPrimes_coe, g]
    have e1 : ∑ᶠ ℓ, (N'.finSum ℓ - (N.ext ι).finSum ℓ) = ∑ ℓ ∈ B, (N'.finSum ℓ - (N.ext ι).finSum ℓ) := by
      refine finsum_eq_sum_of_support_subset _ fun ℓ hℓ => ?_
      by_contra hc
      refine hℓ (sub_eq_zero.2 (Finset.sum_congr rfl fun κ' _ => ?_))
      exact (hl ℓ κ').1 fun h => hc ((hB ℓ).2 h)
    rw [finsum_sub_distrib (hsupp _ hAd') (hsupp _ hAdx)] at e1
    rw [← Finset.sum_div, Finset.sum_neg_distrib, ← e1]
    have e2 : ∑ s, N'.inf s = ∑ s, (N.ext ι).inf s := rfl
    simp only [LogNorms.deg]
    rw [e2]
    ring
  rw [hsplit]
  have hrd : hostRd E = rootDiscr E := OnHodge.hostRd_eq E
  refine near_of (p + q) bad h2 _ _ _ _ (extP fun ℓ => w ℓ / Module.finrank ℚ E / Real.log (ℓ : ℕ)) ?_ ?_ ?_
  · rw [hdeg]
    refine value_bound p q _ _ ?_
    have h7 : (7 : ℝ) ≤ H.d := by
      have := H.d_mod
      have : 7 ≤ H.d := by omega
      exact_mod_cast this
    have h1 := (GlobalTheory.T.sqrt_discriminant_bounds_cm_field E H).2
    rw [hrd, ← Real.log_sqrt (by norm_num)]
    exact Real.log_le_log (Real.sqrt_pos.2 (by norm_num)) ((Real.sqrt_le_sqrt h7).trans h1)
  · intro n hn
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ : Nat.Primes, (ℓ : ℕ) = n := ⟨⟨n, hbp n hn⟩, rfl⟩
    rw [extendFromPrimes_coe, extendFromPrimes_coe]
    refine ⟨div_nonneg (div_nonneg (hw0 ℓ) hnE.le) (hlog ℓ).le, ?_⟩
    have hk : ∀ κ' : F' →+* ℂ_[ℓ], |N'.fin ℓ κ' - (N.ext ι).fin ℓ κ'| ≤ ((p + q : ℕ) : ℝ) * (cP ℓ * Real.log (ℓ : ℕ) -
        logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := fun κ' => by
      obtain ⟨a, ha, ha0, -, e⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
        ((κ'.comp f).injective.comp RingOfIntegers.coe_injective) differentIdeal_ne_bot
      rw [e, RingHom.comp_apply, RingHom.comp_apply, hf]
      exact (hl ℓ κ').2 hn a ha ha0
    have hfib := GlobalTheory.T.sum_embeddings_base_change E F' ℂ_[ℓ] f
      fun j => logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
    have hs : |N'.finSum ℓ - (N.ext ι).finSum ℓ| ≤ ((p + q : ℕ) : ℝ) * (Module.finrank ℚ F' * (cP ℓ * Real.log (ℓ : ℕ)) -
        ∑ κ' : F' →+* ℂ_[ℓ], logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := by
      simp only [LogNorms.finSum]
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun κ' _ => hk κ').trans (le_of_eq ?_))
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
    have hS : ∑ κ' : F' →+* ℂ_[ℓ], logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
        -(Module.finrank ℚ F' * (w ℓ / Module.finrank ℚ E)) := by
      apply mul_left_cancel₀ hnE.ne'
      rw [hfib]
      simp only [w]
      field_simp
    rw [hS] at hs
    simp only [g]
    rw [abs_div, abs_neg, abs_of_pos hn', div_le_iff₀ hn']
    refine hs.trans (le_of_eq ?_)
    have := (hlog ℓ).ne'
    field_simp
    ring
  · rw [hBs]
    simp only [extendFromPrimes_coe]
    obtain ⟨hfin, hsum⟩ := GlobalTheory.T.different_ideal_log_sum_root_discriminant E
    have hwf : (Function.support w).Finite := hfin.subset fun ℓ hℓ => fun h => hℓ (by simp only [w]; rw [h, neg_zero])
    have hws : ∑ᶠ ℓ, w ℓ = Module.finrank ℚ E * Real.log (rootDiscr E) := by
      simp only [w]
      rw [finsum_neg_distrib, hsum]
      ring
    have hle : ∑ ℓ ∈ B, w ℓ ≤ ∑ᶠ ℓ, w ℓ := by
      rw [finsum_eq_sum_of_support_subset w (s := B ∪ hwf.toFinset) (fun ℓ hℓ => by simp [hℓ])]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun ℓ _ _ => hw0 ℓ
    rw [Finset.sum_congr rfl fun ℓ _ => div_mul_cancel₀ _ (hlog ℓ).ne', ← Finset.sum_div, div_le_iff₀ hnE, hrd]
    linarith

end RootFieldNumerics.RF
end
end

section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem rootFlatOnHodge (hFD : Fl.FlatDegree) (hG : Given) : Flat.RootFlatOnHodge :=
  RF.rootFlatOnHodge_of RF.cptEx RF.periodOf RF.smoothLine
    (RF.localCmp_of RF.pointEx RF.valuePhi RF.intFrames RF.fibSandwich) RF.chiEx RF.numerics hFD hG

theorem global_model_tower_final_condition : Fl.FlatDegree → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  intro hFD hG E _ _ _ _ H D Xo l c Y _ T o II hY _ _ _ _ a τ
  exact Flat.OnHodge.tower (rootFlatOnHodge hFD hG) hY ⟨o.toTowerOrigin, o.omVB⟩ a τ

end RootFieldNumerics
end
