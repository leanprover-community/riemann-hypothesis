import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyPullUnitaryTraitFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIdlAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleMapOfSameUniformisedCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRelAmpleKTrivOfTrivialisationsGenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModuliObjectSpreadNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPartMemTautologicalPointTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointLiftZeroFirstCoordinate
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFamilyFromRegularBaseCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplAtFactorOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsDomainOfIsComplAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentIndepOfIsComplAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefficientFieldOfCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjectiveOfResidueOfCotangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegeneratingFamilyDataFromBaseAlgClosedResidue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyIsPointRigidTautologicalChart

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem bdParam_ne_zero (k : Type) [Field k] (m e : ℕ) (i : Fin m) : bdParam k m e i ≠ 0 := fun h => by
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin e) 1)) h
  simp [bdParam, MvPowerSeries.coeff_X] at this

theorem exists_fractionRing_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

theorem exists_lift_normBl {X Z S : Scheme.{0}} (i : X ⟶ Z) (π : S ⟶ Z) (j : X ⟶ S) (J : Z.IdealSheafData)
    (hN : GlobalTheory.Poinc.IsNormBl π J) (hji : j ≫ π = i) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ X) (hy : jK R ≫ a = y ≫ i) (f : R) (hf : f ≠ 0)
    (hJ : idlAlong J a = Ideal.span {f}) : ∃ ξ : Sp R ⟶ S, jK R ≫ ξ = y ≫ j := by
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, -⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  obtain ⟨c, ⟨hc1, -⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  exact ⟨c, hc1⟩

theorem taut_exists_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∃ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT
  obtain ⟨hm, hs, -⟩ := hT
  have hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)).charZero
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  have hBase : GlobalTheory.Mum.Base (ChartRing k m e) := ⟨hAdm, hcF⟩
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  obtain ⟨⟨-, -, hi, -, -, -, -⟩, -, hext, ⟨-, -, hval⟩, ⟨hbl, -, -, -, hji, -, -, -⟩, -⟩ := hU
  obtain ⟨ξZ, hξZ, -⟩ := hext _ hBase C.t ⟨C.P⟩ C.y C.gen (spMap C.b) C.y_over.symm
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) C.P.D.toPre.X
  have hPF := hpf C.P.D.toPre.X C.rank
  have hnat : ∀ i, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • C.δ i) = n := fun i =>
    hPF.exists_nat (Submodule.smul_mem _ _ (C.cone.mem i)) (fun y => by
      simpa using mul_nonneg (by positivity : (0 : ℤ) ≤ l.M') (C.cone.nonneg i y))
  choose b hb using hnat
  let a : Fin m → ℕ := fun i => d * b (Fin.cast hm.symm i)
  have hprod : ∏ i, bdParam k m e i ^ a i = ∏ i : Fin C.m, C.s i ^ (d * b i) :=
    (Fintype.prod_equiv (finCongr hm) _ _ (fun j => by simp [a, hs j])).symm
  have hI : idlAlong J ξZ = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
    refine GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr k m e _ a fun W _ _ _ hW ψ hψi hψl => ?_
    haveI := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hne : ∀ i, ψ (C.s i) ≠ 0 := fun i h0 => by
      have : C.s i = 0 := hψi (h0.trans (map_zero ψ).symm)
      rw [hs i] at this
      exact bdParam_ne_zero k m e _ this
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible (hne i) hϖ
    obtain ⟨fK, hκ⟩ := exists_fractionRing_map ψ hψi
    obtain ⟨t, tK, P, h1, h2, be, hbe, hmono, hφ⟩ :=
      GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ hBase C W hW ψ hψi hψl ϖ hϖ w hw (spMap fK) hκ
    obtain ⟨n, hn, hIn⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξZ) (spMap fK ≫ C.y)
      (by rw [Category.assoc, ← hξZ, ← Category.assoc, hκ, Category.assoc]) t tK h1 h2 P be hbe hmono
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hIn, hprod, map_prod]
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    have hnw : n = ∑ i, w i * (d * b i) := by
      have : (n : ℝ) = ∑ i, (w i : ℝ) * (d * b i) := by
        rw [hn, hφ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hb i]; ring
      exact_mod_cast this
    have : Associated (∏ i, ψ (C.s i ^ (d * b i))) (∏ i : Fin C.m, (ϖ ^ w i) ^ (d * b i)) :=
      Associated.prod _ _ _ fun i _ => by rw [map_pow]; exact (hw i).pow_pow
    rw [hnw]
    refine (this.trans ?_).symm
    rw [← Finset.prod_pow_eq_pow_sum]
    simp only [← pow_mul]
    exact Associated.refl _
  have hf0 : ∏ i, bdParam k m e i ^ a i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (bdParam_ne_zero k m e _)
  obtain ⟨ξ, hξ⟩ := exists_lift_normBl i π j J hbl hji _ ξZ C.y hξZ _ hf0 hI
  exact ⟨ξ, hξ.symm⟩

end GlobalTheory.UChart
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivSol

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def mulPull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (n : ℕ) :
    IsPullDeg φ (mulDeg D n) (mulDeg D' n) where
  e := hD.e
  e_hom := hD.e_hom
  w := hD.w
  w_gen := hD.w_gen
  he := hD.he
  w_rig := hD.w_rig
  xe := hD.xe
  c_pr := fun (x : D'.X) => by
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    show (D'.c (n • x)).left ≫ _ = specOf φ ≫ (D.c (n • hD.xe x)).left
    rw [← hx]
    exact hD.c_pr (n • x)
  W := hD.W
  psiW := ⟨fun (χ : D.X) => hD.psiW.psi (n • χ), fun (χ : D.X) => hD.psiW.psi_gen (n • χ), fun (χ : D.X) => hD.psiW.psi_eq (n • χ)⟩
  g := hD.g
  g_comm := hD.g_comm
  psi_pr := fun (x : D'.X) => by
    have h := hD.psi_pr (n • x)
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    rw [hx] at h
    exact h

theorem mulDeg_psiEven (D : DegPre R) (n : ℕ) (h : D.PsiEven) : (mulDeg D n).PsiEven :=
  fun (a : D.X) => MulDeg.corr_even_degenerationData_negPoint D h (n • a) (n • (-a)) (neg_nsmul a n)

theorem mulDeg_tauBimult (D : DegPre R) (n : ℕ) (h : D.TauBimult) : (mulDeg D n).TauBimult :=
  fun (a a' b : D.X) => MulDeg.corr_bimultiplicative_degenerationData_sums D h (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
    (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _)

theorem mulDeg_psiUnitOn (D : DegPre R) (n : ℕ) (h : ∀ y, PsiUnitOn D y Set.univ) :
    ∀ y, PsiUnitOn (mulDeg D n) y Set.univ :=
  fun (y : D.X) => h (n • y)

end GlobalTheory.DivSol

namespace GlobalTheory.DivSol

theorem exists_qkPt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ y : P.D.toPre.X, ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', p₀.y = y := by
  intro E _ _ _ H D' l c L R _ _ _ _hB t P iw I _ s ε e _hbal hs hdf y
  obtain ⟨g, hD, hg, -, -⟩ := hdf
  obtain ⟨DR, hR, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg polBaseChange_holds L.W R iw L.D ⊤
    (GlobalTheory.ArcPull.nonempty_psiOn_top L.D L.gen) trivial
  have hbiR : DR.TauBimult := GlobalTheory.tauBimult_of_isPullDeg globalFns_holds _ _ iw L.D DR hR L.bimult
  have hunR : ∀ y, PsiUnitOn DR y Set.univ := GlobalTheory.PullDegTop.psiUnitOn_univ hR L.gen
  have hevR : DR.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull globalFns_holds _ _ iw L.D DR hR L.even
  have hC : IsPullDeg (RingHom.id R) (mulDeg DR l.M') (GlobalTheory.PolDeg.rescale P.D.toPre g) :=
    (GlobalTheory.Mum.isPullDeg_unique_any L.W R iw (mulDeg L.D l.M') _ _ ⟨mulPull hR l.M'⟩ ⟨hD⟩).some
  obtain ⟨T, ib, β, ββ, w, hF⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData (RingHom.id R) DR hbiR hunR l.M'
  let e' : P.D.toPre.X ≃+ (Fin T.r → ℤ) := hC.xe.trans ib
  let x : (Fin T.r → ℤ) ≃+ L.D.X := e'.symm.trans e.toAddEquiv
  have hx : ∀ a, x (e' a) = e a := fun a => by simp [x]
  let ε' : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    LinearMap.mk₂ ℤ (fun u v => ε k (x u) (H.w0 • x v) + ε k (x v) (H.w0 • x u))
      (fun m₁ m₂ n => by simp only [map_add, smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x m)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
      (fun m n₁ n₂ => by simp only [map_add, smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x n)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
  have hne : ∀ i, algebraMap R (FractionRing R) (s i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hs i)
  have hgv : ∀ y, ((g y : (FractionRing R)ˣ) : FractionRing R) =
      (∏ k, algebraMap R (FractionRing R) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg y, Units.val_inv_eq_inv_val, inv_inv]
  have hcoc : ∀ a a' : P.D.toPre.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing R)ˣ) : FractionRing R) =
      ∏ i, algebraMap R (FractionRing R) (s i) ^ ((l.M' : ℤ) * ε' i (e' a) (e' a')) := by
    intro a a'
    rw [Units.val_mul, Units.val_mul, hg (a + a'), hgv a, hgv a', ← Finset.prod_inv_distrib,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hne i), ← zpow_add₀ (hne i)]
    congr 1
    simp only [ε', LinearMap.mk₂_apply, hx, map_add, smul_add, LinearMap.add_apply]
    ring
  obtain ⟨β', ββ', w', hF'⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg DR l.M') (mulDeg_psiEven _ _ hevR)
    (mulDeg_tauBimult _ _ hbiR) (mulDeg_psiUnitOn _ _ hunR) ib β ββ w hF R (RingHom.id R) Function.injective_id
    P.D.toPre g hC s ε' e' (fun _ => rfl) hcoc
  obtain ⟨p, hp, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε' l.M' R P.D.toPre (RingHom.id R) s e' β' ββ' w'
    P.D.tau_bimult hF' hs (FractionRing R) (e' y)
  exact ⟨p, by rw [hp]; simp⟩

end GlobalTheory.DivSol
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelTorsionPoint_of_comesFromBase : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ y : P.D.toPre.X, ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', p₀.y = y := by
  atlas_forward_decl GlobalTheory.DivSol.exists_qkPt_of_divFrom
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPoint_lift_zero_first_coordinate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g)), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivBy L Q oQ iw s ε e g hD → ∀ a : D'.La, ∃ p : QkPt Q (FractionRing V) l.M', IsLevPt L iw hD a p := by
  first | exact @GlobalTheory.UCanon.exists_levPt | exact GlobalTheory.UCanon.exists_levPt | (intros; apply GlobalTheory.UCanon.exists_levPt <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivTorsRat

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_char_descend {X K F : Type} [Group X] [Field K] [Field F] (f : K →+* F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (t : X →* Fˣ) (ht : t ^ k = 1) :
    ∃ t₀ : X →* Kˣ, (Units.map f.toMonoidHom).comp t₀ = t := by
  have hinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have : NeZero k := ⟨hk⟩
  have hr : ∀ x, t x ∈ (Units.map f.toMonoidHom).range := fun x => by
    have h1 : ((t x : Fˣ) : F) ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, ht]; rfl
    obtain ⟨i, -, hi⟩ := (hζ.map_of_injective f.injective).eq_pow_of_pow_eq_one h1
    exact ⟨(hζ.isUnit hk).unit ^ i, Units.ext (by simpa using hi)⟩
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (t.codRestrict _ hr), MonoidHom.ext fun x => ?_⟩
  exact MonoidHom.apply_ofInjective_symm hinj _

theorem exists_qkExt_of_b {V : Type} [CommRing V] [IsDomain V] {Q : DegPre V} (hB : Q.TauBimult) {K F : Type} [Field K]
    [Field F] [Algebra (FractionRing V) K] [Algebra (FractionRing V) F] (f : K →+* F)
    (hf : f.comp (algebraMap (FractionRing V) K) = algebraMap (FractionRing V) F) {k : ℕ} (hk : k ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (p : QkPt Q F k) (hp : p.y = 0) (q : QkPt Q K k) (hq : q.y = 0)
    (hb : p.g.b.left = spMap f ≫ q.g.b.left) : ∃ p₀ : QkPt Q K k, QkExt f p₀ p := by
  have hb' : p.g.b = (gtExt Q f hf q.g).b := (Over.OverMorphism.ext hb).trans (gtExt_b f hf _).symm
  have np : k • p.g = 0 := by rw [qk_nsmul hB, hp, map_zero]
  have nq : k • q.g = 0 := by rw [qk_nsmul hB, hq, map_zero]
  obtain ⟨t, ht⟩ := exists_torusPt_eq (g := p.g + -(gtExt Q f hf q.g)) (by rw [add_b, neg_b, hb', mul_inv_cancel])
  have tk : t ^ k = 1 := by
    have : torusPt Q F (Additive.ofMul (t ^ k)) = torusPt Q F (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, ← ht, nsmul_add, smul_neg, ← map_nsmul, np, nq, ofMul_one, map_zero, map_zero, neg_zero,
        add_zero]
    exact torusPt_injective this
  obtain ⟨t₀, rfl⟩ := exists_char_descend f hk hζ t tk
  have t0 : t₀ ^ k = 1 := MonoidHom.ext fun x => Units.map_injective (f := f.toMonoidHom) f.injective (by
    have := DFunLike.congr_fun tk x
    rw [MonoidHom.pow_apply, map_pow, MonoidHom.one_apply, map_one]
    exact this)
  refine ⟨qkMk hB 0 (q.g + torusPt Q K (Additive.ofMul t₀)) ?_, (qkExt_iff hB f hf _ _).2 (qk_ext hp ?_)⟩
  · rw [nsmul_add, nq, ← map_nsmul, ← ofMul_pow, t0, ofMul_one, map_zero, map_zero, add_zero]
  · show p.g = gtExt Q f hf (q.g + torusPt Q K (Additive.ofMul t₀))
    rw [map_add, GlobalTheory.QkNumberField.gtExt_torusPt, ← ht]
    abel

theorem exists_ptEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) (T : Over S') (b : T.left ⟶ S) (hb : b = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  refine ⟨MulEquiv.ofBijective (pushHom gp T) ⟨fun x y e => ?_, fun y => ?_⟩, fun _ => rfl⟩
  · exact Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))
  · exact ⟨Over.homMk (gp.1.lift y.left T.hom (Over.w y)) (gp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (gp.1.lift_fst _ _ _)⟩

theorem exists_etaA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B W : Type} [CommRing B] [CommRing W] {b : Geo.Tor.Base l B} {σ : B →+* W} (o : Obj D l b (spMap σ)) {F : Type} [Field F]
    [IsAlgClosed F] (j : W →+* F) (x : Over.mk (spMap j) ⟶ o.t.G) (hx : x ^ l.A = 1) :
    ∃ a, x.left = spMap j ≫ (o.etaA a).left := by
  obtain ⟨-, I, -, h, -⟩ := o.geom F (spMap j) (j.comp σ) (by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos x).1 hx
  refine ⟨a, ?_⟩
  rw [← ha, ← h]
  simp

theorem exists_qkExt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ p : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', p.y = 0 → ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) p₀ p := by
  intro E _ _ _ H D' l c L R _ _ _ _ t P iw I _ s ε e hε hs ⟨g, hD, hdiv⟩ p hp
  have hB := P.D.tau_bimult
  have hM : 0 < l.M' := (LowDat.lowLevel l).A_pos
  let K := FractionRing R
  let F := AlgebraicClosure K
  let j : L.W →+* F := (algebraMap K F).comp ((algebraMap R K).comp iw)
  have hj : spMap j = (TF (R := R) F).hom ≫ spMap iw := by
    show _ = (jFK (R := R) F ≫ jK R) ≫ spMap iw
    simp only [j, jFK, jK, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have gp : IsGrpPullback P.D.toPre.P.A L.D.P.A (spMap iw) (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) :=
    pull_grp hD
  obtain ⟨ρ₁, h₁⟩ := exists_ptEquiv gp (TF (R := R) F) (spMap j) hj
  obtain ⟨ρ₂, h₂⟩ := exists_ptEquiv L.ab.1 (Over.mk (spMap j)) (spMap j) (Category.comp_id _).symm
  have hbk : p.g.b ^ l.M' = 1 := by rw [← nsmul_b, qk_nsmul hB, hp, map_zero, zero_b]
  obtain ⟨a, ha⟩ := exists_etaA L.o j (ρ₂.symm (ρ₁ p.g.b)) (by
    show _ ^ l.M' = 1
    rw [← map_pow, ← map_pow, hbk, map_one, map_one])
  obtain ⟨q, hq, hqb⟩ := GlobalTheory.T.exists_levelPoint_lift_zero_first_coordinate L P.D.toPre P.oD iw s ε e g hD hε hs hdiv a
  have hζ : IsPrimitiveRoot (⟨zeta l.M', c.zeta_mem⟩ : c.F) l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (Complex.isPrimitiveRoot_exp l.M' hM.ne')
      Subtype.val_injective
  refine exists_qkExt_of_b hB (algebraMap K F) (RingHom.comp_id _) hM.ne'
    (hζ.map_of_injective ((algebraMap R K).comp (iw.comp L.b)).injective) p hp q hq ?_
  have e₂ := h₂ (ρ₂.symm (ρ₁ p.g.b))
  rw [ρ₂.apply_symm_apply, ha, h₁] at e₂
  refine gp.1.hom_ext (e₂.trans (Eq.symm ((Category.assoc _ _ _).trans
    ((congrArg (spMap (algebraMap K F) ≫ ·) hqb).trans ?_)))) ?_
  · rw [hj]
    show _ = (((spMap (algebraMap K F) ≫ jK R) ≫ _) ≫ _) ≫ _
    simp only [Category.assoc]
  · exact (Over.w p.g.b).trans ((Over.w (extMap (R := R) (algebraMap K F) (RingHom.comp_id _) ≫ q.g.b)).symm)

end GlobalTheory.DivTorsRat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qkPoint_extension_of_divided_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ p : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', p.y = 0 → ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) p₀ p := by
  atlas_forward_decl GlobalTheory.DivTorsRat.exists_qkExt_of_divFrom
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivGalFix

open GlobalTheory.TorusExt

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qkPt_rational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ q : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ q₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) q₀ q := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD q
  have hB := P.D.tau_bimult
  have ha : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
      (algebraMap (FractionRing R) (FractionRing R)) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p₀, hy⟩ := GlobalTheory.T.exists_levelTorsionPoint_of_comesFromBase L R hR t P iw s ε e hε hs hD q.y
  set p₁ := qkExt hB (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ha p₀ with hp₁
  have h0 : l.M' • (q.g - p₁.g) = iota hB (AlgebraicClosure (FractionRing R)) 0 := by
    rw [smul_sub, qk_nsmul hB, qk_nsmul hB, map_zero]
    show iota hB _ q.y - iota hB _ p₀.y = 0
    rw [hy, sub_self]
  obtain ⟨r₀, hr⟩ := GlobalTheory.T.exists_qkPoint_extension_of_divided_data L R hR t P iw s ε e hε hs hD (qkMk hB 0 (q.g - p₁.g) h0) rfl
  rw [qkExt_iff hB _ ha] at hr
  refine ⟨qkAdd hB p₀ r₀, ?_⟩
  rw [qkExt_iff hB _ ha, qkExt_qkAdd, ← hr, ← hp₁]
  apply qk_ext
  · show q.y = p₀.y + 0
    rw [hy, add_zero]
  · show q.g = p₁.g + (q.g - p₁.g)
    abel

theorem qkExt_equiv_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD σ p p' hpp'
  refine GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational R P.D l.M' (fun q => ?_) σ.toAlgHom p p' hpp'
  obtain ⟨q₀, hq⟩ := qkPt_rational L R hR t P iw s ε e hε hs hD q
  exact ⟨q₀, q, hq, qk_equiv_refl P.D.tau_bimult q⟩

end GlobalTheory.DivGalFix
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  atlas_forward_decl GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem torsRat_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → GlobalTheory.TChart.TorsRat t.G l.M' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD
  haveI : CharZero R := hR.2
  have hadm : AdmBase R (maximalIdeal R) := hR.1
  have hn : 1 ≤ l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  haveI := P.U.gen_hom
  refine GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed t.G t.G P.A P.U.gen (𝟙 _) (𝟙 _) l.M' P.U.gen_hom
    inferInstance inferInstance (Category.comp_id _) hn ?_
  intro σ x hx
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ t.G, y = x := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj t.G,
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ l.M' = 1 := by rw [hy0]; exact hx
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ l.M' = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A.A, a = h ≫ P.U.gen.hom := ⟨_, rfl⟩
  have ha : a ^ l.M' = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) l.M' hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨⟨p', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom l.M' hn p
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p' a a' hext ha').1 ((hT.1 p a).2 hp.symm)
  have heq := GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data L R hR t P iw s ε e hε hs hD σ p p' hext
  have haa : a' = a := ((hT.1 p' a').1 h2).trans (((hT.2.2.1 p p').2 heq).symm.trans hp)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app t.G).left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app t.G := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ P.U.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ P.U.gen.hom P.U.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  rw [hy0] at hyx
  simpa using hyx

end GlobalTheory.UCanon
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_torsion_rational_of_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → GlobalTheory.TChart.TorsRat t.G l.M' := by
  atlas_forward_decl GlobalTheory.UCanon.torsRat_of_divFrom
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsAway

theorem torsRat_away_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R) [IsDomain (Localization.Away f)] (G : Over (Sp R))
    [GrpObj G] (G' : Over (Sp (Localization.Away f))) [GrpObj G'] (π : G'.left ⟶ G.left),
    IsGrpPullback G' G (spMap (algebraMap R (Localization.Away f))) π → ∀ n : ℕ,
      GlobalTheory.TChart.TorsRat G n ↔ GlobalTheory.TChart.TorsRat G' n := by
  intro R _ _ f _ G _ G' _ π hπ n
  have hf : f ≠ 0 := by
    rintro rfl
    have : Subsingleton (Localization.Away (0 : R)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : R)) ⟨1, pow_one _⟩
    exact not_subsingleton (Localization.Away (0 : R)) this
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) := IsLocalization.injective _ hle
  constructor
  · exact GlobalTheory.TChart.AbLevel.torsRat_of_isGrpPullback _ hinj hπ
  · intro h K _ _ κ x hx
    letI : Algebra (Localization.Away f) (FractionRing R) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsScalarTower R (Localization.Away f) (FractionRing R) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsFractionRing (Localization.Away f) (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) (Localization.Away f)
        (FractionRing R)
    let e := FractionRing.algEquiv (Localization.Away f) (FractionRing R)
    let j : FractionRing (Localization.Away f) →+* FractionRing R := e.toAlgHom.toRingHom
    have hj : ∀ r : R, j (algebraMap _ (FractionRing (Localization.Away f)) (algebraMap R (Localization.Away f) r)) =
        algebraMap R (FractionRing R) r := by
      intro r
      exact (e.commutes _).trans (IsScalarTower.algebraMap_apply R (Localization.Away f) (FractionRing R) r).symm
    have hsq : spMap j ≫ jK (Localization.Away f) ≫ spMap (algebraMap R (Localization.Away f)) = jK R := by
      show spMap j ≫ spMap (algebraMap _ (FractionRing (Localization.Away f))) ≫ spMap (algebraMap R (Localization.Away f)) =
        spMap (algebraMap R (FractionRing R))
      rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      exact congrArg spMap (RingHom.ext hj)
    let T : Over (Sp (Localization.Away f)) := Over.mk (spMap (κ.comp j) ≫ jK (Localization.Away f))
    have hT : T.hom ≫ spMap (algebraMap R (Localization.Away f)) = spMap κ ≫ jK R := by
      show (spMap (κ.comp j) ≫ jK (Localization.Away f)) ≫ spMap (algebraMap R (Localization.Away f)) = _
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Category.assoc, hsq]
    let e0 : Over.mk (T.hom ≫ spMap (algebraMap R (Localization.Away f))) ⟶ Over.mk (spMap κ ≫ jK R) :=
      Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
    let x' := (GlobalTheory.ObjPull.pushEquiv hπ T).symm (e0 ≫ x)
    have hx' : x' ^ n = 1 := by
      simp only [x']
      rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]
    obtain ⟨y, hy⟩ := h K (κ.comp j) x' hx'
    have hyw : y.left ≫ G'.hom = jK (Localization.Away f) := Over.w y
    refine ⟨Over.homMk (spMap j ≫ y.left ≫ π) ?_, ?_⟩
    · show (spMap j ≫ y.left ≫ π) ≫ G.hom = jK R
      rw [Category.assoc, Category.assoc, hπ.1.w, ← Category.assoc y.left, hyw]
      exact hsq
    · show x.left = spMap κ ≫ spMap j ≫ y.left ≫ π
      have h1 : x'.left ≫ π = x.left :=
        (GlobalTheory.ObjPull.pushEquiv_symm_left hπ T (e0 ≫ x)).trans (Category.id_comp _)
      rw [← h1, hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      simp only [Category.assoc]

end GlobalTheory.TorsAway
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClsOpen

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.ClsOpen

open GlobalTheory.ClsOpen in

theorem GlobalTheory.clsOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (D' : Datum H) (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (C : Fam Xo c V) (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → θ.comp (iw.comp L.b) = C.b → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, θ (s (.inl i)) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L C.P.D.toPre C.P.oD (θ.comp iw) (fun k => θ (s k)) ε e → ∃ (y₁ : Sp (FractionRing R) ⟶ Xo.XF c) (yo : Sp (Localization.Away (∏ i, s (.inl i))) ⟶ Xo.XF c) (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, s (.inl i)))), y₁ ≫ pullback.snd _ _ = jK R ≫ spMap (iw.comp L.b) ∧ GlobalTheory.UPoinc.GenOf Xo c y₁ t₁ ∧ (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, s (.inl i))), g ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK R → g ≫ yo = y₁) ∧ κ ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y := by
  intro E _ _ _ H Dw l Xo c φ D' L R V _ _ _ _ _ _ hR hV C t₁ P₁ iw θ hθ hb m N s ε e₁ e hε hs hu hD₁ hD
  set f : R := ∏ i, s (.inl i) with hf_def
  have hθf : θ f ≠ 0 := by rw [hf_def, map_prod]; exact Finset.prod_ne_zero_iff.2 fun i _ => hs i
  have hf0 : f ≠ 0 := fun h => hθf (by rw [h, map_zero])
  have hsk : ∀ k, s k ≠ 0 := by
    rintro (i | j)
    · exact fun h => hs i (by rw [h, map_zero])
    · exact (hu j).ne_zero
  have hθk : ∀ k, θ (s k) ≠ 0 := by
    rintro (i | j)
    · exact hs i
    · exact ((hu j).map θ).ne_zero
  let A := Localization.Away f
  have hpow : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain A := IsLocalization.isDomain_localization hpow
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (Submonoid.powers f) A hR.1.1
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A (Submonoid.powers f) hpow
  have hψ := GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase L P₁.D.toPre P₁.oD iw s ε e₁ hD₁ f (by
    rintro (i | j)
    · exact ⟨1, by rw [pow_one, hf_def]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)⟩
    · exact ⟨0, (hu j).dvd⟩)
  obtain ⟨tO, ⟨mO⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap (algebraMap R A)) t₁
  obtain ⟨hpr, ham, hkt⟩ := GlobalTheory.T.isProper_relAmple_kTriv_of_trivialisations_generate R hR t₁ P₁ f hψ tO mO
  have htors : GlobalTheory.TChart.TorsRat tO.G l.M' :=
    (GlobalTheory.TorsAway.torsRat_away_iff R f t₁.G tO.G mO.φ mO.cart l.M').1 (GlobalTheory.T.genericFibre_torsion_rational_of_base L R hR t₁ P₁ iw s ε e₁ hε hsk hD₁)
  let K := FractionRing V
  have hunitK : IsUnit (((algebraMap V K).comp θ) f) := by
    rw [RingHom.comp_apply]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hθf)
  let g : A →+* K := IsLocalization.Away.lift f hunitK
  have hg : g.comp (algebraMap R A) = (algebraMap V K).comp θ := IsLocalization.lift_comp _
  let bA : c.F →+* A := (algebraMap R A).comp (iw.comp L.b)
  let incl := (IntermediateField.inclusion c.le).toRingHom
  have hgb : g.comp bA = (algebraMap V K).comp C.b := by
    show g.comp ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [← RingHom.comp_assoc, hg, RingHom.comp_assoc, hb]
  have E1 : spMap g ≫ spMap (algebraMap R A) = jK V ≫ spMap θ :=
    (spMap_comp' _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp' _ _))
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.LevelQuotRep.obj_pull_same Xo.univ (C.y ≫ pullback.fst _ _)
  have hsK : (C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap g ≫ spMap (bA.comp incl) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.y_over, spMap_comp' incl bA, ← Category.assoc,
      ← spMap_comp' bA g, hgb, spMap_comp']
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := (genOf_iff Xo c C.y C.t).1 C.gen
  obtain ⟨bc⟩ := GlobalTheory.T.exists_tripleMap_of_same_uniformised_coords L R V hR hV t₁ P₁ C.t C.P iw θ hθ s ε e₁ e hθk hD₁ hD
  obtain ⟨n₁⟩ := GlobalTheory.TraitOrder.cancel (Category.id_comp _) m₂ mK.toSABMap
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl bc m₁
  obtain ⟨n₃⟩ := GlobalTheory.TraitOrder.comp (Category.id_comp _) n₂ n₁
  obtain ⟨n₄⟩ := GlobalTheory.TraitOrder.cancel E1 mO n₃
  obtain ⟨o, ho, ⟨mo⟩⟩ := GlobalTheory.T.exists_unitaryModuliObject_spread_normal_domain Dw l c A bA tO hpr ham hkt htors K g _ oK hsK n₄
  obtain ⟨f₀, ⟨hf₀s, ⟨mf₀⟩⟩, -⟩ := Xo.rep (Sp A) (spMap (bA.comp incl)) inferInstance o
  have hf₀ : f₀ ≫ Xo.s = spMap bA ≫ spMap incl := by rw [hf₀s, spMap_comp']
  let yo : Sp A ⟶ Xo.XF c := pullback.lift f₀ (spMap bA) hf₀
  have hκ : spMap g ≫ yo = C.y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      obtain ⟨mk'⟩ := GlobalTheory.LevelQuotRep.obj_comp mo mf₀
      exact (Xo.rep (Sp K) _ inferInstance oK).unique ⟨by rw [Category.assoc, hf₀s, hsK], ⟨mk'⟩⟩ ⟨rfl, ⟨mK⟩⟩
    · rw [Category.assoc, pullback.lift_snd, C.y_over, ← spMap_comp', hgb, spMap_comp']
  have hunitR : IsUnit ((algebraMap R (FractionRing R)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf0)
  let jA : A →+* FractionRing R := IsLocalization.Away.lift f hunitR
  have hjA : jA.comp (algebraMap R A) = algebraMap R (FractionRing R) := IsLocalization.lift_comp _
  have hg₀ : spMap jA ≫ spMap (algebraMap R A) = jK R := by rw [← spMap_comp', hjA]
  have mo' : SABMap tO Xo.univ.t f₀ := ho ▸ mf₀.toSABMap
  refine ⟨spMap jA ≫ yo, yo, spMap g, ?_, ?_, ?_, E1, hκ⟩
  · rw [Category.assoc, pullback.lift_snd, ← hg₀, Category.assoc]
    show spMap jA ≫ spMap ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [spMap_comp']
  · refine (genOf_iff Xo c _ t₁).2 ?_
    obtain ⟨t', ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap jA) tO
    exact ⟨t', GlobalTheory.TraitOrder.comp hg₀ mO n,
      GlobalTheory.TraitOrder.comp (by rw [Category.assoc, pullback.lift_fst]) mo' n⟩
  · intro g' hg'
    obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
    have h2 : CommRingCat.ofHom (algebraMap R A) ≫ φ' = CommRingCat.ofHom (algebraMap R (FractionRing R)) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact hg')
    have h3 : φ'.hom = jA := IsLocalization.ringHom_ext (Submonoid.powers f)
      ((congrArg CommRingCat.Hom.hom h2).trans hjA.symm)
    have h4 : φ' = CommRingCat.ofHom jA := by ext1; exact h3
    rw [h4]
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classified_on_open_of_specialises_to_classified : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (D' : Datum H) (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (C : Fam Xo c V) (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → θ.comp (iw.comp L.b) = C.b → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, θ (s (.inl i)) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L C.P.D.toPre C.P.oD (θ.comp iw) (fun k => θ (s k)) ε e → ∃ (y₁ : Sp (FractionRing R) ⟶ Xo.XF c) (yo : Sp (Localization.Away (∏ i, s (.inl i))) ⟶ Xo.XF c) (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, s (.inl i)))), y₁ ≫ pullback.snd _ _ = jK R ≫ spMap (iw.comp L.b) ∧ GlobalTheory.UPoinc.GenOf Xo c y₁ t₁ ∧ (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, s (.inl i))), g ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK R → g ≫ yo = y₁) ∧ κ ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y := by
  atlas_forward_decl GlobalTheory.clsOpen
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

theorem sum_residue_smul_toCotangent {R : Type} [CommRing R] [IsLocalRing R] {Idx : Type} [Fintype Idx]
    (a : Idx → R) (y : Idx → R) (hy : ∀ i, y i ∈ maximalIdeal R) :
    ∑ i, residue R (a i) • (maximalIdeal R).toCotangent ⟨y i, hy i⟩ =
      (maximalIdeal R).toCotangent ⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ := by
  have h : (⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ : maximalIdeal R) =
      ∑ i, a i • (⟨y i, hy i⟩ : maximalIdeal R) := by
    ext; simp [smul_eq_mul]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]

end GlobalTheory.CohenChart

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

theorem exists_ringEquiv_chartRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    IsAdicComplete (maximalIdeal R) R → Nonempty (ℚ →+* R) → ∀ (m : ℕ) (t : Fin m → R),
    (∀ i, t i ∈ maximalIdeal R) →
    (∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R) →
    ∃ (k : Type) (_ : Field k) (e : ℕ) (σ : R ≃+* ChartRing k m e), ∀ i, σ (t i) = bdParam k m e i := by
  intro R _ _ hc hQ m t ht hind
  classical
  obtain ⟨q⟩ := hQ
  letI : Algebra ℚ (ResidueField R) := ((IsLocalRing.residue R).comp q).toAlgebra
  haveI : CharZero (ResidueField R) := algebraRat.charZero _
  haveI := hc
  obtain ⟨Λ, hF, hΛ⟩ := GlobalTheory.CohenRegular.exists_coefficientField_of_charZero R
  letI := hF.toField

  let v : Fin m → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩
  have hv : LinearIndependent (ResidueField R) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (R := R) (g j)
    have h1 : ∑ j, residue R (a j) • v j = 0 := by simpa [ha] using hg
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq_zero] at h1
    rw [← ha i, residue_eq_zero_iff]
    exact hind a h1 i
  set d := Module.finrank (ResidueField R) (CotangentSpace R) with hd
  have hmd : m ≤ d := by simpa using hv.fintype_card_le_finrank
  set W := Submodule.span (ResidueField R) (Set.range v) with hW
  have hWd : Module.finrank (ResidueField R) (CotangentSpace R ⧸ W) = d - m := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank (ResidueField R) W = m := by rw [finrank_span_eq_card hv]; simp
    omega
  let b := Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R ⧸ W) hWd
  choose w hw using fun j => W.mkQ_surjective (b j)
  choose s hs using fun j => (maximalIdeal R).toCotangent_surjective (w j)
  let x : Fin m ⊕ Fin (d - m) → R := Sum.elim t (fun j => (s j : R))
  have hx : ∀ j, x j ∈ maximalIdeal R := by
    rintro (j | j)
    exacts [ht j, (s j).2]
  let g : Fin m ⊕ Fin (d - m) → CotangentSpace R := fun j => (maximalIdeal R).toCotangent ⟨x j, hx j⟩
  set U := Submodule.span (ResidueField R) (Set.range g) with hU
  have hUtop : ∀ y : CotangentSpace R, y ∈ U := by
    intro y
    have hWU : W ≤ U := Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)
    have hwU : ∀ j, w j ∈ U := fun j => Submodule.subset_span ⟨Sum.inr j, by simp [g, x, hs]⟩
    have h1 : W.mkQ (y - ∑ j, b.repr (W.mkQ y) j • w j) = 0 := by
      simp only [map_sub, map_sum, map_smul, hw, b.sum_repr, sub_self]
    have h2 : y - ∑ j, b.repr (W.mkQ y) j • w j ∈ W := by
      rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at h1
    have h3 : ∑ j, b.repr (W.mkQ y) j • w j ∈ U := U.sum_mem fun j _ => U.smul_mem _ (hwU j)
    have := U.add_mem (hWU h2) h3
    simpa using this

  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  haveI : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  let f : ChartRing Λ m (d - m) →ₐ[Λ] R := GlobalTheory.mvEvalAdic Λ (maximalIdeal R) x hx
  have hfX : ∀ j, f (X j) = x j := fun j => GlobalTheory.mvEvalAdic_X (A := Λ) (maximalIdeal R) x hx j
  have hfC : ∀ a : Λ, f (C a) = a := fun a => GlobalTheory.mvEvalAdic_C (A := Λ) (maximalIdeal R) x hx a
  have hle : ∀ g ∈ maximalIdeal (ChartRing Λ m (d - m)), f g ∈ maximalIdeal R := by
    intro g hg
    have h4 := GlobalTheory.algHom_sub_constantCoeff_mem f (K := maximalIdeal R) (fun j => by rw [hfX]; exact hx j) g
    have h5 := GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hXm : ∀ j, (X j : ChartRing Λ m (d - m)) ∈ maximalIdeal (ChartRing Λ m (d - m)) := fun j =>
    GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp)
  have hloc : IsLocalHom (f : ChartRing Λ m (d - m) →+* R) := ⟨fun g hg => by
    by_contra hn
    exact (hle g hn) hg⟩
  have hres : ∀ z : R, ∃ r, z - (f : ChartRing Λ m (d - m) →+* R) r ∈ maximalIdeal R := by
    intro z
    obtain ⟨a, ha, h⟩ := hΛ z
    exact ⟨C ⟨a, ha⟩, by simpa [hfC] using h⟩
  have hcot : maximalIdeal R ≤ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) ⊔
      maximalIdeal R ^ 2 := by
    intro z hz
    obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField R)).1
      (hUtop ((maximalIdeal R).toCotangent ⟨z, hz⟩))
    choose a ha using fun j => residue_surjective (R := R) (c j)
    have h1 : ∑ j, residue R (a j) • g j = (maximalIdeal R).toCotangent ⟨z, hz⟩ := by simpa [ha] using hc'
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq] at h1
    have h2 : ∑ j, a j * x j ∈ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) :=
      sum_mem fun j _ => Ideal.mul_mem_left _ _ (by rw [← hfX]; exact Ideal.mem_map_of_mem _ (hXm j))
    have h3 : z = ∑ j, a j * x j + (z - ∑ j, a j * x j) := by ring
    rw [h3]
    refine Submodule.add_mem_sup h2 ?_
    have : (z - ∑ j, a j * x j) = -((∑ j, a j * x j) - z) := by ring
    rw [this]
    exact neg_mem h1
  have hcA : IsAdicComplete (maximalIdeal (ChartRing Λ m (d - m))) (ChartRing Λ m (d - m)) :=
    GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv
      (MvPowerSeries.renameEquiv Λ finSumFinEquiv.symm).toRingEquiv
      (h := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries Λ (m + (d - m)))
  have hsurj : Function.Surjective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.LocalSurj.surjective_of_residue_of_cotangent _ R _ hcA hloc hres hcot
  letI : Algebra (ChartRing Λ m (d - m)) R := (f : ChartRing Λ m (d - m) →+* R).toAlgebra
  haveI : Module.Finite (ChartRing Λ m (d - m)) R :=
    Module.Finite.of_surjective (Algebra.linearMap (ChartRing Λ m (d - m)) R) hsurj
  have hdA : ringKrullDim (ChartRing Λ m (d - m)) = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF, Nat.card_sum,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, zero_add]
  have hdR : ringKrullDim R = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance, ← hd]
    have hmd' : m + (d - m) = d := by omega
    rw [hmd']
  have hinj : Function.Injective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq hdA hdR
  let φ := RingEquiv.ofBijective (f : ChartRing Λ m (d - m) →+* R) ⟨hinj, hsurj⟩
  refine ⟨Λ, inferInstance, d - m, φ.symm, fun i => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  show t i = f (X (Sum.inl i))
  rw [hfX]
  rfl

end GlobalTheory.CohenChart
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_powerSeries_prescribed_parameters : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → Nonempty (ℚ →+* R) → ∀ (m : ℕ) (t : Fin m → R), (∀ i, t i ∈ maximalIdeal R) → (∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R) → ∃ (k : Type) (_ : Field k) (e : ℕ) (σ : R ≃+* ChartRing k m e), ∀ i, σ (t i) = bdParam k m e i := by
  atlas_forward_decl GlobalTheory.CohenChart.exists_ringEquiv_chartRing
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isComplAt_ringEquiv_comp {A R S : Type} [CommRing A] [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (ψ : A →+* R) (σ : R ≃+* S) (h : IsComplAt ψ) : IsComplAt ((σ : R →+* S).comp ψ) := by
  obtain ⟨hN, hC, hF, hM, hR⟩ := h
  have hmap : (maximalIdeal R).map σ = maximalIdeal S := map_ringEquiv_maximalIdeal σ
  have hcomap : (maximalIdeal S).comap (σ : R →+* S) = maximalIdeal R := by
    rw [← hmap]; exact Ideal.comap_map_of_bijective _ σ.bijective
  refine ⟨isNoetherianRing_of_ringEquiv R σ, ?_, ?_, ?_, ?_⟩
  · haveI := hC
    rw [← hmap, IsAdicComplete.congr_ringEquiv]; exact hC
  · exact RingHom.Flat.comp hF (RingHom.Flat.of_bijective σ.bijective)
  · rw [← Ideal.comap_comap, hcomap, ← Ideal.map_map, hM]; exact hmap
  · intro s
    obtain ⟨a, b, hb, hab⟩ := hR (σ.symm s)
    refine ⟨a, b, ?_, ?_⟩
    · simpa using hb.map (σ : R →+* S)
    · have : (σ : R →+* S) (σ.symm s * ψ b - ψ a) ∈ maximalIdeal S := by
        rw [← Ideal.mem_comap, hcomap]; exact hab
      simpa using this

theorem exists_chartRing_factor : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W], Nonempty (ℚ →+* W) → ∀ (m N : ℕ) (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial (Fin m ⊕ Fin N) W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → (∀ i, ψV (MvPolynomial.X (.inl i)) ∈ maximalIdeal V) → ∃ (k : Type) (_ : Field k) (e : ℕ) (ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* ChartRing k m e) (θ : ChartRing k m e →+* V), GlobalTheory.TChart.IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) ∧ ∀ i, ψ (MvPolynomial.X (.inl i)) = bdParam k m e i := by
  intro W _ _ hQ m N V _ _ hV ψV hCV hXV
  obtain ⟨R, _, _, _, ψ, θ, hψ, hθ, hθψ, hψC⟩ :=
    exists_complAt_factor_of_isAdicComplete W (Fin m ⊕ Fin N) V hV ψV hCV
  obtain ⟨hreg, -⟩ := isRegularLocalRing_and_isDomain_of_isComplAt W (Fin m ⊕ Fin N) R ψ hψ hψC
  haveI := hreg
  let t : Fin m → R := fun i => ψ (MvPolynomial.X (.inl i))
  have ht : ∀ i, t i ∈ maximalIdeal R := by
    intro i
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (θ (t i)) := hu.map θ
    have h2 : θ (t i) = ψV (MvPolynomial.X (.inl i)) := by
      show (θ.comp ψ) _ = _; rw [hθψ]
    rw [h2] at h1
    exact (mem_maximalIdeal _).1 (hXV i) h1
  have hind : ∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R := by
    intro a ha i
    exact cotangent_indep_of_isComplAt W (Fin m ⊕ Fin N) R ψ hψ hψC m (Function.Embedding.inl) ht a
      (Ideal.mem_sup_left ha) i
  have hQR : Nonempty (ℚ →+* R) := ⟨(ψ.comp MvPolynomial.C).comp hQ.some⟩
  obtain ⟨k, _, e, σ, hσ⟩ := GlobalTheory.T.exists_ringEquiv_powerSeries_prescribed_parameters R hψ.2.1 hQR m t ht hind
  refine ⟨k, inferInstance, e, (σ : R →+* ChartRing k m e).comp ψ, θ.comp (σ.symm : ChartRing k m e →+* R),
    isComplAt_ringEquiv_comp ψ σ hψ, inferInstance, ?_, ?_, ?_⟩
  · rw [← hθψ]; ext x <;> simp
  · show IsLocalHom ((σ : R →+* ChartRing k m e).comp (ψ.comp MvPolynomial.C))
    infer_instance
  · intro i; exact hσ i

end GlobalTheory.TChart
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toricChartRing_factorisation_localHom : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W], Nonempty (ℚ →+* W) → ∀ (m N : ℕ) (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial (Fin m ⊕ Fin N) W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → (∀ i, ψV (MvPolynomial.X (.inl i)) ∈ maximalIdeal V) → ∃ (k : Type) (_ : Field k) (e : ℕ) (ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* ChartRing k m e) (θ : ChartRing k m e →+* V), GlobalTheory.TChart.IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) ∧ ∀ i, ψ (MvPolynomial.X (.inl i)) = bdParam k m e i := by
  atlas_forward_decl GlobalTheory.TChart.exists_chartRing_factor
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem injective_of_flat_of_isDomain {A R : Type} [CommRing A] [IsDomain A] [CommRing R] [Nontrivial R] (ψ : A →+* R)
    (h : ψ.Flat) : Function.Injective ψ := by
  letI := ψ.toAlgebra
  haveI : Module.Flat A R := h
  refine (injective_iff_map_eq_zero ψ).2 fun a ha => ?_
  by_contra h0
  have hr := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero h0)
  have h1 : a • (1 : R) = a • (0 : R) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_zero, _root_.mul_one]; exact ha
  exact one_ne_zero (hr h1)

theorem exists_canon_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (θ : ChartRing k m e →+* V), Nonempty (Canon C₁) ∧ (∃ hm : C₁.m = m, ∀ i, C₁.s i = bdParam k m e (Fin.cast hm i)) ∧ IsLocalHom θ ∧ Through C C₁ θ := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C hn
  obtain ⟨D', L, θ₀, N, ε, e, s, hp, hq, hθ₀, hb, hδ, hs, hu, hdiv⟩ := GlobalTheory.T.degeneratingFamily_data_from_base_algClosed_residue Xo c φ V hV hk C hn
  have hC₀ : (MvPolynomial.eval₂Hom θ₀ s).comp MvPolynomial.C = θ₀ := RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ _
  have hsm : ∀ i, s (.inl i) ∈ maximalIdeal V := fun i => by
    obtain ⟨u, hu⟩ := (hs i).symm
    rw [← hu]; exact Ideal.mul_mem_right _ _ (C.s_mem i)
  have hs0 : ∀ i, s (.inl i) ≠ 0 := fun i h => C.s_ne_zero i ((hs i).eq_zero_iff.1 h)
  obtain ⟨k, _, e', ψ, θ, hcompl, hθ, hθψ, hψ, hbd⟩ := GlobalTheory.T.exists_toricChartRing_factorisation_localHom L.W ⟨L.b.comp (algebraMap ℚ c.F)⟩ C.m N V hV.1.2.2.2
    (MvPolynomial.eval₂Hom θ₀ s) (by rw [hC₀]; exact hθ₀) (fun i => by rw [MvPolynomial.eval₂Hom_X']; exact hsm i)
  have hθX : ∀ j, θ (ψ (MvPolynomial.X j)) = s j := fun j => by
    rw [← RingHom.comp_apply, hθψ, MvPolynomial.eval₂Hom_X']
  have hθC : θ.comp (ψ.comp MvPolynomial.C) = θ₀ := by rw [← RingHom.comp_assoc, hθψ, hC₀]
  have hinj : Function.Injective (ψ.comp MvPolynomial.C) :=
    (injective_of_flat_of_isDomain ψ hcompl.2.2.1).comp (MvPolynomial.C_injective _ _)
  let b₁ : c.F →+* ChartRing k C.m e' := (ψ.comp MvPolynomial.C).comp L.b
  have hR : GlobalTheory.Mum.Base (ChartRing k C.m e') :=
    ⟨GlobalTheory.MumfordChart.admissibleBase_chartRing k C.m e', (b₁.charZero_iff b₁.injective).1 inferInstance⟩
  have htor : ∀ j, IsUnit (ψ (MvPolynomial.X (.inr j))) := fun j => hθ.map_nonunit _ (by rw [hθX]; exact hu j)
  have hmem : ∀ i, ψ (MvPolynomial.X (.inl i)) ∈ maximalIdeal (ChartRing k C.m e') := fun i hi =>
    hsm i (by rw [← hθX]; exact hi.map θ)
  have hne : ∀ i, θ (ψ (MvPolynomial.X (.inl i))) ≠ 0 := fun i => by rw [hθX]; exact hs0 i
  have hval : ∀ i y, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y = C.δ i (e.symm y) (e.symm y) := fun i y => by
    rw [hδ i]
    show _ = (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm y)) (e (e.symm y))
    rw [e.apply_symm_apply]
  have hnn : ∀ i y, 0 ≤ (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun i y => by
    rw [hval]; exact C.cone.nonneg i _
  have hpos : ∀ y, y ≠ 0 → 0 < ∑ i, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun y hy => by
    obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal V).ne_top (y := e.symm y) (by simpa using hy)
    refine Finset.sum_pos' (fun j _ => hnn j y) ⟨i, Finset.mem_univ _, ?_⟩
    rw [hval]
    exact pos_of_mul_pos_left (by rw [mul_comm]; exact hi) (Int.natCast_nonneg l.M')
  obtain ⟨t₁, P₁, e₁, hdiv₁, hmono⟩ := GlobalTheory.T.mumford_family_from_regular_base_coordinates L (ChartRing k C.m e') hR (ψ.comp MvPolynomial.C) hinj C.m N
    (fun j => ψ (MvPolynomial.X j)) (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) (fun j => (ε j).2)
    (fun i => ⟨hmem i, fun h => hne i (by rw [h, map_zero])⟩) htor hnn hpos e.injective.nontrivial
  obtain ⟨y₁, yo, κ, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.classified_on_open_of_specialises_to_classified Xo c φ D' L (ChartRing k C.m e') V hR hV C.toFam t₁ P₁
    (ψ.comp MvPolynomial.C) θ hθ (by rw [← RingHom.comp_assoc, hθC, hb]) C.m N (fun j => ψ (MvPolynomial.X j))
    (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) e₁ e (fun j => (ε j).2) hne htor hdiv₁
    (by rw [hθC, funext hθX]; exact hdiv)
  have hrk : Module.finrank (𝓞 E) P₁.D.toPre.X = Module.finrank (𝓞 E) C.P.D.toPre.X := (e₁.trans e.symm).finrank_eq
  have hcone : IsCone H.bar φ fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
    have h := C.cone.pull_equiv (e₁.trans e.symm)
    have he : (fun i => pull (e₁.trans e.symm).toLinearMap (C.δ i)) =
        fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
      funext i
      rw [hδ i]
      refine LinearMap.ext₂ fun a b => ?_
      show (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm (e₁ a))) (e (e.symm (e₁ b))) = _
      rw [e.apply_symm_apply, e.apply_symm_apply]
      rfl
    rwa [he] at h
  let C₁ : MonoFam Xo c φ (ChartRing k C.m e') :=
    ⟨⟨b₁, t₁, P₁, y₁, h₁, h₂⟩, C.m, fun i => ψ (MvPolynomial.X (.inl i)), hmem,
      fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X), hcone, hrk.le.trans C.rank, hmono⟩
  exact ⟨k, _, C.m, e', C₁, θ, ⟨⟨D', by rw [← hp, ← hrk], by rw [← hq, ← hrk], L, N, ε, e₁, fun _ => rfl, ψ, hcompl, hψ,
    rfl, fun _ => rfl, htor, hdiv₁⟩⟩, ⟨rfl, hbd⟩, hθ, yo, κ, h₃, h₄, h₅⟩

end GlobalTheory.UCanon
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_family_through_degenerating_family : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (θ : ChartRing k m e →+* V), Nonempty (Canon C₁) ∧ (∃ hm : C₁.m = m, ∀ i, C₁.s i = bdParam k m e (Fin.cast hm i)) ∧ IsLocalHom θ ∧ Through C C₁ θ := by
  atlas_forward_decl GlobalTheory.UCanon.exists_canon_through
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem spMap_isDominant_of_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : IsDominant (spMap f) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hf]
    exact bot_le)⟩

theorem spMap_ext_of_injective {A B : Type} [CommRing A] [IsDomain A] [CommRing B] {S : Scheme.{0}} [S.IsSeparated]
    (f : A →+* B) (hf : Function.Injective f) {a b : Sp A ⟶ S} (h : spMap f ≫ a = spMap f ≫ b) : a = b := by
  haveI := spMap_isDominant_of_injective f hf
  exact ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (spMap f) h

theorem isSeparated_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    X.IsSeparated := by
  obtain ⟨N, ci, hci, hcis⟩ := h
  haveI := hci
  have : IsSeparated f := by
    rw [← hcis, PSpace.str]
    infer_instance
  exact ⟨by rw [← terminal.comp_from f]; infer_instance⟩

end GlobalTheory.UCanon

namespace GlobalTheory.UCanon

theorem exists_taut_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), Nontrivial C.P.D.toPre.X → C.y ≫ j = jK V ≫ ξV → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S) (θ : ChartRing k m e →+* V), IsTautB C₁ ∧ C₁.y ≫ j = jK _ ≫ ξ ∧ IsLocalHom θ ∧ spMap θ ≫ ξ = ξV := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep V _ _ _ hB hac C ξV hnt hCV
  obtain ⟨k, hk, m, e, C₁, θ, ⟨hcan⟩, hpar, hθ, hthr⟩ := GlobalTheory.T.exists_canonical_family_through_degenerating_family Xo c φ V hB hac C hnt
  letI := hk
  have hT : IsTautB C₁ := GlobalTheory.T.canonicalFamily_isPointRigid_tautologicalChart Xo c φ hpq hpf hns C₁ hcan hpar
  obtain ⟨ξ, hξ⟩ := GlobalTheory.UChart.taut_exists_map Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C₁ hT.1
  haveI : S.IsSeparated := isSeparated_of_projOver hU.2.2.2.2.1.2.1
  refine ⟨k, hk, m, e, C₁, ξ, θ, hT, hξ, hθ, ?_⟩
  obtain ⟨yo, κ, hgen, hκ, hκy⟩ := hthr

  obtain ⟨hm, hs⟩ := hpar
  have hne : (∏ i, C₁.s i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [hs i]
    exact bdParam_ne_zero k m e _
  set L := Localization.Away (∏ i, C₁.s i)
  have hle : Submonoid.powers (∏ i, C₁.s i) ≤ nonZeroDivisors (ChartRing k m e) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hne
  haveI : IsDomain L := IsLocalization.isDomain_localization hle
  have hu : IsUnit (algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) (∏ i, C₁.s i)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hne)
  let gR : L →+* FractionRing (ChartRing k m e) := IsLocalization.Away.lift (∏ i, C₁.s i) hu
  have hgR : gR.comp (algebraMap (ChartRing k m e) L) = algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) :=
    IsLocalization.Away.lift_comp (∏ i, C₁.s i) hu
  have hinj : Function.Injective gR := by
    refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
    rw [(IsLocalization.injective L hle).eq_iff, (IsFractionRing.injective (ChartRing k m e) (FractionRing (ChartRing k m e))).eq_iff]
  have hg : spMap gR ≫ spMap (algebraMap (ChartRing k m e) L) = jK (ChartRing k m e) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgR]

  have hopen : spMap (algebraMap (ChartRing k m e) L) ≫ ξ = yo ≫ j := by
    refine spMap_ext_of_injective gR hinj ?_
    rw [← Category.assoc, hg, ← hξ, ← Category.assoc, hgen _ hg]
  refine spMap_ext_of_injective (algebraMap V (FractionRing V)) (IsFractionRing.injective _ _) ?_
  change jK V ≫ _ = jK V ≫ _
  rw [← Category.assoc, ← hκ, Category.assoc, hopen, ← Category.assoc, hκy, hCV]

end GlobalTheory.UCanon
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tautological_chart_versality : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), Nontrivial C.P.D.toPre.X → C.y ≫ j = jK V ≫ ξV → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S) (θ : ChartRing k m e →+* V), IsTautB C₁ ∧ C₁.y ≫ j = jK _ ≫ ξ ∧ IsLocalHom θ ∧ spMap θ ≫ ξ = ξV := by
  atlas_forward_decl GlobalTheory.UCanon.exists_taut_through
end
