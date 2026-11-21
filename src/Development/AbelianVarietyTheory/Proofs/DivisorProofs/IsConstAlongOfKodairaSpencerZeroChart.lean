import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorCommutingPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaud
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisOfIntFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueAtPolarizedFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsSymbolZeroTorsionPointsHorizontal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfSymmetric
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialDegenerationUnitPartExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolZeroEqConnection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleSectionUnitAtClosedPointTorusChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueAtEqUnitMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomial

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_raynaudTangent_invariantFields : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  first | exact @GlobalTheory.RayBasis.exists_basis_isInv | exact GlobalTheory.RayBasis.exists_basis_isInv | (intros; apply GlobalTheory.RayBasis.exists_basis_isInv <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_unique_at_polarized_fieldPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (K : Type) [Field K] [CharZero K] (φ : Γ(X, U.1) →+* K) (P₀ : PolAV (Sp K)) (m : P₀.A.left ⟶ t.G.left), ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ V → IsGrpPullback P₀.A t.G (spMap φ ≫ chart U) m → LBIso P₀.L (t.PP.L.pull m) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(X, U.1)), IsKS t V U v D Θ → IsKS t V U v D Θ' → φ.mapMatrix Θ = φ.mapMatrix Θ' := by
  first | exact @GlobalTheory.KSPtUniq.isKS_unique_at_point | exact GlobalTheory.KSPtUniq.isKS_unique_at_point | (intros; apply GlobalTheory.KSPtUniq.isKS_unique_at_point <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartKSUniq

theorem isKS_unique_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤)), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ' → Θ = Θ' := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _ n v hv hb D Θ Θ' h h'
  haveI : CharZero (ChartRing k m d) :=
    charZero_of_injective_algebraMap (R := k) (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))
  haveI : CharZero (FractionRing (ChartRing k m d)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d)))
  let φ : Γ(Sp (ChartRing k m d), ⊤) →+* FractionRing (ChartRing k m d) :=
    (algebraMap (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom
  have hφ : Function.Injective φ := by
    exact (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).commRingCatIsoToRingEquiv.injective
  have hx : spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) = jK (ChartRing k m d) := by
    show spMap φ ≫ (isAffineOpen_top (Sp (ChartRing k m d))).fromSpec = _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp [φ]
  set R := ChartRing k m d with hRdef
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) :=
    GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have hf : (∏ i, bdParam k m d i : R) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ h0 => by
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
      simp [bdParam, MvPowerSeries.coeff_X] at this
  have hV : ⊤ ≤ (spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ
      (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, bdParam k m d i)) := by
    intro p _
    change (spMap φ) p ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen _
    rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen]
    show PrimeSpectrum.comap φ p ∈ PrimeSpectrum.basicOpen _
    rw [PrimeSpectrum.mem_basicOpen]
    show _ ∉ Ideal.comap φ p.asIdeal
    haveI := p.isPrime
    rw [Ideal.mem_comap, Ideal.eq_bot_of_prime p.asIdeal, Ideal.mem_bot]
    intro h0
    apply hf
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_zero, ← h0]
    show _ = algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom _))
    rw [Iso.inv_hom_id_apply]
  have key := GlobalTheory.T.kodairaSpencer_unique_at_polarized_fieldPoint E H (Sp R) t _ (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) n v hv hb
    (FractionRing R) φ P.A _ hV (by rw [hx]; exact gpG) hL _ Θ Θ' h h'
  ext a b
  exact hφ (congrFun₂ key a b)

end GlobalTheory.ChartKSUniq
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_unique_over_chart_abelian_locus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤)), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ' → Θ = Θ' := by
  atlas_forward_decl GlobalTheory.ChartKSUniq.isKS_unique_chart
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSZeroMod

theorem intDer {A : Type} [CommRing A] (inst : Algebra ℤ A) (D : @Derivation ℤ A A _ _ _ inst _ _) :
    ∃ D' : @Derivation ℤ A A _ _ _ (Ring.toIntAlgebra A) _ _, ⇑D' = ⇑D := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact ⟨D, rfl⟩

theorem exists_basis_isKS_symbol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vY : Module.Basis (Fin n) (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vY a) (dd a)) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∃ v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) ∧ IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) (h.Θ.map (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab Y n vY dd hdd D hD h hb hdef
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) h
    simp [MvPowerSeries.coeff_X] at this
  choose v' hv' using fun a => GlobalTheory.ChartKSBracket.tanPt E H (ChartRing k m d) t P Y (vY a)
  obtain ⟨b, hbv⟩ := GlobalTheory.T.uniformisedTangentBasis_of_raynaudBasis E H (ChartRing k m d) t P Y n vY v' hv'
  have hx : spMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom ≫ 𝟙 (Sp (ChartRing k m d)) =
      chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) := by
    rw [Category.comp_id, chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    rfl
  obtain ⟨b', hb'⟩ := GlobalTheory.TotalFrame.exists_basis_map b _ hx
  have ev : (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) ≫ (tv (v' a)).left) =
      fun a => (tv (b' a)).left := funext fun a => by rw [hb', hbv]
  refine ⟨fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) ≫ (tv (v' a)).left,
    fun a => GlobalTheory.ChartKSBracket.isTanAtG_tv E H _ t (v' a), fun w hw => ?_, ?_⟩
  · rw [ev]
    refine ⟨b'.repr (GlobalTheory.LieMet.tanOf hw), (GlobalTheory.LieMet.isComb_iff _ _ (GlobalTheory.LieMet.tanOf hw)).2 (b'.sum_repr _).symm,
      fun a ha => ?_⟩
    rw [(GlobalTheory.LieMet.isComb_iff _ _ (GlobalTheory.LieMet.tanOf hw)).1 ha, Module.Basis.repr_sum_self]
  · obtain ⟨D', hD'⟩ := intDer _ D
    revert h
    rw [← hD']
    intro h hb hdef
    exact GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud E H (ChartRing k m d) t P m (bdParam k m d) gam hmon hne hab Y n vY dd hdd v' hv' D' h hb hdef

set_option maxHeartbeats 1600000 in

theorem symbol_mem_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab n v hv hcomb Y n' v' dd hdd D q hq h hb hdef Θ hΘ hm
  letI := H.starRing
  have hD : ∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := fun i => by
    rw [hq i]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  obtain ⟨w, hw, hwb, hks⟩ := exists_basis_isKS_symbol E H k m d t P gam hmon hli hab Y n' v' dd hdd D hD h hb hdef
  choose C hC using fun c => (hwb (v c) (hv c)).exists
  have hks' := GlobalTheory.KSFrameChange.isKS_frame_change E H (Sp (ChartRing k m d)) t
    ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i)))
    (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) n n' v w (Matrix.of C)
    (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ hv hw hC hΘ
  have heq := GlobalTheory.T.kodairaSpencer_matrix_unique_over_chart_abelian_locus E H k m d t P gam hmon hli hab n' w hw hwb D _ _ hks' hks
  intro a b
  have e := congrArg (fun M => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (M a b)) heq
  simp only [Matrix.map_apply, Iso.inv_hom_id_apply] at e
  rw [← e, Matrix.mul_apply, map_sum]
  refine Ideal.sum_mem _ fun c _ => ?_
  rw [map_mul, Matrix.mul_apply, map_sum, Finset.sum_mul]
  refine Ideal.sum_mem _ fun e' _ => ?_
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hm e' c))

end GlobalTheory.KSZeroMod
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_symbol_mem_maximalIdeal_of_kodairaSpencer_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d) := by
  atlas_forward_decl GlobalTheory.KSZeroMod.symbol_mem_maximalIdeal
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Heat.AbConstAlong

theorem abelian_part_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) :=
  GlobalTheory.Heat.AbConst.abelian_part_const

end GlobalTheory.Heat.AbConstAlong
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_constant_heat_operator_symbol_in_maximal_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) := by
  atlas_forward_decl GlobalTheory.Heat.AbConstAlong.abelian_part_const
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymSpread

theorem inv_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

end GlobalTheory.SymSpread
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ConstDefSym

open GlobalTheory.CechPic

theorem lbIso_pull_of_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : Type) [Field k] [CharZero k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (Q.P.L.pull π₁) (Q.P.L.pull π₂) := by
  intro R _ _ Q k _ _ ρ B' _ π₁ π₂ h₁ h₂ hfib

  let ρ₀ : R →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ
  let A₀ : Over (Sp k) := (Over.pullback (spMap ρ₀)).obj Q.P.A
  letI : GrpObj A₀ := Functor.grpObjObj
  have hj : IsGrpPullback A₀ Q.P.A (spMap ρ₀) (pullback.fst Q.P.A.hom (spMap ρ₀)) := isGrpPullback_pullback Q.P.A (spMap ρ₀)
  have ec : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have h₂' : IsGrpPullback B' Q.P.A (spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀) π₂ := h₂.congr ec rfl
  let q : B'.left ⟶ A₀.left := hj.1.lift π₂ (B'.hom ≫ spMap (algebraMap k (DualNumber k)))
    (by rw [h₂'.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst Q.P.A.hom (spMap ρ₀) = π₂ := hj.1.lift_fst _ _ _
  have hq₂ : q ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) := hj.1.lift_snd _ _ _
  have hq : IsGrpPullback B' A₀ (spMap (algebraMap k (DualNumber k))) q :=
    IsGrpPullback.cancel hj (h₂'.congr rfl hq₁.symm) hq₂
  have eid : GlobalTheory.DeRham.epsRed k ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [GlobalTheory.DeRham.epsRed, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of k)
    ext x
    simp
  let i : A₀.left ⟶ B'.left := hq.1.lift (𝟙 _) (A₀.hom ≫ GlobalTheory.DeRham.epsRed k)
    (by rw [Category.id_comp, Category.assoc, eid, Category.comp_id])
  have e : i ≫ q = 𝟙 _ := hq.1.lift_fst _ _ _
  have hi₂ : i ≫ B'.hom = A₀.hom ≫ GlobalTheory.DeRham.epsRed k := hq.1.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A₀).hom := inferInstanceAs (IsMonHom (𝟙 A₀))
  have hi : IsGrpPullback A₀ B' (GlobalTheory.DeRham.epsRed k) i :=
    IsGrpPullback.cancel hq ((isGrpPullback_of_iso (Iso.refl A₀)).congr eid.symm (by rw [e]; rfl)) hi₂
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb hj

  have hL := Q.P.isLB
  have hsymA : pull (GrpObj.inv : Q.P.A ⟶ Q.P.A).left (cls Q.P.L hL) = cls Q.P.L hL := by
    have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨Q.sym, Q.sym_gen⟩
    rw [cls_linComb hL] at h0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul,
      pull_id] at h0
    exact sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h0)
  have key : ∀ {f : Sp (DualNumber k) ⟶ Sp R} (π : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A f π →
      LBIso ((Q.P.L.pull π).pull (GrpObj.inv : B' ⟶ B').left) (Q.P.L.pull π) := by
    intro f π hπ
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _)]
    show pull _ (pull π (cls Q.P.L hL)) = pull π (cls Q.P.L hL)
    rw [← pull_comp, GlobalTheory.SymSpread.inv_comp_of_isGrpPullback hπ, pull_comp, hsymA]
  have hfib' : i ≫ π₁ = i ≫ π₂ := hfib A₀.left i A₀.hom hi₂
  have hclosed : LBIso ((Q.P.L.pull π₁).pull i) ((Q.P.L.pull π₂).pull i) := by
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)]
    show pull i (pull π₁ (cls Q.P.L hL)) = pull i (pull π₂ (cls Q.P.L hL))
    rw [← pull_comp, ← pull_comp, hfib']
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric k A₀ B' i q hA₀ hi hq e _ _ (pull_isLB hL _) (pull_isLB hL _)
    (key π₁ h₁) (key π₂ h₂) hclosed

end GlobalTheory.ConstDefSym
end
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTauZero

theorem exists_isUnitTau_zero_val_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  intro E _ _ _ H k _ _ m d t P gam mu
  have hF : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim
      (K' := Fin 4) ![(P.D.toPre.c (mu + 0)).left, (P.D.toPre.c mu).left, (P.D.toPre.c 0).left, (P.D.toPre.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [add_zero, Finset.univ_eq_empty, Finset.prod_empty, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    simp [Matrix.vecHead, Matrix.vecTail]
  obtain ⟨τ₀, hτ, hv⟩ := exists_gen P.D.toPre.P.isLB hF (LB.oneGen P.D.toPre.P.L) (LB.isGen_oneGen _)
  have h1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨τ₀, ⟨hτ, 1, ?_, fun zz J hJ => ?_⟩, h1⟩
  · simp
  · have hB : P.D.toPre.TauBimult := P.D.tau_bimult
    rw [h1 _ _ zz J hJ, _root_.mul_one]
    have vτ : val (P.D.toPre.tau mu 0) (𝟙 _) zz J =
        val (P.D.toPre.psi (mu + 0)) (𝟙 _) zz J * (val (P.D.toPre.psi mu) (𝟙 _) zz J)⁻¹ *
          (val (P.D.toPre.psi 0) (𝟙 _) zz J)⁻¹ * (val P.D.toPre.rigK (𝟙 _) zz J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have vρ : val P.D.toPre.rigK (𝟙 _) zz J = val P.D.toPre.rig (jK _) zz J := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    have hp : ∀ a : P.D.toPre.X, a = mu → val (P.D.toPre.psi a) (𝟙 _) zz J = val (P.D.toPre.psi mu) (𝟙 _) zz J := by
      rintro a rfl; rfl
    have h0 := GlobalTheory.PsiZero.val_psi_zero hB hJ
    have hu : unitOn (1 : (FractionRing (ChartRing k m d))ˣ) = 1 := map_one _
    rw [vτ, hp _ (add_zero mu), h0, vρ, hu, map_one, mul_inv_cancel, _root_.one_mul, inv_inv, mul_inv_cancel]

end GlobalTheory.UnitTauZero
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitPartPeriodTau_zero_value_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  atlas_forward_decl GlobalTheory.UnitTauZero.exists_isUnitTau_zero_val_one
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

open InhTate

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem monomial_eq_of_mul_unit {W : Type} [CommRing W] [Nontrivial W] {σ : Type} {P M : σ →₀ ℕ}
    {x x' : MvPowerSeries σ W} (hx : IsUnit x) (hx' : IsUnit x')
    (he : MvPowerSeries.monomial P (1 : W) * x = MvPowerSeries.monomial M 1 * x') : P = M := by
  have h1 : ∀ (P M : σ →₀ ℕ) (x x' : MvPowerSeries σ W), IsUnit x' →
      MvPowerSeries.monomial P (1 : W) * x = MvPowerSeries.monomial M 1 * x' → P ≤ M := by
    intro P M x x' hx' he
    have hc := congrArg (MvPowerSeries.coeff M) he
    rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, if_pos le_rfl, tsub_self,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hc
    by_contra hPM
    rw [if_neg hPM, _root_.one_mul] at hc
    exact (hx'.map (MvPowerSeries.constantCoeff (σ := σ) (R := W))).ne_zero hc.symm
  exact le_antisymm (h1 _ _ _ _ hx' he) (h1 _ _ _ _ hx he.symm)

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

end GlobalTheory.MumFam
end
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.RigChart
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTauSymm

theorem exps_eq {σ k : Type} [Field k] [IsDomain (MvPowerSeries σ k)] {m : ℕ} (v : Fin m → σ)
    (hv : Function.Injective v) (A B : Fin m → ℤ) {x x' : MvPowerSeries σ k} (hx : IsUnit x) (hx' : IsUnit x')
    (he : (∏ i, algebraMap (MvPowerSeries σ k) (FractionRing (MvPowerSeries σ k)) (MvPowerSeries.X (v i)) ^ A i) *
        algebraMap _ _ x =
      (∏ i, algebraMap (MvPowerSeries σ k) (FractionRing (MvPowerSeries σ k)) (MvPowerSeries.X (v i)) ^ B i) *
        algebraMap _ _ x') :
    A = B := by
  set K := FractionRing (MvPowerSeries σ k)
  let n : Fin m → ℕ := fun i => (A i).natAbs + (B i).natAbs
  have hne : ∀ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ≠ 0 := fun i => by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]
    intro e0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (v i) 1)) e0
    simp [MvPowerSeries.coeff_X] at this
  have H : ∀ C : Fin m → ℤ, (∀ i, 0 ≤ C i + n i) →
      (∏ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ C i) *
        ∏ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ n i =
        algebraMap _ K (∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ (C i + n i).toNat) := by
    intro C hC
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne i), Int.toNat_of_nonneg (hC i)]
  have hA : ∀ i, 0 ≤ A i + n i := fun i => by simp only [n]; omega
  have hB : ∀ i, 0 ≤ B i + n i := fun i => by simp only [n]; omega
  have he' := congrArg (· * ∏ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ n i) he
  rw [mul_right_comm, H A hA, mul_right_comm, H B hB, ← map_mul, ← map_mul] at he'
  have he'' := IsFractionRing.injective _ K he'
  have hmon : ∀ a : Fin m → ℕ, ∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ a i =
      MvPowerSeries.monomial (∑ i, Finsupp.single (v i) (a i)) 1 := by
    intro a
    simp_rw [MvPowerSeries.X_pow_eq]
    rw [MvPowerSeries.prod_monomial]
    simp
  have happ : ∀ (a : Fin m → ℕ) (i : Fin m), (∑ j, Finsupp.single (v j) (a j)) (v i) = a i := by
    classical
    intro a i
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      exact fun e => hj (hv e)
    · simp
  rw [hmon, hmon] at he''
  have hPM := GlobalTheory.MumFam.monomial_eq_of_mul_unit hx hx' he''
  funext i
  have := congrArg (fun f => f (v i)) hPM
  simp only [happ] at this
  have a1 := Int.toNat_of_nonneg (hA i)
  have b1 := Int.toNat_of_nonneg (hB i)
  omega

end GlobalTheory.UnitTauSymm

namespace GlobalTheory.UnitTauSymm

open GlobalTheory.LogKSChart ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem commGroup_four_factor_rearrange {G : Type} [CommGroup G] (a b c A B C D : G) :
    a * A * (b * B)⁻¹ * (c * C)⁻¹ * D⁻¹ = a * b⁻¹ * c⁻¹ * (A * B⁻¹ * C⁻¹ * D⁻¹) := by
  simp only [mul_inv]
  ac_rfl

theorem exists_units_rel {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R)
    (gam : Fin m → LinearMap.BilinForm ℤ Q.X) (y z : Q.X) (n1 n2 n3 : Fin m → ℕ)
    (p1 : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c (y + z)).left) fun _ => -1))
    (p2 : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c y).left) fun _ => -1))
    (p3 : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c z).left) fun _ => -1))
    (hp1 : IsUnitPart Q t gam (y + z) n1 p1) (hp2 : IsUnitPart Q t gam y n2 p2) (hp3 : IsUnitPart Q t gam z n3 p3)
    (τ₀ : LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left]
      ![-1, 1, 1, -1])) (hτ : τ₀.IsGen) (e : (FractionRing R)ˣ)
    (hv : ∀ zz J, Good Q.P.L zz J →
      val (Q.tau y z) (𝟙 _) zz J = gm (𝟙 (TK R).left) zz ⊤ (unitOn e) * val τ₀ (toUnit (TK R)).left zz J) :
    ∃ x x' : R, IsUnit x ∧ IsUnit x' ∧ (e : FractionRing R) * algebraMap R _ x =
      algebraMap R _ (∏ i, t i ^ n1 i) * (algebraMap R _ (∏ i, t i ^ n2 i))⁻¹ *
        (algebraMap R _ (∏ i, t i ^ n3 i))⁻¹ * algebraMap R _ x' := by
  obtain ⟨hg1, -, e1, he1, hv1⟩ := hp1
  obtain ⟨hg2, -, e2, he2, hv2⟩ := hp2
  obtain ⟨hg3, -, e3, he3, hv3⟩ := hp3
  have hc0 : Q.c 0 = η[Q.P.A] := by
    have h := Q.c_add 0 0
    rw [add_zero] at h
    have h' : Q.c 0 * Q.c 0 = Q.c 0 := h.symm
    have h1 : Q.c 0 = 1 := mul_eq_left.1 h'
    rw [h1, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hc0' : (Q.c 0).left = eSec Q.P.A := by rw [hc0]; rfl
  let T := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ p1 (LB.invGen Q.P.L _ _ p2))
    (LB.invGen Q.P.L _ _ p3)) (LB.invGen Q.P.L _ _ Q.rig)
  have hT : T.IsGen :=
    LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _
      (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ hg1 (LB.isGen_invGen (L := Q.P.L) _ _ _ hg2))
      (LB.isGen_invGen (L := Q.P.L) _ _ _ hg3)) (LB.isGen_invGen (L := Q.P.L) _ _ _ Q.rig_gen)
  have hF : FormEq (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (Q.c (y + z)).left) (fun _ : PUnit => (Q.c y).left))
      (fun _ : PUnit => (Q.c z).left)) (fun _ : PUnit => eSec Q.P.A))
      (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => -(-1 : ℤ))) (fun _ : PUnit => -(-1 : ℤ)))
        (fun _ : PUnit => -(1 : ℤ)))
      (K' := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, hc0', neg_neg]
    simp [Matrix.vecHead, Matrix.vecTail, hc0']
  obtain ⟨W', hW', hvW⟩ := exists_gen Q.P.isLB hF T hT
  let E : (FractionRing R)ˣ := e1 * e2⁻¹ * e3⁻¹
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  have hui : ∀ a : (FractionRing R)ˣ, unitOn a⁻¹ = (unitOn a)⁻¹ := fun a => map_inv (Units.map _) a
  have hvE : ∀ zz J, Good Q.P.L zz J → val (Q.tau y z) (𝟙 _) zz J =
      gm (𝟙 (TK R).left) zz ⊤ (unitOn E) * val W' (toUnit (TK R)).left zz J := by
    intro zz J hJ
    rw [hvW _ _ zz J hJ]
    simp only [DegPre.tau, DegPre.rigK, T, val_mul hJ, val_inv, val_pull hJ]
    rw [hv1 zz J hJ, hv2 zz J hJ, hv3 zz J hJ, Category.id_comp]
    rw [hu, hu, hui, hui, map_mul, map_mul, map_inv, map_inv]
    exact commGroup_four_factor_rearrange _ _ _ _ _ _ _
  obtain ⟨w, hw⟩ := GlobalTheory.ValueTwoGen.exists_unit_gen _ (TLinPf.linComb_cover Q.P.L Q.P.isLB _ _) τ₀ W' hτ hW'
  have key : ∀ zz J, Good Q.P.L zz J → val W' (toUnit (TK R)).left zz J =
      gm (toUnit (TK R)).left zz ⊤ w * val τ₀ (toUnit (TK R)).left zz J := by
    intro zz J hJ
    have hs : ∀ j, W'.s j = res le_top w * τ₀.s j := fun j => Units.ext (hw j)
    show gm _ zz _ (W'.s _) = _ * gm _ zz _ (τ₀.s _)
    erw [hs, MonoidHom.map_mul, gm_res _ zz le_top (hJ.mem _ _)]
  have k₁ : unitOn e * pullTop (jK R) (1 : Γ(Sp R, ⊤)ˣ) = unitOn E * pullTop (jK R) w :=
      GlobalTheory.TauLocal.eq_of_gm Q.P.isLB fun zz J hJ => by
    have s := (hv zz J hJ).symm.trans (hvE zz J hJ)
    rw [key zz J hJ, ← _root_.mul_assoc] at s
    have hg : gm (toUnit (TK R)).left zz ⊤ w = gm (𝟙 _) zz ⊤ (pullTop (jK R) w) :=
      (show gm (toUnit (TK R)).left zz ⊤ w = gm (𝟙 _ ≫ jK R) zz ⊤ w from rfl).trans
        (gm_pull (𝟙 _) (jK R) zz ⊤ trivial w).symm
    rw [map_mul, map_mul, ← hg, map_one, map_one, _root_.mul_one]
    exact mul_right_cancel s
  have nat := fun v : Γ(Sp R, ⊤)ˣ => congrArg (fun g => g.hom v.val)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  have e₂ := congrArg (fun v => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom v.val) k₁
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (1 : Γ(Sp R, ⊤)ˣ).val,
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val, (1 : Γ(Sp R, ⊤)ˣ).isUnit.map _, w.isUnit.map _, ?_⟩
  have hE : (E : FractionRing R) = algebraMap R _ (∏ i, t i ^ n1 i) * (algebraMap R _ (∏ i, t i ^ n2 i))⁻¹ *
      (algebraMap R _ (∏ i, t i ^ n3 i))⁻¹ := by
    simp only [E, Units.val_mul, Units.val_inv_eq_inv_val, he1, he2, he3]
  rw [← hE]
  refine Eq.trans ?_ (e₂.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w))))
  · refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat 1)))
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply e.val
  · exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply E.val

end GlobalTheory.UnitTauSymm

namespace GlobalTheory.UnitTauSymm

open GlobalTheory.LogKSChart

theorem gam_symm_of_isUnitTau : ∀ (k : Type) [Field k] (m d : ℕ) (Q : DegPre (ChartRing k m d)) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q (bdParam k m d) gam → ∀ (mu α : Q.X) (τ₀ : LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (mu + α)).left, (Q.c mu).left, (Q.c α).left, (Q.c 0).left] ![-1, 1, 1, -1])), IsUnitTau Q (bdParam k m d) gam mu α τ₀ → ∀ i, gam i mu α = gam i α mu := by
  intro k _ m d Q gam hM mu α τ₀ hτ i
  obtain ⟨n1, p1, hp1⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q (bdParam k m d) gam hM (mu + α)
  obtain ⟨n2, p2, hp2⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q (bdParam k m d) gam hM mu
  obtain ⟨n3, p3, hp3⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q (bdParam k m d) gam hM α
  have hn1 := hp1.2.1 i
  have hn2 := hp2.2.1 i
  have hn3 := hp3.2.1 i
  obtain ⟨hτg, e, he, hv⟩ := hτ
  obtain ⟨x, x', hx, hx', hrel⟩ := exists_units_rel Q _ gam mu α n1 n2 n3 p1 p2 p3 hp1 hp2 hp3 τ₀ hτg e hv
  set K := FractionRing (ChartRing k m d)
  let a : Fin m → K := fun i => algebraMap (ChartRing k m d) K (bdParam k m d i)
  have hne : ∀ i, a i ≠ 0 := fun i => by
    simp only [a]
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]
    intro e0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) e0
    simp [bdParam, MvPowerSeries.coeff_X] at this
  have hP : ∀ n : Fin m → ℕ, algebraMap (ChartRing k m d) K (∏ i, bdParam k m d i ^ n i) = ∏ i, a i ^ n i := fun n => by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => map_pow _ _ _
  have hP0 : ∀ n : Fin m → ℕ, ∏ i, a i ^ n i ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne i)
  rw [he, hP, hP, hP] at hrel
  have key : (∏ i, a i ^ (fun i => gam i mu α + n2 i + n3 i) i) * algebraMap _ K x =
      (∏ i, a i ^ (fun i => (n1 i : ℤ)) i) * algebraMap _ K x' := by
    have e1 : (∏ i, a i ^ (fun i => gam i mu α + n2 i + n3 i) i) =
        (∏ i, a i ^ gam i mu α) * (∏ i, a i ^ n2 i) * ∏ i, a i ^ n3 i := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [zpow_add₀ (hne i), zpow_add₀ (hne i), zpow_natCast, zpow_natCast]
    have e2 : (∏ i, a i ^ (fun i => (n1 i : ℤ)) i) = ∏ i, a i ^ n1 i := by
      refine Finset.prod_congr rfl fun i _ => ?_
      exact zpow_natCast _ _
    have hrel' : (∏ i, a i ^ gam i mu α) * algebraMap _ K x =
        (∏ i, a i ^ n1 i) * (∏ i, a i ^ n2 i)⁻¹ * (∏ i, a i ^ n3 i)⁻¹ * algebraMap _ K x' := hrel
    rw [e1, e2]
    calc (∏ i, a i ^ gam i mu α) * (∏ i, a i ^ n2 i) * (∏ i, a i ^ n3 i) * algebraMap _ K x
        = ((∏ i, a i ^ gam i mu α) * algebraMap _ K x) * (∏ i, a i ^ n2 i) * (∏ i, a i ^ n3 i) := by ring
      _ = ((∏ i, a i ^ n1 i) * (∏ i, a i ^ n2 i)⁻¹ * (∏ i, a i ^ n3 i)⁻¹ * algebraMap _ K x') *
          (∏ i, a i ^ n2 i) * (∏ i, a i ^ n3 i) := by rw [hrel']
      _ = (∏ i, a i ^ n1 i) * algebraMap _ K x' * ((∏ i, a i ^ n2 i)⁻¹ * (∏ i, a i ^ n2 i)) *
          ((∏ i, a i ^ n3 i)⁻¹ * (∏ i, a i ^ n3 i)) := by ring
      _ = (∏ i, a i ^ n1 i) * algebraMap _ K x' := by
        rw [inv_mul_cancel₀ (hP0 n2), inv_mul_cancel₀ (hP0 n3), _root_.mul_one, _root_.mul_one]
  have hAB := congrFun (exps_eq (σ := Fin m ⊕ Fin d) (k := k) Sum.inl Sum.inl_injective _ _ hx hx' key) i
  simp only [map_add, LinearMap.add_apply] at hn1
  linarith

end GlobalTheory.UnitTauSymm
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.RigChart
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentForms_symm_of_isUnit_tau_on_toricChart : ∀ (k : Type) [Field k] (m d : ℕ) (Q : DegPre (ChartRing k m d)) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q (bdParam k m d) gam → ∀ (mu α : Q.X) (τ₀ : LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (mu + α)).left, (Q.c mu).left, (Q.c α).left, (Q.c 0).left] ![-1, 1, 1, -1])), IsUnitTau Q (bdParam k m d) gam mu α τ₀ → ∀ i, gam i mu α = gam i α mu := by
  atlas_forward_decl GlobalTheory.UnitTauSymm.gam_symm_of_isUnitTau
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ShiftUnitPart

open ReciprocityTheory.ChartRestriction.G.DVR

theorem good_comp' {X Y Z : Scheme.{0}} {L : LB X} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
  have := hJ (r ≫ ψ)
  rwa [Scheme.Hom.comp_apply] at this

theorem gs_comp_stalk' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem gm_comp_stalk' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)ˣ) : (gm (r ≫ h) z U a).val = (r.stalkMap z).hom (gm h (r z) U a).val := by
  rw [← gs_unit _ _ _ hU, ← gs_unit (r ≫ h) z U (by rwa [Scheme.Hom.comp_apply])]
  exact gs_comp_stalk' r h z U hU _

theorem val_comp_stalk' {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    (val t (r ≫ h) z J).val = (r.stalkMap z).hom (val t h (r z) (fun ψ => J (r ≫ ψ))).val := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t h (r z) (fun ψ => J (r ≫ ψ)) (fun k => J (r ≫ h ≫ φ k)) (fun k => rfl)]
  have hm : (r ≫ h) z ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gs_unit _ z _ hm _).symm.trans ((gs_comp_stalk' r h z _ hm _).trans (congrArg _ (gs_unit h (r z) _ hm _)))

theorem val_transport {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (c : Γ(Y, ⊤)ˣ) (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = gm (𝟙 Y) y ⊤ c * val t' (𝟙 Y) y J)
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) : val t r z J = gm r z ⊤ c * val t' r z J := by
  apply Units.ext
  have e1 := val_comp_stalk' t (𝟙 Y) r z hJ
  have e2 := val_comp_stalk' t' (𝟙 Y) r z hJ
  have e3 := gm_comp_stalk' r (𝟙 Y) z ⊤ trivial c
  simp only [Category.comp_id] at e1 e2 e3
  rw [Units.val_mul, e1, e2, e3, h _ _ (good_comp' r z hJ), Units.val_mul, map_mul]

section Gen
variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R)

theorem prod_famB (ρ : Q.P.A ⟶ Q.P.A) (α : Q.X) (k : ℕ) {U : Type} [CommGroup U] (h : (Q.P.A.left ⟶ Q.P.A.left) → U) :
    ∏ i, h (ρ.left ≫ Q.famφB α i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (ρ * cP Q _ α).left * (h (cP Q _ α).left)⁻¹ * h (1 : Q.P.A ⟶ Q.P.A).left := by
  have e₀ : ρ.left ≫ Q.famφB α 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ Q.famφB α 1 = (ρ * cP Q _ α).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 _) (cP Q _ α)).trans (by rw [Category.comp_id, comp_cP]))
  have e₂ : ρ.left ≫ Q.famφB α 2 = (cP Q _ α).left := congrArg (fun q => q.left) (comp_cP Q ρ α)
  have e₃ : ρ.left ≫ Q.famφB α 3 = (1 : Q.P.A ⟶ Q.P.A).left :=
    congrArg (fun q : Q.P.A ⟶ Q.P.A => q.left) (MonObj.comp_one (M := Q.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_U (e : ℕ) (mu α : Q.X) {Kv : Type} [Fintype Kv]
    {φv : Kv → ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ Q.P.A.left)} {εv : Kv → ℤ}
    (v : LB.Gen (LB.LinComb Q.P.L φv εv)) (hv : v.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ Q.P.A.left) → U),
      ∏ i, h (φv i) ^ εv i = (h (cP Q _ (mu + α)).left)⁻¹ * h (cP Q _ mu).left * h (cP Q _ α).left *
        (h (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Q.P.A).left)⁻¹ * (h (cP Q _ mu).left ^ e)⁻¹ *
        h (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Q.P.A).left ^ e)
    (σ : Q.SecB e α) :
    ∃ σ₁u : Q.SecB e (α + e • mu), ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ Q.P.A) (z : T.left)
      (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J →
      sval σ₁u ρ.left z J = sval σ (ρ ≫ (𝟙 Q.P.A * cP Q _ mu)).left z J *
        (cubN (cubV Q.cub z J) e (ρ ≫ cP Q _ α) (ρ ≫ cP Q _ mu) ρ *
          (cubV Q.cub z J (ρ ≫ cP Q _ α) ρ (ρ ≫ cP Q _ mu))⁻¹ * val v (ρ ≫ toUnit _).left z J).val := by
  obtain ⟨a, ha⟩ : ∃ a : Q.P.A ⟶ Q.P.A, cP Q _ α = a := ⟨_, rfl⟩
  obtain ⟨mm, hmm⟩ : ∃ mm : Q.P.A ⟶ Q.P.A, cP Q _ mu = mm := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Q.P.A ⟶ Q.P.A, 𝟙 Q.P.A = x := ⟨_, rfl⟩
  rw [ha, hmm, hx]
  obtain ⟨N, hN, vN⟩ := exists_cubN Q.cub a mm x e
  let U := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ N (LB.invGen Q.P.L _ _
      (LB.pullGen Q.P.L (thφ Q.P.A (x3 Q.P.A)) thε Q.cub.t (lift a (lift x mm)).left)))
    (LB.pullGen Q.P.L _ _ v (toUnit Q.P.A).left)
  have hU : U.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ Q.cub.isGen _))) (pullGen_isGen _ _ _ _ hv _)
  have c₁ : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
  have c₂ : mm * x = x * mm := mul_comm _ _
  have c₃ : cP Q Q.P.A (mu + α) = a * mm := by rw [cPoint_add, ha, hmm, mul_comm]
  have c₄ : cP Q Q.P.A (α + e • mu) = a * mm ^ e := by rw [cPoint_add, cPoint_nsmul, ha, hmm]
  have c₅ : x * (a * mm ^ e) = a * mm ^ e * x := mul_comm _ _
  obtain ⟨σ₁u, hσ⟩ := exists_sec Q.P.isLB (φ' := Q.famφB (α + e • mu)) (ε' := DegPre.famε e) (fun U _ h => by
      have p₀ := prod_famB Q (x * mm) α e h
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((toUnit Q.P.A).left ≫ q))
      have p₃ := prod_famB Q (𝟙 _) (α + e • mu) e h
      have e₀ : ∀ i, (𝟙 Q.P.A : Q.P.A ⟶ Q.P.A).left ≫ Q.famφB (α + e • mu) i = Q.famφB (α + e • mu) i := fun i => by
        rw [Over.id_left, Category.id_comp]
      simp only [e₀] at p₃
      rw [hx] at p₃
      have t₁ : ∀ χ, (toUnit Q.P.A).left ≫ (cP Q (𝟙_ (Over (Spec (CommRingCat.of R)))) χ).left = (cP Q Q.P.A χ).left :=
        fun χ => congrArg (fun q => q.left) (comp_cP Q (toUnit Q.P.A) χ)
      have t₂ : (toUnit Q.P.A).left ≫ (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Q.P.A).left = (1 : Q.P.A ⟶ Q.P.A).left :=
        congrArg (fun q : Q.P.A ⟶ Q.P.A => q.left) (MonObj.comp_one (M := Q.P.A) (toUnit Q.P.A))
      simp only [t₁, t₂] at p₂
      rw [c₃, hmm, ha] at p₂
      rw [ha, c₁] at p₀
      rw [c₄, c₅] at p₃
      refine Eq.trans (prod_sum₂ _ p₀ (prod_sum₂ _ (prod_sum₂ _ rfl (prod_neg _ _ p₁)) p₂)) (Eq.trans ?_ p₃.symm)
      rw [c₂]
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_one, Matrix.head_cons, _root_.mul_one, ofMul_one]
      module)
    (pullMulSec σ (x * mm).left U hU)
  refine ⟨σ₁u, fun T ρ z J hJ => ?_⟩
  rw [hσ _ _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, Over.comp_left]
  congr 2
  refine (val_mul hJ _ _ _).trans ?_
  rw [val_pull hJ]
  refine congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((vN T ρ z J hJ).trans (by rw [← hx, Category.comp_id])) ((val_inv _ _).trans (congrArg (·⁻¹) ((val_cub Q.cub ρ hJ _ _ _).trans (by rw [← hx, Category.comp_id])))))) (by rw [Over.comp_left])
end Gen

theorem nonneg_shift {X : Type} [AddCommGroup X] (g : LinearMap.BilinForm ℤ X) (mu α : X) (hs : g mu α = g α mu)
    (hnn : ∀ y, 0 ≤ g y y) (n : ℕ) (hn : g mu mu = 2 * n) (e : ℕ) (he : (g mu α).natAbs ≤ e) :
    0 ≤ (e : ℤ) * n + g mu α := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have key : ∀ x : ℤ, 0 ≤ 2 * x * g mu α + g α α := fun x => by
      have := hnn (x • mu + α)
      simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hn, ← hs] at this
      push_cast at this
      linarith
    have h0 : g mu α = 0 := by
      by_contra hne
      have := key (-(g α α + 1) * g mu α)
      nlinarith [sq_pos_of_ne_zero hne, hnn α]
    simp [h0]
  · have h1 : -(g mu α) ≤ ((g mu α).natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact neg_le_abs _
    have h2 : ((g mu α).natAbs : ℤ) ≤ e := by exact_mod_cast he
    have h3 : (1 : ℤ) ≤ n := by exact_mod_cast hpos
    nlinarith

theorem gs_zero' {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) : gs f z ⊤ (0 : Γ(Y, ⊤)) = 0 := by
  rw [gs_eq f z ⊤ trivial, map_zero, map_zero]

theorem sval_secScale' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem gs_appTop {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (a : Γ(X, ⊤)) :
    gs f z ⊤ (g.appTop.hom a) = gs (f ≫ g) z ⊤ a :=
  gs_pull f g z ⊤ trivial a

theorem exists_shift_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → (∀ i, 0 ≤ (e : ℤ) * n i + gam i mu α) ∧ ∀ σ : P.D.toPre.SecB e α, ∃ σ₁ σ₁u : P.D.toPre.SecB e (α + e • mu), ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ ((e : ℤ) * n i + gam i mu α).toNat)) * sval σ₁u x z J) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u (r ≫ (P.D.toPre.c 0).left) z J = ((val ψ₀ r z J) ^ e * val τ₀ r z J * (val P.D.toPre.rig r z J) ^ e).val * sval σ (r ≫ (P.D.toPre.c mu).left) z J := by
  intro E _ _ _ H k _ _ m d t P gam hM hli hab
  intro Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B' _ π₁ π₂ c' h₁ h₂ h₃ h₄ mu α n ψ₀ τ₀ hψ hτ
  have hsym : ∀ i, gam i mu α = gam i α mu := GlobalTheory.T.exponentForms_symm_of_isUnit_tau_on_toricChart k m d P.D.toPre gam hM mu α τ₀ hτ
  have hN : ∀ e : ℕ, (∑ i, (gam i mu α).natAbs) ≤ e → ∀ i, 0 ≤ (e : ℤ) * n i + gam i mu α := fun e he i =>
    nonneg_shift (gam i) mu α (hsym i) (hM.nonneg i) (n i) (hψ.2.1 i) e
      ((Finset.single_le_sum (f := fun i => (gam i mu α).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans he)
  refine ⟨∑ i, (gam i mu α).natAbs, fun e he => ⟨hN e he, fun σ => ?_⟩⟩
  have hG : GlobalFnsSt := GlobalTheory.ExpansionTotal.globalFns
  have hc0 : P.D.toPre.c 0 = η[P.D.toPre.P.A] := by
    have h := P.D.toPre.c_add 0 0
    rw [add_zero] at h
    have h' : P.D.toPre.c 0 * P.D.toPre.c 0 = P.D.toPre.c 0 := h.symm
    have h1 : P.D.toPre.c 0 = 1 := mul_eq_left.1 h'
    rw [h1, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let v₀ := LB.mulGen P.D.toPre.P.L _ _ _ _ (LB.mulGen P.D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen P.D.toPre.P.L _ _ ψ₀ e) τ₀)
    (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig e)
  have hv₀ : v₀.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hψ.1 e) hτ.1)
    (powGen_isGen _ _ _ _ P.D.toPre.rig_gen e)
  have kc : ∀ χ, (P.D.toPre.c χ).left =
      (cP P.D.toPre (𝟙_ (Over (Spec (CommRingCat.of (ChartRing k m d))))) χ).left := fun χ => by
    rw [cP, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have k1 : (P.D.toPre.c 0).left = (1 : 𝟙_ (Over (Spec (CommRingCat.of (ChartRing k m d)))) ⟶ P.D.toPre.P.A).left := by
    rw [hc0, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have k0 : eSec P.D.toPre.P.A = (1 : 𝟙_ (Over (Spec (CommRingCat.of (ChartRing k m d)))) ⟶ P.D.toPre.P.A).left := by
    rw [← k1, hc0]; rfl
  obtain ⟨σ₁u, hσu⟩ := exists_U P.D.toPre e mu α v₀ hv₀ (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons]
      rw [k1, k0, kc, kc, kc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
      module) σ
  have hne : ∀ i, algebraMap (ChartRing k m d) (FractionRing (ChartRing k m d)) (bdParam k m d i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (by
      intro h0
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
      simp [bdParam, MvPowerSeries.coeff_X] at this)
  obtain ⟨-, -, e1, he1, hv1⟩ := hψ
  obtain ⟨-, e', he', hv'⟩ := hτ
  let tN : ChartRing k m d := ∏ i, bdParam k m d i ^ ((e : ℤ) * n i + gam i mu α).toNat
  have hE : ((e1 ^ e * e' : (FractionRing (ChartRing k m d))ˣ) : FractionRing (ChartRing k m d)) =
      algebraMap (ChartRing k m d) _ tN := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, he1, he']
    simp only [tN, map_prod, map_pow]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul, ← zpow_natCast, ← zpow_natCast (algebraMap _ _ _) (((e : ℤ) * n i + gam i mu α).toNat),
      ← zpow_add₀ (hne i), Int.toNat_of_nonneg (hN e he i)]
    congr 1
    push_cast
    ring
  refine ⟨DVR.SecOps.secScale (Out.scal P.D.toPre.P.A.hom tN) σ₁u, σ₁u, ?_, fun Z x z J hJ => ?_, ?_⟩
  rotate_left
  · rw [sval_secScale' _ _ _ _ hJ]
    exact congrArg (· * _) (gs_appTop x P.D.toPre.P.A.hom z _)
  · intro Z r z J hJ
    let T' : Over (Spec (CommRingCat.of (ChartRing k m d))) := Over.mk r
    have ht : (toUnit T').left = r := (Category.comp_id _).symm.trans (Over.w (toUnit T'))
    let ρ' : T' ⟶ P.D.toPre.P.A := Over.homMk (r ≫ (P.D.toPre.c 0).left) (by
        show (r ≫ (P.D.toPre.c 0).left) ≫ P.D.toPre.P.A.hom = r
        rw [Category.assoc, Over.w (P.D.toPre.c 0)]
        exact Category.comp_id r)
    have hρ1 : ρ' = 1 := by
      rw [Hom.one_def]
      apply Over.OverMorphism.ext
      rw [Over.comp_left, ht, ← hc0]
      rfl
    have hρu : ρ' ≫ toUnit P.D.toPre.P.A = toUnit T' := toUnit_unique _ _
    have hρm : ρ' ≫ (𝟙 P.D.toPre.P.A * cP P.D.toPre _ mu) = toUnit T' ≫ P.D.toPre.c mu := by
      rw [MonObj.comp_mul, Category.comp_id, comp_cP, hρ1, _root_.one_mul]
      rfl
    have C : IsCub (cubV P.D.toPre.cub z J) := isCub_cubV (T := T') P.D.toPre.cub hJ
    have c1 : cubN (cubV P.D.toPre.cub z J) e (ρ' ≫ cP P.D.toPre _ α) (ρ' ≫ cP P.D.toPre _ mu) ρ' = 1 := by
      rw [hρ1]; exact C.N_one _ _ _
    have c2 : cubV P.D.toPre.cub z J (ρ' ≫ cP P.D.toPre _ α) ρ' (ρ' ≫ cP P.D.toPre _ mu) = 1 := by
      rw [hρ1]; exact C.face₂ _ _
    have hv := hσu T' ρ' z J hJ
    rw [c1, c2, hρu, hρm, inv_one, _root_.one_mul, _root_.one_mul] at hv
    show sval σ₁u ρ'.left z J = _
    rw [hv, Over.comp_left, ht]
    rw [val_mul hJ, val_mul hJ, val_pow, val_pow, mul_comm]
  · intro uu hu hc z J hJ
    have hr : ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
        jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) ≫ (toUnit (TK (ChartRing k m d))).left =
        (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d)) ≫ toUnit P.D.toPre.P.A).left := by
      have := congrArg (fun q => q.left) (toUnit_unique (fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d)))
        P.D.toPre.P.A ≫ (Over.homMk (jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) rfl :
          TF (R := ChartRing k m d) (FractionRing (ChartRing k m d)) ⟶ TK (ChartRing k m d)) ≫ toUnit (TK (ChartRing k m d)))
        (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d)) ≫ toUnit P.D.toPre.P.A))
      simpa [Category.assoc] using this
    have hu' : unitOn (e1 ^ e * e') = unitOn e1 ^ e * unitOn e' := by simp [unitOn, map_mul, map_pow]
    have hfm : val (DegPre.famMult P.D.toPre (FractionRing (ChartRing k m d)) e mu α)
        (fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left z J =
        gm ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
          jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) z ⊤ (unitOn (e1 ^ e * e')) *
        val v₀ (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d)) ≫ toUnit P.D.toPre.P.A).left z J := by
      have P1 := val_transport (P.D.toPre.psi mu) (LB.pullGen P.D.toPre.P.L _ _ ψ₀ (toUnit (TK (ChartRing k m d))).left)
        (unitOn e1) (fun y J hJ => (hv1 y J hJ).trans (by rw [val_pull hJ, Category.id_comp]))
        ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
          jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) z J hJ
      have P2 := val_transport (P.D.toPre.tau mu α) (LB.pullGen P.D.toPre.P.L _ _ τ₀ (toUnit (TK (ChartRing k m d))).left)
        (unitOn e') (fun y J hJ => (hv' y J hJ).trans (by rw [val_pull hJ, Category.id_comp]))
        ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
          jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) z J hJ
      rw [val_pull hJ] at P1 P2
      rw [val_famMult (fst _ _) hJ e mu α, val_pow, val_pow, P1, P2, DegPre.rigK, val_pull hJ, hr, val_mul hJ,
        val_mul hJ, val_pow, val_pow, hu', map_mul, map_pow, mul_pow]
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    have hGv : (gm ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
          jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) z ⊤ (unitOn (e1 ^ e * e'))).val =
        gs (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z ⊤ (Out.scal P.D.toPre.P.A.hom tN) := by
      rw [← gs_unit _ z ⊤ trivial]
      show gs _ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (ChartRing k m d)))).inv.hom
        ((e1 ^ e * e' : (FractionRing (ChartRing k m d))ˣ) : FractionRing (ChartRing k m d))) = _
      rw [hE]
      all_goals
        have nat := congrArg (fun f => f.hom tN) (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (algebraMap (ChartRing k m d) (FractionRing (ChartRing k m d)))))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
        rw [nat, gs_appTop, Out.scal, gs_appTop]
        congr 1
    have G := (gen_fe (F := FractionRing (ChartRing k m d)) hG e mu α).2 uu hu hc _ (𝟙 _) z J hJ
    rw [Over.id_left] at G
    rw [G]
    have hz0 : Out.scal (DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).hom (0 : ChartRing k m d) = 0 := by
      simp [Out.scal]
    rw [hz0, gs_zero', zero_mul, add_zero, sval_secScale' _ _ _ _ hJ]
    have etr : DegPre.trF P.D.toPre (FractionRing (ChartRing k m d)) mu ≫ DegPre.prB P.D.toPre _ =
        DegPre.prB P.D.toPre _ ≫ (𝟙 P.D.toPre.P.A * cP P.D.toPre _ mu) := by
      rw [MonObj.comp_mul, Category.comp_id, comp_cP]
      exact lift_snd _ _
    rw [etr, hσu _ (DegPre.prB P.D.toPre _) z J hJ, uVal_id, Category.id_comp, hfm]
    simp only [comp_cP, Units.val_mul, th]
    rw [hGv]
    ring

end GlobalTheory.ShiftUnitPart
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shifted_section_div_monomial_over_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → (∀ i, 0 ≤ (e : ℤ) * n i + gam i mu α) ∧ ∀ σ : P.D.toPre.SecB e α, ∃ σ₁ σ₁u : P.D.toPre.SecB e (α + e • mu), ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ ((e : ℤ) * n i + gam i mu α).toNat)) * sval σ₁u x z J) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u (r ≫ (P.D.toPre.c 0).left) z J = ((val ψ₀ r z J) ^ e * val τ₀ r z J * (val P.D.toPre.rig r z J) ^ e).val * sval σ (r ≫ (P.D.toPre.c mu).left) z J := by
  atlas_forward_decl GlobalTheory.ShiftUnitPart.exists_shift_div_monomial
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_shift_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (e : ℕ), 1 ≤ e → ∀ (mu α : P.D.toPre.X) (N : Fin m → ℕ) (σ σ' : P.D.toPre.SecB e α) (σ₁ σ₁u σ₁' σ₁u' : P.D.toPre.SecB e (α + e • mu)), TActs Y h e α σ σ' → ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ → ShiftEq P.D.toPre e mu α σ' σ₁' 0 σ₁' → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u x z J) → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁' x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u' x z J) → ∃ σ₁u'' : P.D.toPre.SecB e (α + e • mu), TActs Y h e (α + e • mu) σ₁u σ₁u'' ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u'' x z J = sval σ₁u' x z J - gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i)) * sval σ₁u x z J := by
  first | exact @GlobalTheory.Heat.heat_div_monomial | exact GlobalTheory.Heat.heat_div_monomial | (intros; apply GlobalTheory.Heat.heat_div_monomial <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitsEval

section Pts
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem c_zero_one : D.c 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  exact (mul_eq_left.1 h.symm)

theorem left_toUnit {T : Scheme.{0}} (f : T ⟶ Spec (CommRingCat.of R)) :
    (toUnit (Over.mk f)).left = f := by
  have := Over.w (toUnit (Over.mk f))
  simpa using this

theorem famφB_pt {T : Scheme.{0}} (f : T ⟶ Spec (CommRingCat.of R)) (a b : D.X) :
    (f ≫ (D.c a).left) ≫ D.famφB b 0 = f ≫ (D.c a).left ∧
    (f ≫ (D.c a).left) ≫ D.famφB b 1 = f ≫ (D.c (a + b)).left ∧
    (f ≫ (D.c a).left) ≫ D.famφB b 2 = f ≫ (D.c b).left ∧
    (f ≫ (D.c a).left) ≫ D.famφB b 3 = f ≫ (D.c 0).left := by
  have hf : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, f ≫ x.left = (toUnit (Over.mk f) ≫ x).left := by
    intro x; rw [Over.comp_left, left_toUnit]
  refine ⟨by simp [DegPre.famφB], ?_, ?_, ?_⟩
  · change (f ≫ (D.c a).left) ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c b)).left = _
    have hp : ∀ (x y : D.P.A ⟶ D.P.A), padd D.P.A x y = x * y := fun _ _ => rfl
    have hp' : ∀ (x y : 𝟙_ _ ⟶ D.P.A), padd D.P.A x y = x * y := fun _ _ => rfl
    rw [hf, hf, ← Over.comp_left, D.c_add, hp, hp', comp_mul, comp_mul]
    congr 2
    all_goals simp [← Category.assoc]
  · change (f ≫ (D.c a).left) ≫ (toUnit D.P.A ≫ D.c b).left = _
    rw [hf, hf, ← Over.comp_left]; congr 1; simp [← Category.assoc]
  · change (f ≫ (D.c a).left) ≫ (toUnit D.P.A ≫ η[D.P.A]).left = _
    rw [hf, hf, ← Over.comp_left, c_zero_one]; congr 1
    rw [comp_one, ← Category.assoc, toUnit_unique ((toUnit _ ≫ D.c a) ≫ toUnit _) (toUnit _)]; rfl

end Pts
end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

section Ev
variable {A : Type} [CommRing A]

noncomputable def ev (z : Sp A) : A →+* (Sp A).presheaf.stalk z where
  toFun a := gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  map_one' := by rw [map_one, gs_eq _ z ⊤ trivial, map_one, map_one]
  map_mul' a b := by rw [map_mul, gs_mul _ z ⊤ trivial]
  map_zero' := by rw [map_zero, gs_eq _ z ⊤ trivial, map_zero, map_zero]
  map_add' a b := by rw [map_add, gs_add _ z ⊤ trivial]

theorem ev_apply (z : Sp A) (a : A) : ev z a = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := rfl

theorem gs_spMap {R : Type} [CommRing R] (g : R →+* A) (z : Sp A) (r : R) :
    gs (spMap g) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = ev z (g r) := by
  have h := gs_pull (𝟙 _) (spMap g) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  rw [Category.id_comp] at h
  rw [← h, ev_apply]
  congr 1
  have := congrArg (fun f => f.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact this.symm

theorem gm_unitOn (z : Sp A) (u : Aˣ) : gm (𝟙 _) z ⊤ (unitOn u) = Units.map (ev z).toMonoidHom u := by
  ext
  rw [← gs_unit _ z ⊤ trivial]
  rfl

end Ev
end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem alg_eval {k S : Type} [Field k] [CharZero k] [CommRing S] (φ : DualNumber k →+* S) (e : ℕ) (he : 1 ≤ e)
    (κ ee : (DualNumber k)ˣ) (ℓα ℓμ s : k)
    (hee : (ee : DualNumber k) = 1 + TrivSqZeroExt.inr ((e : k) * ℓμ - s))
    (Uρ Uc Wi W0 Wt : Sˣ) (Aρ Ac A'c : S) (hAc : IsUnit Ac) (hWt : Wt * W0 = Wi)
    (hi : Aρ * Wi.val = φ (κ.val * (1 + TrivSqZeroExt.inr ℓα)) *
      (Ac + φ (TrivSqZeroExt.inr ((2 * (e : k))⁻¹)) * A'c))
    (hii : Uρ.val * Aρ * W0.val = φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) *
      (Uc.val * Ac + φ (TrivSqZeroExt.inr ((2 * (e : k))⁻¹)) *
        (Uc.val * A'c - φ (TrivSqZeroExt.inl (2 * (e : k) * s)) * (Uc.val * Ac)))) :
    Uρ = Wt * Units.map φ.toMonoidHom ee * Uc := by
  set c₁ : k := (2 * (e : k))⁻¹ with hc₁
  have he0 : (2 * (e : k)) ≠ 0 := by
    have : (e : k) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
    exact mul_ne_zero two_ne_zero this
  have hnil : IsNilpotent (φ (TrivSqZeroExt.inr c₁) * A'c) := by
    refine ⟨2, ?_⟩
    rw [mul_pow, ← map_pow, pow_two, TrivSqZeroExt.inr_mul_inr, map_zero, zero_mul]
  have hX : IsUnit (Ac + φ (TrivSqZeroExt.inr c₁) * A'c) := by
    first
      | exact hnil.isUnit_add_left_of_commute hAc (Commute.all _ _)
      | exact IsUnit.add_of_isNilpotent hAc hnil
  have hK : IsUnit (φ (κ.val * (1 + TrivSqZeroExt.inr ℓα))) := by
    refine IsUnit.map φ (IsUnit.mul κ.isUnit ?_)
    refine ⟨⟨1 + TrivSqZeroExt.inr ℓα, 1 - TrivSqZeroExt.inr ℓα, ?_, ?_⟩, rfl⟩ <;>
      ext <;> simp
  have hY := hK.mul hX
  have d1 : φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) -
      φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) * φ (TrivSqZeroExt.inr c₁) *
        φ (TrivSqZeroExt.inl (2 * (e : k) * s)) = φ ee.val * φ (κ.val * (1 + TrivSqZeroExt.inr ℓα)) := by
    rw [← map_mul, ← map_mul, ← map_sub, ← map_mul, hee]
    congr 1
    have h1 : c₁ * (2 * (e : k) * s) = s := by rw [hc₁, ← _root_.mul_assoc, inv_mul_cancel₀ he0, _root_.one_mul]
    ext <;> simp <;> linear_combination (-(TrivSqZeroExt.fst (κ : DualNumber k))) * h1
  have d2 : φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) * φ (TrivSqZeroExt.inr c₁) =
      φ ee.val * φ (κ.val * (1 + TrivSqZeroExt.inr ℓα)) * φ (TrivSqZeroExt.inr c₁) := by
    rw [← map_mul, ← map_mul, ← map_mul, hee]
    congr 1
    ext <;> simp <;> ring
  have hWt' : Wt.val * W0.val = Wi.val := by rw [← Units.val_mul, hWt]
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  apply hY.mul_right_cancel
  linear_combination (-Uρ.val) * hi + (-(Uρ.val * Aρ)) * hWt' + Wt.val * hii +
    (Wt.val * Uc.val * Ac) * d1 + (Wt.val * Uc.val * A'c) * d2

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem exists_acts' {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) {O : Type} [CommRing O]
    [StarRing O] [Module O Dd.toPre.X] {oa : Dd.toPre.OAct O} (Y : Ray oa) {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left) (hv : ∀ a, IsInv Y.H (v a) (dd a))
    (inst : Algebra ℤ R) (D : @Derivation ℤ R R _ _ _ inst _ _) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D)
    (hb : IsBasic Y h) (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) : ∃ σ', TActs Y h k α σ σ' := by
  obtain rfl : inst = Ring.toIntAlgebra R := Subsingleton.elim _ _
  exact heat_acts_on_terms R Dd O oa Y n v dd hv D h hb k α σ

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem prod_fam {G T : Type} [CommGroup G] (F : T → G) (p : Fin 4 → T) (e : ℕ) :
    ∏ j, F (p j) ^ DegPre.famε e j = F (p 0) ^ ((e : ℤ) - 1) * F (p 1) * (F (p 2))⁻¹ * F (p 3) := by
  simp [Fin.prod_univ_four, DegPre.famε]

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem mul_inv_mul_cancel_comm {G : Type} [CommGroup G] (a b c d x : G) (e : ℕ) :
    (a ^ ((e : ℤ) - 1) * b * c⁻¹ * d ^ (1 - (e : ℤ))) * (d ^ ((e : ℤ) - 1) * x * x⁻¹ * d) =
      a ^ ((e : ℤ) - 1) * b * c⁻¹ * d := by
  group

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

set_option maxHeartbeats 1000000 in

theorem units_eval : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ lam : ℕ → P.D.toPre.X → k, ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ ee : (DualNumber k)ˣ, (ee : DualNumber k) = 1 + TrivSqZeroExt.inr (lam e mu - ∑ i, ((e : k) * (n i : k) + (gam i mu α : k)) * MvPowerSeries.constantCoeff (q i)) → ∀ zz J, Good P.D.toPre.P.L zz J → (val ψ₀ (spMap ρ) zz J) ^ e * val τ₀ (spMap ρ) zz J * (val P.D.toPre.rig (spMap ρ) zz J) ^ e = gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) * gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) * (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) * (val ψ₀ (spMap (constHom ρ)) zz J) ^ e * val τ₀ (spMap (constHom ρ)) zz J * (val P.D.toPre.rig (spMap (constHom ρ)) zz J) ^ e := by
  intro E _ _ _ H k _ _ m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B' _ π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' w hw
  obtain ⟨κ, ℓ, hconn⟩ := GlobalTheory.T.heatOperator_symbolZero_eq_connection E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' w hw
  refine ⟨fun e mu => (e : k) * ℓ e mu, ?_⟩
  intro mu α n ψ₀ τ₀ hψ hτ
  obtain ⟨e₁, he₁⟩ := GlobalTheory.T.exists_bundleSection_unit_at_closedPoint_torusChart E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc'
  obtain ⟨e₂, he₂⟩ := GlobalTheory.T.exists_shifted_section_div_monomial_over_chart E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' mu α n ψ₀ τ₀ hψ hτ
  refine ⟨max (max e₁ e₂) 1, fun e he ee hee zz J hJ => ?_⟩
  have he1 : 1 ≤ e := le_trans (le_max_right _ _) he
  have hle₁ : e₁ ≤ e := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) he
  have hle₂ : e₂ ≤ e := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) he
  obtain ⟨σ, hσu⟩ := he₁ e hle₁ mu α
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  obtain ⟨σ', hσσ'⟩ := exists_acts' P.D Y v' dd hdd _ D h hB e α σ
  obtain ⟨hN, hσ₁⟩ := he₂ e hle₂
  obtain ⟨σ₁, σ₁u, hS, hfac, hval⟩ := hσ₁ σ
  obtain ⟨σ₁', σ₁u', hS', hfac', hval'⟩ := hσ₁ σ'
  obtain ⟨σ₁u'', hT'', hval''⟩ := GlobalTheory.T.heatOperator_shift_div_monomial E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' e he1 mu α (fun i => ((e : ℤ) * n i + gam i mu α).toNat) σ σ' σ₁ σ₁u σ₁' σ₁u'
    hσσ' hS hS' hfac hfac'

  have pts := fun (a b : P.D.toPre.X) => famφB_pt P.D.toPre (spMap ρ) a b
  have pts' := fun (a b : P.D.toPre.X) => famφB_pt P.D.toPre (spMap (constHom ρ)) a b
  have hB' : ∀ a b : P.D.toPre.X, c' a ≫ B'.hom = c' b ≫ B'.hom := fun a b => by rw [(hc' a).1, (hc' b).1]
  have X0 : ∀ a b : P.D.toPre.X, c' a ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 0 ∧
      c' a ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 0 := fun a b =>
    ⟨by rw [(hc' a).2.1, (pts a b).1], by rw [(hc' a).2.2, (pts' a b).1]⟩
  have X1 : ∀ a b : P.D.toPre.X, c' (a + b) ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 1 ∧
      c' (a + b) ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 1 := fun a b =>
    ⟨by rw [(hc' _).2.1, (hc' a).2.1, (pts a b).2.1], by rw [(hc' _).2.2, (hc' a).2.2, (pts' a b).2.1]⟩
  have X2 : ∀ a b : P.D.toPre.X, c' b ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 2 ∧
      c' b ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 2 := fun a b =>
    ⟨by rw [(hc' _).2.1, (hc' a).2.1, (pts a b).2.2.1], by rw [(hc' _).2.2, (hc' a).2.2, (pts' a b).2.2.1]⟩
  have X3 : ∀ a b : P.D.toPre.X, c' 0 ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 3 ∧
      c' 0 ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 3 := fun a b =>
    ⟨by rw [(hc' _).2.1, (hc' a).2.1, (pts a b).2.2.2], by rw [(hc' _).2.2, (hc' a).2.2, (pts' a b).2.2.2]⟩
  have hi := hconn e he1 α σ σ' hσσ' _ (c' mu) ![c' mu, c' (mu + α), c' α, c' 0] (by
    intro j; fin_cases j
    · exact ⟨(X0 mu α).1, (X0 mu α).2, hB' _ _⟩
    · exact ⟨(X1 mu α).1, (X1 mu α).2, hB' _ _⟩
    · exact ⟨(X2 mu α).1, (X2 mu α).2, hB' _ _⟩
    · exact ⟨(X3 mu α).1, (X3 mu α).2, hB' _ _⟩) zz J hJ
  have hii := hconn e he1 (α + e • mu) σ₁u σ₁u'' hT'' _ (c' 0) ![c' 0, c' (α + e • mu), c' (α + e • mu), c' 0] (by
    intro j; fin_cases j
    · exact ⟨(X0 0 _).1, (X0 0 _).2, hB' _ _⟩
    · have h1 := X1 0 (α + e • mu)
      rw [zero_add] at h1
      exact ⟨h1.1, h1.2, hB' _ _⟩
    · exact ⟨(X2 0 _).1, (X2 0 _).2, hB' _ _⟩
    · exact ⟨(X3 0 _).1, (X3 0 _).2, hB' _ _⟩) zz J hJ

  have vρ := hval _ (spMap ρ) zz J hJ
  have vc := hval _ (spMap (constHom ρ)) zz J hJ
  have vc' := hval' _ (spMap (constHom ρ)) zz J hJ
  have v'' := hval'' _ (spMap (constHom ρ) ≫ (P.D.toPre.c 0).left) zz J hJ
  rw [← (hc' 0).2.1, ← (hc' mu).2.1] at vρ
  rw [← (hc' 0).2.2, ← (hc' mu).2.2] at vc vc'
  have hx0 : (spMap (constHom ρ) ≫ (P.D.toPre.c 0).left) ≫ P.D.toPre.P.A.hom = spMap (constHom ρ) := by
    rw [Category.assoc, Over.w (P.D.toPre.c 0)]; simp
  rw [hx0, gs_spMap, ← (hc' 0).2.2] at v''
  rw [(hc' mu).1, ← ev_apply, ← ev_apply] at hi
  rw [(hc' 0).1, ← ev_apply, ← ev_apply, v'', vρ, vc, vc'] at hii
  have hcH : ∀ r, constHom ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) := by
    intro r; simp [constHom, hρ, TrivSqZeroExt.algebraMap_eq_inl]
  set s : k := ∑ i, ((((e : ℤ) * n i + gam i mu α).toNat : ℕ) : k) * MvPowerSeries.constantCoeff (q i) with hs
  have hcst : constHom ρ (2 * (e : ChartRing k m d) * ∑ i, ((((e : ℤ) * n i + gam i mu α).toNat : ℕ) : ChartRing k m d) * q i) =
      TrivSqZeroExt.inl (2 * (e : k) * s) := by
    rw [hcH, hs]; congr 1
    rw [map_mul, map_mul, map_sum]
    simp only [map_mul, map_natCast, map_ofNat]
  rw [hcst, map_add, map_nsmul, nsmul_eq_mul] at hii

  have hee' : (ee : DualNumber k) = 1 + TrivSqZeroExt.inr ((e : k) * ℓ e mu - s) := by
    rw [hee, hs]
    congr 3
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have h0 := Int.toNat_of_nonneg (hN i)
    have h1 : ((((e : ℤ) * n i + gam i mu α).toNat : ℕ) : k) = ((((e : ℤ) * n i + gam i mu α) : ℤ) : k) := by
      rw [← Int.cast_natCast, h0]
    rw [h1]; push_cast; ring
  have hAc : IsUnit (sval σ (c' mu ≫ π₂) zz J) := by
    have := hσu zz J hJ
    rwa [← (hc' mu).2.2] at this
  rw [gm_unitOn, alg_eval (ev zz) e he1 (κ e) ee (ℓ e α) (ℓ e mu) s hee' _ _ _ _
    (gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) *
      gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) *
      (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ *
      gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)))
    _ _ _ hAc ?_ hi hii]
  · simp only [_root_.mul_assoc]
  · have e1 := prod_fam (fun x => gm x zz _ (w.s (fun _ => J (x ≫ π₂), fun _ => J (x ≫ π₁))))
      ![c' 0, c' (α + e • mu), c' (α + e • mu), c' 0] e
    have e2 := prod_fam (fun x => gm x zz _ (w.s (fun _ => J (x ≫ π₂), fun _ => J (x ≫ π₁))))
      ![c' mu, c' (mu + α), c' α, c' 0] e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] at e1 e2
    rw [e1, e2]
    exact mul_inv_mul_cancel_comm _ _ _ _ _ e

end GlobalTheory.UnitsEval
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitPart_psi_tau_tangent_vector_variation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ lam : ℕ → P.D.toPre.X → k, ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ ee : (DualNumber k)ˣ, (ee : DualNumber k) = 1 + TrivSqZeroExt.inr (lam e mu - ∑ i, ((e : k) * (n i : k) + (gam i mu α : k)) * MvPowerSeries.constantCoeff (q i)) → ∀ zz J, Good P.D.toPre.P.L zz J → (val ψ₀ (spMap ρ) zz J) ^ e * val τ₀ (spMap ρ) zz J * (val P.D.toPre.rig (spMap ρ) zz J) ^ e = gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) * gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) * (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) * (val ψ₀ (spMap (constHom ρ)) zz J) ^ e * val τ₀ (spMap (constHom ρ)) zz J * (val P.D.toPre.rig (spMap (constHom ρ)) zz J) ^ e := by
  atlas_forward_decl GlobalTheory.UnitsEval.units_eval
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitsAlong

theorem alg {G : Type} [CommGroup G] (P T Rg Wy Wyz Wz W0 U2 E Pc Tc Rgc : G) (e : ℕ) (n n' : ℤ)
    (hA : P ^ e * T * Rg ^ e = Wy ^ n * Wyz * Wz⁻¹ * W0 ^ n' * (U2 * E) * Pc ^ e * Tc * Rgc ^ e)
    (hB : P ^ e * 1 * Rg ^ e = Wy ^ n * Wy * W0⁻¹ * W0 ^ n' * U2 * Pc ^ e * 1 * Rgc ^ e) :
    T = Wyz * Wy⁻¹ * Wz⁻¹ * W0 * E * Tc := by
  apply Additive.ofMul.injective
  have hA' := congrArg Additive.ofMul hA
  have hB' := congrArg Additive.ofMul hB
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one, add_zero] at hA' hB' ⊢
  calc Additive.ofMul T = (e • Additive.ofMul P + Additive.ofMul T + e • Additive.ofMul Rg) -
        (e • Additive.ofMul P + e • Additive.ofMul Rg) := by abel
    _ = _ := by rw [hA', hB']; abel

theorem unitTau_along : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ c : ℚ, c ≠ 0 ∧ ∃ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen ∧ ∀ y z τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam y z τ₀ → ∀ e : (DualNumber k)ˣ, (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, (c : k) * MvPowerSeries.constantCoeff (q i) * gam i y z) → ∀ zz J, Good P.D.toPre.P.L zz J → val τ₀ (spMap ρ) zz J = gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) * (gm (c' (y)) zz _ (w.s (fun _ => J (c' (y) ≫ π₂), fun _ => J (c' (y) ≫ π₁))))⁻¹ * (gm (c' (z)) zz _ (w.s (fun _ => J (c' (z) ≫ π₂), fun _ => J (c' (z) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) * val τ₀ (spMap (constHom ρ)) zz J := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  intro Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' _ π₁ π₂ c' h₁ h₂ hfib hc'
  obtain ⟨w, hw⟩ := GlobalTheory.ConstDefSym.lbIso_pull_of_const (ChartRing k m d) P.D.toPre k ρ B' inferInstance π₁ π₂ h₁ h₂ hfib
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.unitPart_psi_tau_tangent_vector_variation E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' π₁ π₂ c' h₁ h₂ hfib hc' w hw
  refine ⟨-1, by norm_num, w, hw, ?_⟩
  intro y z τ₀ hτ ee hee zz J hJ
  obtain ⟨n, ψ₀, hψ⟩ := GlobalTheory.UnitPart.exists_isUnitPart P.D.toPre (bdParam k m d) gam hmon y
  obtain ⟨τ₁, hτ₁, hv₁⟩ := GlobalTheory.T.exists_unitPartPeriodTau_zero_value_one E H k m d t P gam y
  obtain ⟨e₁, he₁⟩ := hlam y z n ψ₀ τ₀ hψ hτ
  obtain ⟨e₂, he₂⟩ := hlam y 0 n ψ₀ τ₁ hψ hτ₁
  obtain ⟨u₂, hu₂⟩ : ∃ u : (DualNumber k)ˣ, (u : DualNumber k) = 1 + TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i)) :=
    ⟨⟨_, 1 - TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i)),
      by ext <;> simp, by ext <;> simp⟩, rfl⟩
  have hu₁ : ((u₂ * ee : (DualNumber k)ˣ) : DualNumber k) = 1 + TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y z : k)) * MvPowerSeries.constantCoeff (q i)) := by
    rw [Units.val_mul, hu₂, hee]
    have hs : ∀ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y z : k)) * MvPowerSeries.constantCoeff (q i) =
        (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i) -
          (((-1 : ℚ) : k) * MvPowerSeries.constantCoeff (q i) * (gam i y z : k)) := by
      intro i
      simp only [map_zero, Int.cast_zero, add_zero, Rat.cast_neg, Rat.cast_one]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_sub_distrib]
    ext <;> simp
    ring
  have A := he₁ (max e₁ e₂) (le_max_left _ _) (u₂ * ee) hu₁ zz J hJ
  have B := he₂ (max e₁ e₂) (le_max_right _ _) u₂ hu₂ zz J hJ
  rw [hv₁ _ (spMap ρ) zz J hJ, hv₁ _ (spMap (constHom ρ)) zz J hJ] at B
  have hW : ∀ a : P.D.toPre.X, a = y →
      gm (c' a) zz _ (w.s (fun _ => J (c' a ≫ π₂), fun _ => J (c' a ≫ π₁))) =
        gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))) := by
    rintro a rfl; rfl
  rw [hW (y + 0) (add_zero y)] at B
  have hG : gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn (u₂ * ee)) =
      gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn u₂) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) := by
    rw [← map_mul]; congr 1; simp only [unitOn, map_mul]
  rw [hG] at A
  exact alg (hA := A) (hB := B)

end GlobalTheory.UnitsAlong
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitPart_periods_constant_along_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ c : ℚ, c ≠ 0 ∧ ∃ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen ∧ ∀ y z τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam y z τ₀ → ∀ e : (DualNumber k)ˣ, (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, (c : k) * MvPowerSeries.constantCoeff (q i) * gam i y z) → ∀ zz J, Good P.D.toPre.P.L zz J → val τ₀ (spMap ρ) zz J = gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) * (gm (c' (y)) zz _ (w.s (fun _ => J (c' (y) ≫ π₂), fun _ => J (c' (y) ≫ π₁))))⁻¹ * (gm (c' (z)) zz _ (w.s (fun _ => J (c' (z) ≫ π₂), fun _ => J (c' (z) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) * val τ₀ (spMap (constHom ρ)) zz J := by
  atlas_forward_decl GlobalTheory.UnitsAlong.unitTau_along
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSFlatPer

theorem isConstAlong_of_heat_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ
  obtain ⟨B', inst, π₁, π₂, h₁, h₂, h₃⟩ := GlobalTheory.T.abelian_part_constant_heat_operator_symbol_in_maximal_ideal E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ
  choose c' hc' using GlobalTheory.T.heatOperators_symbol_zero_torsion_points_horizontal E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ B' π₁ π₂ h₁ h₂ h₃
  obtain ⟨c, hc, w, hw, hrel⟩ := GlobalTheory.T.unitPart_periods_constant_along_tangent E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ B' π₁ π₂ c' h₁ h₂ h₃ hc'
  exact ⟨c, hc, B', inst, π₁, π₂, w, c', h₁, h₂, h₃, hw, hc', hrel⟩

end GlobalTheory.KSFlatPer
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_constant_of_flat_heatOperators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  atlas_forward_decl GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat
end

section
section
set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSConst

theorem isConstAlong_of_ks_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab n v hv hb D q hq Θ hKS hΘ ρ hρ
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m d
  haveI : IsNoetherianRing (ChartRing k m d) := hA.1
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) := hA.2.2.2
  letI := H.starRing
  obtain ⟨Y⟩ : Nonempty (Ray P.oD) := inferInstance
  obtain ⟨n', v', dd, hdd⟩ := GlobalTheory.T.exists_basis_raynaudTangent_invariantFields (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h0 => by
    have h4 := congrArg (fun f : ChartRing k m d => MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1) f) h0
    simp [bdParam, MvPowerSeries.coeff_X] at h4
  have f1 : ∀ x y, D (x + y) = D x + D y := D.map_add
  have f2 : ∀ (z : ℤ) (x : ChartRing k m d), D (z • x) = z • D x := fun z x => map_zsmul D z x
  have f3 : D 1 = 0 := D.map_one_eq_zero
  have f4 : ∀ x y, D (x * y) = x • D y + y • D x := D.leibniz
  obtain ⟨h, hB, hD⟩ : ∃ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
    generalize (⇑D : ChartRing k m d → ChartRing k m d) = f at f1 f2 f3 f4 hq ⊢
    letI : Algebra ℤ (ChartRing k m d) := Ring.toIntAlgebra _
    let D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d) :=
      { toFun := f, map_add' := f1, map_smul' := fun z x => f2 z x, map_one_eq_zero' := f3, leibniz' := f4 }
    exact GlobalTheory.T.exists_torusInvariant_heatOperator_commuting_periods (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd m (bdParam k m d) gam hmon hne D'
      (fun i => by
        show f (bdParam k m d i) ∈ _
        rw [hq i]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  exact GlobalTheory.T.degenerationData_constant_of_flat_heatOperators E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hB hD
    (GlobalTheory.T.heat_symbol_mem_maximalIdeal_of_kodairaSpencer_zero E H k m d t P gam hmon hli hab n v hv hb Y n' v' dd hdd D q hq h hB hD Θ hKS hΘ) ρ hρ
end GlobalTheory.KSConst
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConstAlong_of_kodairaSpencer_zero_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  atlas_forward_decl GlobalTheory.KSConst.isConstAlong_of_ks_zero
end
