import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymplecticSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameIsValueAtThetaConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFrameSqOfTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCoordPtLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsionFrame_sq_of_torsion : ∀ (S : Scheme.{0}) (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ) (T : Over S) (x : T ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))), IsTorsFrame P rig n x τ → IsTorsFrame P rig (n ^ 2) x τ := by
  first | exact @GlobalTheory.USep.isTorsFrame_sq | exact GlobalTheory.USep.isTorsFrame_sq | (intros; apply GlobalTheory.USep.isTorsFrame_sq <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GenLocal

theorem exists_gen_unit_point : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)), t.IsGen := by
  intro V _ _ _ D b
  choose i hi using fun k : Fin 2 =>
    exists_chart D.P.isLB ((![(η[D.P.A]).left, b.left] k) (closedPoint V))
  exact AbSquare.exists_gen_of_mem_chart D.P.isLB _ _ i fun k y => by
    have : (![(η[D.P.A]).left, b.left] k) ⁻¹ᵁ D.P.L.U (i k) = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
    exact (this.ge trivial : y ∈ (![(η[D.P.A]).left, b.left] k) ⁻¹ᵁ D.P.L.U (i k))

end GlobalTheory.GenLocal
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_translatedBundle_integralPoint : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)), t.IsGen := by
  atlas_forward_decl GlobalTheory.GenLocal.exists_gen_unit_point
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_function_thetaSection_integralPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ f : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ b.left) z J * (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom f) * (val ρ₀ r z J).val := by
  first | exact @GlobalTheory.IntPointFn.fn_of_theta | exact GlobalTheory.IntPointFn.fn_of_theta | (intros; apply GlobalTheory.IntPointFn.fn_of_theta <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.UT.CoefZeroInt

theorem coef_zero_int : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (th : Fam D (FractionRing V) 1), ∃ lam : FractionRing V, ∀ (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b → ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w 0 (th.s 0) x → ∀ z J, Good D.P.L z J → cst (FractionRing V) z x * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = cst (FractionRing V) z lam * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J * (val w (𝟙 _) z J).val := by
  intro V _ _ D θ hθ th
  obtain ⟨lam, hlam, -⟩ := existsUnique_scalar D θ hθ (FractionRing V) th
  refine ⟨lam, fun g b hb w x hx z J hJ => ?_⟩
  have h1 := hx z J hJ
  rw [pow_one] at h1
  rw [h1]
  have hs : sval (th.s 0) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J =
      sval (famProj D (FractionRing V) 1 0 th) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J := rfl
  have hfst : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ famBase D (FractionRing V) = 𝟙 _ := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (fst (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.prB D (FractionRing V)).left =
      (toUnit (TF (R := V) (FractionRing V))).left ≫ b.left := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (snd (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_snd, hb, Over.comp_left]
  have hv : (Geo.Tor.val (g.s 0) (𝟙 (TF (R := V) (FractionRing V)).left) z J).val = 1 := by
    rw [val_corr hJ g.s_zero, val_one]; rfl
  have e1 := sval_smul' (π := famBase D (FractionRing V)) hJ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left lam (termF D (FractionRing V) 1 0 θ)
  have e2 := sval_pullOver (L := D.P.L) (ε := DegPre.famε 1) (prB_hom' D (FractionRing V)) (famφ_prB D (FractionRing V) 0) θ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left hJ
  have hc : constVal (𝟙 (TF (R := V) (FractionRing V)).left) z lam = cst (FractionRing V) z lam := rfl
  rw [hs, hlam, e1, hfst]
  erw [e2]
  rw [hsnd, hv, _root_.mul_one, hc]

end GlobalTheory.UT.CoefZeroInt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_term_zero_integral_torusPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (th : Fam D (FractionRing V) 1), ∃ lam : FractionRing V, ∀ (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b → ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w 0 (th.s 0) x → ∀ z J, Good D.P.L z J → cst (FractionRing V) z x * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = cst (FractionRing V) z lam * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J * (val w (𝟙 _) z J).val := by
  atlas_forward_decl GlobalTheory.UT.CoefZeroInt.coef_zero_int
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.Poinc.Sep.FrameInt

theorem exists_rescale_gen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (u : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t' r z J = gm r z ⊤ u * val t r z J := by
  refine ⟨⟨fun j => t.s j * res le_top u⟩, fun i j => ?_, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, ht i j, _root_.mul_assoc]
    refine congrArg (fun q => _ * (_ * q)) (unit_ext fun y hy => ?_)
    exact ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · exact (map_mul _ _ _).trans ((mul_comm _ _).trans (congrArg (· * _) (gm_res r z le_top (hJ.mem φ r) u)))

end GlobalTheory.Poinc.Sep.FrameInt

namespace GlobalTheory.Poinc.Sep.FrameInt

theorem gs_top_eq {V : Type} [CommRing V] [IsDomain V] (a : V) (z : (TF (R := V) (FractionRing V)).left) :
    gs (toUnit (TF (R := V) (FractionRing V))).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  rw [toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

theorem map_map_unit {V : Type} [CommRing V] (ε : Vˣ) :
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom ε) : Vˣ) : V) = ε := by
  show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ε) = ε
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Poinc.Sep.FrameInt

open GlobalTheory.Poinc.Sep.FrameInt in

theorem GlobalTheory.Poinc.Sep.FrameInt.integral_terms : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)) (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))) (s₀ : V₁), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ (m ^ 2) = 1 → ∃ c, p = toUnit _ ≫ b c) ∧ (∀ c, (t c).IsGen) ∧ (∀ c (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)), Normd κ → ∀ (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → val (t c) r z J ^ ((m ^ 2) ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧ (∀ c (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c).left) z J * (val (t c) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (s₀ * u 0 c)) * (val ρ₀ r z J).val) := by
  intro m hm hm3 V₁ _ _ _ hV hk D X C _ e u mo hmo hT θ hθ ρ₀ hρ₀
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨th, g, b, w, hgb, -, hcov, hw, hcoef, ⟨c₀, hc₀⟩, hbN, hfr, -⟩ :=
    thetaTerms_integral D hN1 e _ hT

  have ht : ∀ c, ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)), t.IsGen ∧
      ∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J = val (w c) (𝟙 _) z J := by
    intro c
    obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_generator_translatedBundle_integralPoint V₁ D (b c)
    obtain ⟨ε, hε⟩ := hfr c t' ht'
    obtain ⟨t, htg, htv⟩ := exists_rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε)
    refine ⟨t, htg, fun z J hJ => Units.ext ?_⟩
    rw [htv _ _ z J hJ, Units.val_mul, hε z J hJ, gm_top_eq, map_map_unit]
  choose t htg htv using ht

  obtain ⟨ν, hν⟩ := exists_ratio (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.P.isLB rfl ρ₀ D.rig hρ₀ D.rig_gen
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.thetaFamily_term_zero_integral_torusPoint V₁ D θ hθ th
  choose f hf using fun c => GlobalTheory.T.exists_function_thetaSection_integralPoint V₁ D θ (b c) (t c) (htg c) ρ₀ hρ₀
  obtain ⟨z⟩ := exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have hTF : (TF (R := V₁) (FractionRing V₁)).hom = (toUnit (TF (R := V₁) (FractionRing V₁))).left := by
    simpa using (Over.w (toUnit (TF (R := V₁) (FractionRing V₁)))).symm
  set ν' : V₁ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom.toMonoidHom ν with hν'
  have key : ∀ c, algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) =
      lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' := by
    intro c
    have h0 := hcoef 0 c
    rw [show e 0 = 0 from map_zero e] at h0
    have a := hlam (g c) (b c) (hgb c) (w c) _ h0 z J hJ
    rw [← htv c z J hJ, _root_.mul_assoc, hf c _ _ z J hJ, gs_top_eq,
      hν _ _ z J hJ, Units.val_mul, gm_top_eq, rigV, hTF] at a
    have a' : cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0)) *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val =
        cst (FractionRing V₁) z (lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν') *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val := by
      rw [a, cst_eq, cst_eq, cst_eq, cst_eq, map_mul, map_mul]
      ring
    exact cst_inj z ((Units.isUnit _).mul_left_inj.1 a')

  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  have hlam0 : lam ≠ 0 := by
    intro h
    have := key c₀
    rw [h, zero_mul, zero_mul] at this
    have h1 : u 0 c₀ * mo 0 = 1 := hc₀
    rw [h1, map_one] at this
    exact one_ne_zero this
  have hν0 : algebraMap V₁ (FractionRing V₁) (ν' : V₁) ≠ 0 :=
    (IsUnit.map (algebraMap V₁ (FractionRing V₁)) ν'.isUnit).ne_zero
  have cross : ∀ c, f c * u 0 c₁ = f c₁ * u 0 c := by
    intro c
    apply hinj
    have k1 := key c
    have k2 := key c₁
    have : lam * algebraMap V₁ (FractionRing V₁) ν' *
        algebraMap V₁ (FractionRing V₁) (f c * u 0 c₁) =
        lam * algebraMap V₁ (FractionRing V₁) ν' * algebraMap V₁ (FractionRing V₁) (f c₁ * u 0 c) := by
      rw [map_mul, map_mul]
      have e1 : lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) = algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) := by rw [k1]
      have e2 : lam * algebraMap V₁ (FractionRing V₁) (f c₁) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c) = algebraMap V₁ (FractionRing V₁) (u 0 c₁ * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c) := by rw [k2]
      simp only [map_mul] at e1 e2
      linear_combination e1 - e2
    exact mul_left_cancel₀ (mul_ne_zero hlam0 hν0) this
  refine ⟨b, t, f c₁ * ↑(hc₁.unit⁻¹), hcov, htg, ?_, ?_⟩
  · intro c κ hκ Z r z' J' hJ'
    refine GlobalTheory.T.integralFrame_identity_of_genericPoint V₁ D (m ^ 2) (b c) (hbN c) (t c) (htg c) κ hκ (fun y I hI => ?_) Z r z' J' hJ'
    rw [htv c y I hI]
    have := (hw c).2 κ hκ y I hI
    rwa [show (g c).b.left = (toUnit (TF (R := V₁) (FractionRing V₁))).left ≫ (b c).left from
      congrArg (fun q => q.left) (hgb c)] at this
  · intro c Z r z' J' hJ'
    have hs : f c = f c₁ * ↑(hc₁.unit⁻¹) * u 0 c := by
      rw [mul_right_comm, ← cross c, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]
    rw [hf c Z r z' J' hJ', hs]
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_thetaTerms_torsionPoints_frames : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)) (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))) (s₀ : V₁), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ (m ^ 2) = 1 → ∃ c, p = toUnit _ ≫ b c) ∧ (∀ c, (t c).IsGen) ∧ (∀ c (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)), Normd κ → ∀ (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → val (t c) r z J ^ ((m ^ 2) ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧ (∀ c (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c).left) z J * (val (t c) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (s₀ * u 0 c)) * (val ρ₀ r z J).val) := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.FrameInt.integral_terms
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

noncomputable section

namespace GlobalTheory.ThetaFibreScalar

theorem famφB_zero {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) :
    D.famφB 0 = ![𝟙 _, 𝟙 _, (toUnit D.P.A ≫ η[D.P.A]).left, (toUnit D.P.A ≫ η[D.P.A]).left] := by
  have h0 := GlobalTheory.Mum.degPre_c_zero D
  have e1 : toUnit D.P.A ≫ D.c 0 = toUnit D.P.A ≫ η[D.P.A] := by
    rw [h0, comp_one, Hom.one_def]
  have e2 : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0) = 𝟙 D.P.A := by
    rw [h0, comp_one, padd, ← Hom.mul_def, _root_.mul_one]
  have e2' : padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A]) = 𝟙 D.P.A := by rw [← e1]; exact e2
  funext i
  fin_cases i <;> simp [DegPre.famφB, e1, e2']

theorem thetaFibre_scalar : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (K : Type) [Field K] (ev : V₁ →+* K) (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), ∃ Λ : K, ∀ (Z : Scheme) (r : Z ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left) (z : Z) J, Good D.P.L z J → sval th r z J = gs (r ≫ (fst (Over.mk (spMap ev)) D.P.A).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J := by
  intro V₁ _ _ D θ hθ K _ ev th
  have hF : FormEq (fun _ : Fin 1 => (snd (Over.mk (spMap ev)) D.P.A).left) (fun _ => ((1 : ℕ) : ℤ))
      (fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i) (DegPre.famε 1) := by
    intro U _ h
    rw [famφB_zero]
    simp [Fin.prod_univ_four, DegPre.famε]
  obtain ⟨th', hth'⟩ := exists_sec D.P.isLB hF th
  obtain ⟨r, hr, -⟩ := hθ K ev (pullTo D ev θ) (isPullSecLC_pullTo D ev θ) th'
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (r 0), fun Z rr z J hJ => ?_⟩
  refine (hth' Z rr z J hJ).symm.trans ?_
  have hm := hJ.mem (fun i => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 i) rr
  have h2 := sval_of (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J
      (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k)) (fun k => by rw [Category.assoc])
  erw [h2]
  rw [sval]
  erw [hr]
  rw [Fin.sum_univ_one]
  erw [gs_mul _ _ _ hm]
  congr 1
  · erw [gs_res rr z le_top hm]
    have := gs_pull rr (fst (Over.mk (spMap ev)) D.P.A).left z ⊤ trivial (r 0)
    refine this.trans ?_
    congr 1
    simp [GlobalTheory.Ex.fnOf]
  · have hle := wchart_comp_le D.P.L (D.famφB 0) (snd (Over.mk (spMap ev)) D.P.A).left
      (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k))
    erw [isPullSecLC_pullTo D ev θ, gs_res rr z hle hm]
    exact gs_pull rr (snd (Over.mk (spMap ev)) D.P.A).left z
      (LB.wchart D.P.L (D.famφB 0) (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k))) (hle hm)
      (θ.f (fun k => J (rr ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k)))

end GlobalTheory.ThetaFibreScalar
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFibre_section_eq_scalar_mul_integralTheta : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (K : Type) [Field K] (ev : V₁ →+* K) (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), ∃ Λ : K, ∀ (Z : Scheme) (r : Z ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left) (z : Z) J, Good D.P.L z J → sval th r z J = gs (r ≫ (fst (Over.mk (spMap ev)) D.P.A).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (snd (Over.mk (spMap ev)) D.P.A).left) z J := by
  atlas_forward_decl GlobalTheory.ThetaFibreScalar.thetaFibre_scalar
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

namespace GlobalTheory.USep.FrameRoot

theorem exists_normd {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (ρ : LB.Gen (D.P.L.pull (eSec D.P.A)))
    (hρ : ρ.IsGen) (n : ℕ)
    (α : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, (mulA D.P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (hα : α.IsGen) (hn : IsNormMul D.P.A D.P.L ρ n α) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
        val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ := by
  have hL := D.P.isLB
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ D.P.A.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ α p) (LB.invGen D.P.L _ _ (GeneratorPullback.powGen D.P.L _ _ p (n ^ 2)))
  have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hα hp)
    (DVR.invGen_isGen _ _ _ _ (DVR.SectionScalarValuation.powGen_isGen' _ _ _ _ hp _))
  have h1 : (1 : D.P.A ⟶ D.P.A).left = D.P.A.hom ≫ eSec D.P.A := rfl
  obtain ⟨κ, hκ, hv⟩ := exists_gen hL
    (φ' := (![𝟙 _, (𝟙 D.P.A ^ n).left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → (D.P.A.left ⟶ D.P.A.left)))
    (ε' := ![((n ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)]) (by
      intro U _ h
      rw [h1]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) u hu
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      val κ r z J = val α r z J * val ρ (r ≫ D.P.A.hom) z J * (val ρ (r ≫ D.P.A.hom) z J ^ (n ^ 2))⁻¹ :=
    fun Z r z J hJ => by
      have a : val p r z J = val ρ (r ≫ D.P.A.hom) z J := val_pull hJ _ _ _
      refine (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg _ a)) ((val_inv _ _).trans (congrArg (·⁻¹) ?_))))
      exact (GlobalTheory.RatioVal.val_powGen _ _ _ _ _).trans (congrArg (· ^ (n ^ 2)) a)
  refine ⟨κ, ⟨hκ, corr_of_val hL fun y J hJ => ?_⟩, key⟩
  have a₃ : val (rigPow D.P.A D.P.L ρ ((n : ℤ) ^ 2)) (𝟙 _) y J = val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have e₁ : (𝟙 _ ≫ eSec D.P.A) ≫ D.P.A.hom = 𝟙 _ := by
    rw [Category.id_comp]; exact Over.w η[D.P.A]
  have b := (val_pull hJ α (eSec D.P.A) (𝟙 _)).symm.trans ((val_corr hJ hn (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₃ (val_inv ρ (𝟙 _)))))
  refine (val_pull hJ κ _ _).trans ((key _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
  rw [b]
  refine (congrArg (fun q => val ρ (𝟙 _) y J ^ ((n : ℤ) ^ 2) * (val ρ (𝟙 _) y J)⁻¹ * val ρ q y J *
    (val ρ q y J ^ (n ^ 2))⁻¹) e₁).trans ?_
  rw [← Nat.cast_pow, zpow_natCast, inv_mul_cancel_right, mul_inv_cancel]

theorem val_rigT {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (T : Over S) (k : ℤ) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J : (Z ⟶ P.A.left) → P.L.ι} (hJ : Good P.L z J) :
    val (rigT P.A P.L rig T k) r z J = val rig (r ≫ T.hom) z J ^ k := by
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec P.A))
    (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec P.A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hm _).trans (gm_pull r T.hom z
    (LB.wchart P.L (fun _ : PUnit => eSec P.A) (fun _ => J (r ≫ T.hom ≫ eSec P.A)))
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _)

theorem exists_root {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (T : Over (Sp V))
    (ρ : LB.Gen (D.P.L.pull (eSec D.P.A))) (hρ : ρ.IsGen) (n : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A)
    (τ : LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := Fin 1) (fun _ => (toUnit T ≫ b).left) (fun _ => 1)))
    (hτ : IsTorsFrame D.P ρ n (toUnit T ≫ b) τ)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (ht : t.IsGen)
    (H : ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : T.left) J, Good D.P.L z J →
      val t T.hom z J ^ (n ^ 2) * val κ (T.hom ≫ b.left) z J = 1) :
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ (n ^ 2) = 1 ∧ ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := by
  have hL := D.P.isLB
  obtain ⟨-, hτg, α, hα, hn, hc⟩ := hτ
  obtain ⟨κ, hκ, hv⟩ := exists_normd D ρ hρ n α hα hn
  have hx : (toUnit T ≫ b).left = T.hom ≫ b.left := rfl
  let p := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) ρ T.hom
  have hp : p.IsGen := DVR.pullGen_isGen _ _ _ _ hρ _
  let q := LB.pullGen D.P.L _ _ t T.hom
  have hq : q.IsGen := DVR.pullGen_isGen _ _ _ _ ht _
  obtain ⟨u, hu, hw⟩ := exists_gen hL (φ' := fun _ : PUnit => T.hom ≫ eSec D.P.A) (ε' := fun _ => 1) (by
      intro U _ h
      rw [hx]
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, DegPre.lineε, eSec, mul_comm, mul_left_comm])
    (LB.mulGen D.P.L _ _ _ _ τ q) (DVR.mulGen_isGen _ _ _ _ _ _ _ hτg hq)
  obtain ⟨c, hcv⟩ := GlobalTheory.CoordSep.exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _)
    (fun a => ⟨a, rfl⟩) hu hp
  have key : ∀ (z : T.left) J, Good D.P.L z J →
      val τ (𝟙 _) z J * val t T.hom z J = gm (𝟙 T.left) z ⊤ c * val ρ T.hom z J := fun z J hJ => by
    have a : val p (𝟙 _) z J = val ρ T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have a' : val q (𝟙 _) z J = val t T.hom z J := (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
    have e := hcv _ (𝟙 _) z J hJ
    rw [hw _ _ z J hJ, val_mul hJ, a, a', Category.id_comp, mul_comm (val ρ T.hom z J)] at e
    exact e
  refine ⟨c, unit_ext fun z _ => ?_, key⟩
  choose J hJ using fun χ : T.left ⟶ D.P.A.left => exists_chart hL (χ z)
  replace hJ : Good D.P.L z J := hJ
  have e₁ : (T.hom ≫ b.left) ≫ D.P.A.hom = T.hom := Over.w (toUnit T ≫ b)
  have h₁ := H κ hκ z J hJ
  rw [hv _ _ z J hJ, e₁] at h₁
  have a₃ : val (powFrame D.P.A D.P.L _ τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
  have h₂ := a₃.symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_pull hJ α _ _) (val_rigT D.P ρ T 1 _ hJ))))
  replace h₂ : val τ (𝟙 _) z J ^ (n ^ 2) = val α (T.hom ≫ b.left) z J * val ρ T.hom z J := by
    rw [← zpow_natCast, Nat.cast_pow, h₂, zpow_one, Category.id_comp, Category.id_comp, hx]
  have h₃ := congrArg (· ^ (n ^ 2)) (key z J hJ)
  simp only [mul_pow] at h₃
  rw [map_pow, map_one]
  have aux : ∀ {U : Type} [CommGroup U] (a s g r r' w : U), s * (w * r' * r⁻¹) = 1 → a = w * r' → a * s = g * r →
      g = 1 := by
    rintro U _ a s g r r' w h rfl h'
    rw [← h, ← _root_.mul_assoc, mul_comm s, h', mul_inv_cancel_right]
  exact aux _ _ _ _ _ _ h₁ h₂ h₃

theorem frame_mul_eq_root : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  intro V₁ _ _ D K _ ev ρ₀ hρ n _ b τ hτ t ht H
  obtain ⟨c, hc, hv⟩ := exists_root D (Over.mk (spMap ev)) ρ₀ hρ n b τ hτ t ht H
  let e : Γ((Over.mk (spMap ev)).left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have he : ∀ a : K, GlobalTheory.Ex.fnOf a = e.symm a := fun _ => rfl
  refine ⟨e c.val, ?_, fun z J hJ => ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  · rw [he, e.symm_apply_apply, gs_unit _ _ ⊤ trivial, ← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hv z J hJ)

end GlobalTheory.USep.FrameRoot
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFrame_mul_integralFrame_eq_root_mul_rig : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  atlas_forward_decl GlobalTheory.USep.FrameRoot.frame_mul_eq_root
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

noncomputable section

namespace GlobalTheory.USep.FrameInt

theorem frameValue_eq_lam_root_mul : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (x : Over.mk (spMap ev) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : K), IsTorsFrame D.P ρ₀ (m ^ 2) x τ → IsValueAt D.P.A D.P.L ((1 : ℕ) : ℤ) th x (powFrame D.P.A D.P.L x τ ((1 : ℕ) : ℤ)) (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro m hm hm3 V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth
  obtain ⟨θ, hθ, -⟩ := ThetaOne.main hV D
  obtain ⟨b, t, s₀, hcov, htg, hκ, hid⟩ := GlobalTheory.T.integral_thetaTerms_torsionPoints_frames m hm hm3 V₁ hV hunit D X C e u mo hmo hT θ hθ ρ₀ hρ₀
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.thetaFibre_section_eq_scalar_mul_integralTheta V₁ D θ hθ K ev th
  refine ⟨(m ^ 2) ^ 2, Λ * ev s₀, Nat.one_le_pow _ _ (by positivity), ?_⟩
  intro x τ c hτ hval
  obtain ⟨c₀, rfl⟩ := hcov K (spMap ev) x hτ.1
  obtain ⟨ζ, hζ, hζv⟩ := GlobalTheory.T.torsionFrame_mul_integralFrame_eq_root_mul_rig V₁ D K ev ρ₀ hρ₀ (m ^ 2) (Nat.one_le_pow _ _ (by omega)) (b c₀) τ hτ (t c₀) (htg c₀)
    (fun κ hκn z J hJ => hκ c₀ κ hκn _ _ z J hJ)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hζ
    exact zero_ne_one hζ
  refine ⟨c₀, ζ⁻¹, by rw [inv_pow, hζ, inv_one], ?_⟩
  let z : (Over.mk (spMap ev)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  choose J hJ using fun χ : (Over.mk (spMap ev)).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have hG : Good D.P.L z J := hJ
  have h1 := GlobalTheory.CoordSep.sv_value hval hG
  have h2 := hΛ _ (lift (𝟙 _) (toUnit _ ≫ b c₀)).left z J hG
  have h3 := hid c₀ _ (Over.mk (spMap ev)).hom z J hG
  have h4 := hζv z J hG
  have eT : (toUnit (Over.mk (spMap ev))).left = (Over.mk (spMap ev)).hom := by
    simpa using Over.w (toUnit (Over.mk (spMap ev)))
  have e1 : (lift (𝟙 (Over.mk (spMap ev))) (toUnit _ ≫ b c₀)).left ≫ (fst (Over.mk (spMap ev)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have e2 : (lift (𝟙 (Over.mk (spMap ev))) (toUnit _ ≫ b c₀)).left ≫ (snd (Over.mk (spMap ev)) D.P.A).left =
      (Over.mk (spMap ev)).hom ≫ (b c₀).left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left, eT]
  rw [e1, e2] at h2
  rw [GlobalTheory.UT.NonVan.val_powFrame] at h1
  have e11 : val τ (𝟙 (Over.mk (spMap ev)).left) z J ^ (((1 : ℕ) : ℤ)) = val τ (𝟙 (Over.mk (spMap ev)).left) z J := zpow_one _
  rw [e11] at h1
  dsimp only [GlobalTheory.VVRank.sv] at h1
  let G : K →+* (Over.mk (spMap ev)).left.presheaf.stalk z := RatioVal.germConst K z
  have g1 : ∀ a : K, gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf a) = G a := fun a => RatioVal.gs_id_const z a
  have g2 : ∀ a : V₁, gs (Over.mk (spMap ev)).hom z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom a) = G (ev a) :=
    fun a => (RatioVal.gs_specMap ev z _).trans (congrArg (fun y => G (ev y))
      (by rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]))
  have g3 : gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf Λ) = G Λ := g1 Λ
  rw [g1] at h1 h4
  rw [g3] at h2
  rw [g2] at h3
  have key : G (c * ζ) * ↑(val ρ₀ (Over.mk (spMap ev)).hom z J) =
      G (Λ * ev (s₀ * u 0 c₀)) * ↑(val ρ₀ (Over.mk (spMap ev)).hom z J) := by
    rw [map_mul, map_mul, _root_.mul_assoc, ← h4, ← _root_.mul_assoc, ← h1, h2, _root_.mul_assoc, h3, _root_.mul_assoc]
  have key2 := (Units.mul_left_inj _).1 key
  have key3 : c * ζ = Λ * ev (s₀ * u 0 c₀) := G.injective key2
  rw [map_mul] at key3
  field_simp
  linear_combination key3

end GlobalTheory.USep.FrameInt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGenerator_torsionFrame_value_eq_scalar_mul_root : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (x : Over.mk (spMap ev) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : K), IsTorsFrame D.P ρ₀ (m ^ 2) x τ → IsValueAt D.P.A D.P.L ((1 : ℕ) : ℤ) th x (powFrame D.P.A D.P.L x τ ((1 : ℕ) : ℤ)) (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  atlas_forward_decl GlobalTheory.USep.FrameInt.frameValue_eq_lam_root_mul
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem GlobalTheory.USep.thetaConst_eq_lam_root_mul : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro n hn hodd
  refine ⟨1, fun j hj V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth => ?_⟩
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, rfl⟩
    omega
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  obtain ⟨M, lam, hM, H⟩ := GlobalTheory.T.thetaGenerator_torsionFrame_value_eq_scalar_mul_root (n ^ j) (hodd.pow) hm3 V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hth
  refine ⟨M, lam, hM, fun y c hc => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant (Sp V₁) D.P ρ₀ hρ₀ (n ^ j) (hodd.pow) _ th y _ hc
  exact H (y ^ n ^ j) τ c (GlobalTheory.T.isTorsionFrame_sq_of_torsion _ D.P ρ₀ (n ^ j) _ (y ^ n ^ j) τ hτ) hv
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_thetaConstants_eq_scalar_mul_root : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  atlas_forward_decl GlobalTheory.USep.thetaConst_eq_lam_root_mul
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.Poinc.Sep.ModelRatio

theorem main : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o : Type) [CommRing o] (J : Type) (b : ZM.TBase o ((n ^ j) ^ 2)) (s : Sp K ⟶ Sp o) (t : ZM.TObj g ((n ^ j) ^ 2) J b s) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ → LBIso t.L (D.P.L.pull π₁) → ∀ v : ZM.Ix g ((n ^ j) ^ 2) → K, t.HasTh (𝟙 _) v → ∀ a a', v a' ≠ 0 → ∃ r ∈ k₀, v a = r * v a' := by
  intro g n hn hodd
  obtain ⟨j₀, hcore⟩ := GlobalTheory.T.normalised_thetaConstants_eq_scalar_mul_root n hn hodd
  refine ⟨j₀, fun j hj V₁ _ _ _ hV hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat o _ J b s t π₁ hp hL v hv a a' hne => ?_⟩
  haveI : IsAlgClosed k₀ := hk₀
  have := t.ab.comm
  obtain ⟨ρ₀, hρ₀⟩ := D.P.rigid
  obtain ⟨w, hw⟩ := hL
  obtain ⟨ρ, hρ, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw D.P.isLB t.isLB hρ₀
  let x : ZM.Ix g ((n ^ j) ^ 2) → (baseOver (Sp K) ⟶ t.pol.A) :=
    fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab a
  have hx : ∀ i, x i ^ ((n ^ j) ^ 2) = 1 := fun i => by
    show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab i) ^ ((n ^ j) ^ 2) = 1
    rw [← MonObj.comp_pow, GlobalTheory.ThetaPtUp.lab_pow t i, MonObj.comp_one]
  obtain ⟨thP, hg, hth⟩ := GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants K t.pol ρ hρ (n ^ j) _ x v hx hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk (spMap ev)).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw D.P.isLB t.isLB thP
  have hgen := GlobalTheory.ThetaPtUp.isGenSec_up hp τ hτ hw D.P.isLB t.isLB hrel hg
  obtain ⟨M, lam, hM, hval⟩ := hcore j hj V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hgen
  have up : ∀ i, ∃ c₀ : C, ∃ ζ : K, ζ ^ M = 1 ∧ v i = lam * ζ * ev (u 0 c₀) := fun i => by
    obtain ⟨y, hy, hy'⟩ := GlobalTheory.Ex.OneGen.exists_torsion_up hp τ hτ (x i) (hx i)
    have q := GlobalTheory.Ex.OneGen.ThG.up hp τ hτ hw D.P.isLB t.isLB hr hy hy' hrel (hth i)
    rw [hi] at q
    exact hval y (v i) q
  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  obtain ⟨c₀, ζ, hζ, hva⟩ := up a
  obtain ⟨c₀', ζ', hζ', hva'⟩ := up a'
  obtain ⟨s₁, hs₁, hs₁e⟩ := hrat 0 c₀ c₁ hc₁
  obtain ⟨s₂, hs₂, hs₂e⟩ := hrat 0 c₀' c₁ hc₁
  have hζk : ζ ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)
  have hζk' : ζ' ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ']; exact k₀.one_mem)
  rw [hva', hs₂e] at hne
  have h₁ : ζ' * s₂ ≠ 0 := fun h => hne (by rw [show lam * ζ' * (s₂ * ev (u 0 c₁)) = lam * (ζ' * s₂) * ev (u 0 c₁) by ring, h]; ring)
  refine ⟨ζ * s₁ * (ζ' * s₂)⁻¹, k₀.mul_mem (k₀.mul_mem hζk hs₁) (k₀.inv_mem (k₀.mul_mem hζk' hs₂)), ?_⟩
  rw [hva, hva', hs₁e, hs₂e]
  have e₁ : ζ * s₁ * (ζ' * s₂)⁻¹ * (lam * ζ' * (s₂ * ev (u 0 c₁))) =
      ζ * s₁ * ((ζ' * s₂)⁻¹ * (ζ' * s₂)) * (lam * ev (u 0 c₁)) := by ring
  rw [e₁, inv_mul_cancel₀ h₁]
  ring

end GlobalTheory.Poinc.Sep.ModelRatio
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_fibre_thetaConstants_ratios_mem_subfield : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o : Type) [CommRing o] (J : Type) (b : ZM.TBase o ((n ^ j) ^ 2)) (s : Sp K ⟶ Sp o) (t : ZM.TObj g ((n ^ j) ^ 2) J b s) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ → LBIso t.L (D.P.L.pull π₁) → ∀ v : ZM.Ix g ((n ^ j) ^ 2) → K, t.HasTh (𝟙 _) v → ∀ a a', v a' ≠ 0 → ∃ r ∈ k₀, v a = r * v a' := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.ModelRatio.main
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep.DescentBaseChange

theorem unitS_subfield {K : Type} [Field K] (k₀ : Subfield K) (u : k₀ˣ) :
    ZM.unitS (spMap k₀.subtype ≫ spMap (RingHom.id k₀)) u = unitOn (Units.map k₀.subtype.toMonoidHom u) := by
  ext
  simp only [ZM.unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (k₀.subtype.comp (RingHom.id k₀)))
  exact (congrArg (fun f => f.hom (u : k₀)) this).symm

theorem tObj_of_baseChange : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (N : ℕ), (N : K) ≠ 0 → ∀ (J : Type) (b : ZM.TBase k₀ N), ∃ (t : ZM.TObj D.P.g N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀))) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
  intro V₁ _ _ D K _ _ ev k₀ N hN J b
  obtain ⟨L1, -⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨P, φ, hφ, hg, hm, w, hw⟩ := L1.polBaseChange _ _ (spMap ev) D.P
  have hpb : IsGrpPullback P.A D.P.A (spMap ev) φ := by
    refine ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
    rfl
  let ze : Kˣ := Units.map k₀.subtype.toMonoidHom b.ζ
  have hze : IsPrimitiveRoot ze N := IsPrimitiveRoot.coe_units_iff.1 (b.prim K k₀.subtype)
  obtain ⟨pt, hpt, hpw⟩ := GlobalTheory.EllipticLevel.exists_symplectic_system L1 P N hN ze hze
  have hu := unitS_subfield k₀ b.ζ
  have key : ∀ g', P.g = g' → ∃ (t : ZM.TObj g' N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀)))
      (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
    rintro _ rfl
    exact ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := P.L, isLB := P.isLB, rigid := P.rigid, sym := P.sym
             ample := P.ample, ktriv := P.ktriv, pt := pt, torsion := hpt
             bij := GlobalTheory.symplectic_system_torsion_basis L1 K P N ze pt hN hze hpt hpw
             pairing := hu ▸ hpw
             act := fun _ => 𝟙 _, hom := fun _ => inferInstance }, φ, hpb, LBIso.symm ⟨w, hw⟩⟩
  exact key _ hg

theorem tBase_of_isAlgClosed (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharZero k₀] (N : ℕ) (hN : N ≠ 0) : Nonempty (ZM.TBase k₀ N) := by
  haveI : NeZero (N : k₀) := ⟨Nat.cast_ne_zero.2 hN⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N k₀)
    (Polynomial.degree_cyclotomic_pos N k₀ (Nat.pos_of_ne_zero hN)).ne'
  have hp : IsPrimitiveRoot z N := (Polynomial.isRoot_cyclotomic_iff).1 hz
  exact ⟨⟨(hp.isUnit (Nat.pos_of_ne_zero hN).ne').unit, (Nat.cast_ne_zero.2 hN : (N : k₀) ≠ 0).isUnit,
    fun K _ β => hp.map_of_injective β.injective⟩⟩

theorem polarised_part_model : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' D.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen := by
  intro g n hn hodd
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points L1 L2 g Empty (fun x => x.elim) 0 n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.geometric_fibre_thetaConstants_ratios_mem_subfield g n hn hodd
  refine ⟨max (max j₁ j₂) 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hDg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hu
  have hj1 : j₁ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hj2 : j₂ ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hj3 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hK : ∀ m : ℕ, m ≠ 0 → (m : K) ≠ 0 := fun m hm => by
    rw [← map_natCast ev]; exact ((hunit m hm).map ev).ne_zero
  haveI : CharZero k₀ := charZero_of_inj_zero fun m hm => by
    by_contra h
    exact hK m h (by simpa using congrArg k₀.subtype hm)
  have hN0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  obtain ⟨b⟩ := tBase_of_isAlgClosed k₀ ((n ^ j) ^ 2) hN0
  obtain ⟨t, π₁, hπ, hL⟩ := tObj_of_baseChange V₁ D K ev k₀ ((n ^ j) ^ 2) (hK _ hN0) Empty b
  subst hDg
  obtain ⟨v, hv⟩ := ZM.TObj.exists_hasTh_of_isLocalRing L1 L2 (hodd.pow) t
  have hspan := ZM.FamilyScheme.span_theta L1 L2 t n v hn.two_le (dvd_pow_self n (by omega)) hv
  obtain ⟨a', ha'⟩ : ∃ a', v a' ≠ 0 := by
    by_contra h
    push_neg at h
    have : Set.range v ⊆ {0} := by rintro _ ⟨a, rfl⟩; exact h a
    rw [Ideal.span_eq_bot.2 (fun x hx => this hx)] at hspan
    exact bot_ne_top hspan
  have hr := hj₂ j hj2 V₁ hCN hunit D rfl X C e u mo hmo hT K ev k₀ hk₀ hu k₀ Empty b _ t π₁ hπ hL v hv
  choose r hrk hr using fun a => hr a a' ha'
  let w : ZM.Ix D.P.g ((n ^ j) ^ 2) → k₀ := fun a => ⟨r a, hrk a⟩
  have hw : t.HasTh (𝟙 _) (fun a => k₀.subtype (w a)) :=
    GlobalTheory.GenericObject.hasTh_unit_mul t _ v _ (v a')⁻¹ (isUnit_iff_ne_zero.2 (inv_ne_zero ha')) (fun a => by
      show r a = (v a')⁻¹ * v a
      rw [hr a, mul_comm (r a), ← _root_.mul_assoc, inv_mul_cancel₀ ha', _root_.one_mul]) hv
  have hd : ZM.VeryDense (ZM.objPrimes b (fun x : Empty => x.elim) 0 (RingHom.id k₀) w) := by
    intro q f hq hf
    have hq0 : q = ⊥ := by
      rcases Ideal.eq_bot_or_top q with h | h
      · exact h
      · exact absurd h hq.ne_top
    subst hq0
    exact ⟨⊥, ⟨K, inferInstance, inferInstance, k₀.subtype, t, (RingHom.injective_iff_ker_eq_bot _).1 k₀.subtype_injective,
      fun x => x.elim, hw⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, -, hmap⟩ := hj₁ j hj1 k₀ b k₀ (RingHom.id k₀) w hd
  obtain ⟨φ, hφ, hφL, -, -⟩ := hmap K k₀.subtype t (fun x => x.elim) hw
  obtain ⟨w', hw'⟩ := LBIso.trans (pull_isLB D.P.isLB π₁) t.isLB (pull_isLB t₀.isLB φ) (LBIso.symm hL) hφL
  exact ⟨t₀.A, inferInstance, t₀.ab.comm, t₀.L, t.A, inferInstance, π₁, φ, w', t₀.ab, t₀.isLB, hπ, hφ, hw'⟩

end GlobalTheory.USep.DescentBaseChange
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianPart_model_over_subfield : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' D.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen := by
  atlas_forward_decl GlobalTheory.USep.DescentBaseChange.polarised_part_model
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.USep.Coords

open GlobalTheory GlobalTheory.UT.SymFrame GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank GlobalTheory.CoordSep GlobalTheory.UT.CoefBasic
open GlobalTheory.TorusExt GlobalTheory.Poinc.Sep GlobalTheory.Poinc.Sep.ConjPt

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

theorem psi_pow {N : ℕ} {b : 𝟙_ (Over (Sp V)) ⟶ D.P.A} (hb : b ^ N = 1) (Ψ : LB.Gen (psiLB D.P N b)) (hΨ : Ψ.IsGen)
    {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)} (hκ : Normd κ)
    (h₁ : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      val Ψ (1 : T ⟶ D.P.A).left z J ^ N * val κ (toUnit T ≫ b).left z J = 1)
    {T : Over (Sp V)} (x : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val Ψ x.left z J ^ N * val κ ((toUnit T ≫ b) * x).left z J = val κ x.left z J := by
  have key := ((((grep_gen (Y := D.P.A) Ψ hΨ (𝟙 _)).pow N).mul (grep_kap κ hκ.1 ((toUnit D.P.A ≫ b) * 𝟙 D.P.A))).mul
    (grep_kap κ hκ.1 (𝟙 D.P.A)).inv).triv GlobalTheory.abelianSchemeLaws_all.1.globalFns (fun U _ h => by
      rw [Fin.prod_univ_two, mul_pow (toUnit D.P.A ≫ b), ← MonObj.comp_pow, hb, MonObj.comp_one, _root_.one_mul]
      show (h (𝟙 _ ≫ 𝟙 _) ^ (N : ℤ) * h (𝟙 _ ≫ ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left) ^ (-(N : ℤ))) ^ N * _ * _ = _
      rw [Category.id_comp, Category.id_comp, Over.id_left]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, Category.comp_id, normd_one hκ hJ, MonObj.comp_mul, Category.comp_id, _root_.mul_one,
        ← Category.assoc, comp_toUnit, h₁ _ y J hJ, inv_one, _root_.mul_one]) T x z J hJ
  beta_reduce at key
  rw [Category.comp_id, Category.comp_id, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
    mul_inv_eq_one] at key
  exact key

theorem lift_pow {m : ℕ} {T : Over (Sp V)} {y : T ⟶ D.P.A} (hy : y ^ m ^ 2 = 1)
    (θ : ThetaGrp D.P.A D.P.L ((m : ℤ) ^ 2) T) (hθ : SymLift D.P.A D.P.L ((m : ℤ) ^ 2) (m ^ 2) y θ)
    (α : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(snd T D.P.A).left, (snd T D.P.A ^ m).left] ![(m : ℤ) ^ 2, -1]))
    (hα : α.IsGen) {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)} (hκ : κ.IsGen)
    (x : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    ((tval θ (lift (𝟙 T) x).left z J * val α (lift (𝟙 T) (y * x)).left z J) ^ (m ^ 2) ^ 2 *
      val κ (y ^ m * x ^ m).left z J) ^ m ^ 2 =
      (val α (lift (𝟙 T) x).left z J ^ (m ^ 2) ^ 2 * val κ (x ^ m).left z J) ^ m ^ 2 := by
  obtain rfl := hθ.pt_eq
  have hL := D.P.isLB
  have G := ((((grep_gen (Y := T ⊗ D.P.A) θ.φ θ.isGen (𝟙 _)).mul
    (grep_gen α hα (translT D.P.A θ.pt).left)).pow ((m ^ 2) ^ 2)).mul
      (grep_kap κ hκ ((fst T D.P.A ≫ θ.pt) ^ m * snd T D.P.A ^ m))).mul
    (((grep_gen α hα (𝟙 _)).pow ((m ^ 2) ^ 2)).mul (grep_kap κ hκ (snd T D.P.A ^ m))).inv
  obtain ⟨K, _, φ, ε, s, hs, h₁, h₂⟩ := G
  obtain ⟨a, ha⟩ := SymLiftOdd.exists_const hL (fst T D.P.A).left (lift (𝟙 T) (1 : T ⟶ D.P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (SymLiftOdd.surj_fst GlobalTheory.abelianSchemeLaws_all.1.globalFns D.P.isAb T)
    (fun U _ h => (h₁ U h).trans (by
      have e₁ : (translT D.P.A θ.pt).left ≫ (snd T D.P.A).left = ((fst T D.P.A ≫ θ.pt) * snd T D.P.A).left := by
        rw [← Over.comp_left, translT, lift_snd]; rfl
      have e₂ : (translT D.P.A θ.pt).left ≫ (snd T D.P.A ^ m).left =
          ((fst T D.P.A ≫ θ.pt) ^ m * snd T D.P.A ^ m).left := by
        rw [← Over.comp_left, MonObj.comp_pow, translT, lift_snd, ← mul_pow]; rfl
      have e₃ : ((fst T D.P.A ≫ θ.pt) ^ m * snd T D.P.A ^ m) ^ m ^ 2 = (snd T D.P.A ^ m) ^ m ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm m, pow_mul, ← MonObj.comp_pow, hy, MonObj.comp_one, one_pow, _root_.one_mul]
      beta_reduce
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two, e₃]
      show (h (𝟙 _ ≫ (snd T D.P.A).left) ^ ((m : ℤ) ^ 2) *
          h (𝟙 _ ≫ ((fst T D.P.A ≫ θ.pt) * snd T D.P.A).left) ^ (-((m : ℤ) ^ 2)) *
        (h ((translT D.P.A θ.pt).left ≫ (snd T D.P.A).left) ^ ((m : ℤ) ^ 2) *
          h ((translT D.P.A θ.pt).left ≫ (snd T D.P.A ^ m).left) ^ (-1 : ℤ))) ^ _ * _ *
        ((h (𝟙 _ ≫ (snd T D.P.A).left) ^ ((m : ℤ) ^ 2) * h (𝟙 _ ≫ (snd T D.P.A ^ m).left) ^ (-1 : ℤ)) ^ _ * _)⁻¹ = _
      rw [e₁, e₂, Category.id_comp, Category.id_comp, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      push_cast
      module)) hs
  let f : (T ⟶ D.P.A) → (T.left.presheaf.stalk z)ˣ := fun x =>
    val α (lift (𝟙 T) x).left z J ^ (m ^ 2) ^ 2 * val κ (x ^ m).left z J
  have key : ∀ x : T ⟶ D.P.A, tval θ (lift (𝟙 T) x).left z J ^ (m ^ 2) ^ 2 * f (θ.pt * x) =
      gm (𝟙 T.left) z ⊤ a * f x := fun x => by
    have e := (h₂ T (lift (𝟙 T) x) z J hJ).symm.trans (ha _ _ z J hJ)
    beta_reduce at e
    rw [lift_fst_left, Category.comp_id, lift_translT, Category.id_comp,
      MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow, lift_snd, ← Category.assoc, lift_fst, Category.id_comp,
      mul_inv_eq_iff_eq_mul, mul_pow, _root_.mul_assoc] at e
    simp only [f]
    rw [mul_pow θ.pt]
    exact e
  have hp : ∏ j ∈ Finset.range (m ^ 2), tval θ (lift (𝟙 T) (θ.pt ^ j * x)).left z J = 1 := by
    have c := val_corr hJ hθ.pow_eq (lift (𝟙 T) x).left
    rw [ThetaPullback.val_powGen θ _ _ hJ, val_one] at c
    rw [← c, Finset.prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [lift_translT, Category.id_comp]
    rfl
  have tel : ∀ n : ℕ, (∏ j ∈ Finset.range n, tval θ (lift (𝟙 T) (θ.pt ^ j * x)).left z J) ^ (m ^ 2) ^ 2 *
      f (θ.pt ^ n * x) = gm (𝟙 T.left) z ⊤ a ^ n * f x := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, mul_pow, _root_.mul_assoc, pow_succ' θ.pt, _root_.mul_assoc θ.pt, key,
        mul_left_comm, ih, pow_succ', _root_.mul_assoc]
  have ha1 := tel (m ^ 2)
  rw [hp, hy, one_pow, _root_.one_mul, _root_.one_mul, eq_comm, mul_eq_right] at ha1
  have k := congrArg (· ^ m ^ 2) (key x)
  simp only [f] at k
  rw [mul_pow (gm _ _ _ _), ha1, _root_.one_mul, mul_pow θ.pt, ← _root_.mul_assoc, ← mul_pow] at k
  exact k

theorem exists_scalar {K R : Type} [Field K] [CommRing R] (φ : K →+* R) (hφ : Function.Injective φ) (k₀ : Subfield K)
    [IsAlgClosed k₀] {M : ℕ} (hM : 1 ≤ M) {I : Type} (v : I → K) (Λ : R)
    (h : ∀ i, ∃ r ∈ k₀, φ (v i) ^ M = Λ * φ r) :
    ∃ (l : K) (r : I → K), (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  by_cases h0 : ∀ i, v i = 0
  · exact ⟨0, fun _ => 0, fun _ => k₀.zero_mem, fun i => by rw [h0, zero_mul]⟩
  obtain ⟨i₀, hi₀⟩ := not_forall.1 h0
  obtain ⟨r₀, m₀, e₀⟩ := h i₀
  have hr₀ : r₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, ← map_pow, map_eq_zero_iff φ hφ] at e₀
    exact pow_ne_zero M hi₀ e₀
  refine ⟨v i₀, fun i => v i / v i₀, fun i => ?_, fun i => (mul_div_cancel₀ _ hi₀).symm⟩
  obtain ⟨r, m₁, e₁⟩ := h i
  have e : v i ^ M * r₀ = r * v i₀ ^ M := hφ (by
    rw [map_mul, map_mul, map_pow, map_pow, e₀, e₁]; ring)
  refine Frames.mem_of_pow_mem k₀ hM (x := v i / v i₀) ?_
  rw [div_pow, (div_eq_div_iff (pow_ne_zero M hi₀) hr₀).2 e]
  exact k₀.div_mem m₁ m₀

theorem coords_scalar [IsLocalRing V] [IsNoetherianRing V] [IsIntegrallyClosed V] (D : DegPre V) {m : ℕ} (hm : 1 ≤ m)
    {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V) (mo : X → V) (a : D.X)
    (hmo : mo (e.symm (m • a)) ≠ 0) (c₀ : C) (hu : IsUnit (u (e.symm (m • a)) c₀))
    (hT : IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu))
    {K : Type} [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K) [IsAlgClosed k₀]
    (hr : ∀ c, ∃ r ∈ k₀, ev (u (e.symm (m • a)) c) = r * ev (u (e.symm (m • a)) c₀))
    {I : Type} (y : I → (Over.mk (spMap ev) ⟶ D.P.A)) (hy : ∀ i, y i ^ m ^ 2 = 1) (v : I → K)
    (H : GlobalTheory.Ex.IsCoordPt D.P m y (toUnit _ ≫ D.c a) (fun i => GlobalTheory.Ex.fnOf (v i))) :
    ∃ (l : K) (r : I → K), (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  have hL := D.P.isLB
  have hN : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  set mu := e.symm (m • a) with hmu
  have hc : ∀ n : ℕ, D.c (n • a) = D.c a ^ n := fun n => by
    induction n with
    | zero =>
      have h := D.c_add 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact mul_eq_left.1 h.symm
    | succ n ih => rw [succ_nsmul, D.c_add, ih, pow_succ]; rfl
  have hχ : D.c (e mu) = D.c a ^ m := by rw [hmu, e.apply_symm_apply, hc]
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, -⟩ := hT
  have hb : ∀ c, b c ^ m ^ 2 = 1 := fun c => (Frames.torsion_of_nsmul (g c) (b c) (h₁ c) (h₂ c)).2
  obtain ⟨θ, hθ⟩ := exists_genAll D.P
  choose Ψ hΨ nΨ vΨ using fun c => exists_psi hN (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c)
  obtain ⟨ρ, A, cross, hA⟩ := exists_vals hθ (m ^ 2) (e mu) (th.s (e mu)) g b h₁ w Ψ hΨ (fun c => vΨ c (e mu)) _ (h₅ mu)
  obtain ⟨κ, hκ⟩ := exists_kap (D := D) GlobalTheory.abelianSchemeLaws_all.1.mulPull (m ^ 2)
  have hv : ∀ c, ∃ r ∈ k₀, ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (A c)) =
      r * ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (A c₀)) := fun c => by
    obtain ⟨r, r₁, r₂⟩ := hr c
    have x := cross c c₀
    rw [mul_pow, mul_pow, mul_right_comm, mul_right_comm (u mu c₀ ^ m ^ 2)] at x
    have x' := congrArg ev (mul_right_cancel₀ (pow_ne_zero _ hmo) x)
    rw [map_mul, map_mul, map_pow, map_pow, r₂] at x'
    refine ⟨r ^ m ^ 2, k₀.pow_mem r₁ _, mul_left_cancel₀ (pow_ne_zero (m ^ 2) (hu.map ev).ne_zero) (x'.symm.trans ?_)⟩
    ring
  obtain ⟨-, -, t, s₁, α, τ, U, s₂, -, hα, -, hs₁, hU, hs₂, hval⟩ := H
  obtain ⟨k, hk⟩ := hθ K (spMap ev) t
  let T : Over (Sp V) := Over.mk (spMap ev)
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨J, hJ⟩ := exists_good' hL p
  have alg : ∀ {R : Type} [CommRing R] (N : ℕ) (v k t A A₀ r : R) (τ P α Ψ ρ κ κ' : Rˣ), v * τ.val = P.val * (k * t) →
      A = t ^ N * (Ψ * ρ ^ N).val → A = r * A₀ → Ψ ^ N * κ' = κ → (P ^ N ^ 2 * κ') ^ N = (α ^ N ^ 2 * κ) ^ N →
      v ^ N ^ 3 = (((α * τ⁻¹ * ρ⁻¹).val * k) ^ N ^ 3 * A₀ ^ N ^ 2) * r ^ N ^ 2 := by
    intro R _ N v k t A A₀ r τ P α Ψ ρ κ κ' a₁ a₂ a₃ a₄ a₅
    have a₆ : (P * τ⁻¹) ^ N ^ 3 = (α * τ⁻¹ * ρ⁻¹) ^ N ^ 3 * (Ψ * ρ ^ N) ^ N ^ 2 := by
      subst a₄
      have a := congrArg Additive.ofMul a₅
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ← natCast_zsmul] at a ⊢
      push_cast at a ⊢
      linear_combination (norm := module) a
    have a₇ : v = (P * τ⁻¹).val * (k * t) := by
      rw [Units.val_mul, mul_right_comm, ← a₁, Units.mul_inv_cancel_right]
    rw [_root_.mul_assoc, ← mul_pow A₀, mul_comm A₀, ← a₃, a₂, a₇, mul_pow, ← Units.val_pow_eq_pow_val, a₆,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    ring
  refine exists_scalar (GlobalTheory.RatioVal.germConst K p) (RingHom.injective _) k₀ (M := (m ^ 2) ^ 3) (Nat.one_le_pow _ _ hN) v
    (@id (T.left.presheaf.stalk p) (((val α (lift (𝟙 T) (toUnit T ≫ D.c a)).left p J * (val τ (𝟙 T.left) p J)⁻¹ *
      (val ρ T.hom p J)⁻¹).val * gs (𝟙 T.left) p ⊤ k) ^ (m ^ 2) ^ 3 * (@id (T.left.presheaf.stalk p) <| GlobalTheory.RatioVal.germConst K p
        (ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (A c₀)))) ^ (m ^ 2) ^ 2)) fun i => ?_
  obtain ⟨c, hc'⟩ := h₃ K (spMap ev) (y i ^ m) (by rw [← pow_mul, mul_comm m, pow_mul, hy, one_pow])
  obtain ⟨r, r₁, r₂⟩ := hv c
  refine ⟨r ^ (m ^ 2) ^ 2, k₀.pow_mem r₁ _, ?_⟩
  have ez : (toUnit T ≫ D.c a) ^ m = toUnit T ≫ D.c (e mu) := by rw [hχ, MonObj.comp_pow]
  have e₁ := sv_value (hval i) hJ
  rw [sv_act (hU i).pt_eq (hs₂ i) _ hJ, sv_mulPull hs₁ _ hJ, hk _ _ p J hJ, lift_fst_left, ← Over.comp_left, lift_snd,
    Category.id_comp, mul_pow, ez, hc', ← _root_.mul_assoc, ← Units.val_mul] at e₁
  have e₂ := (GlobalTheory.RatioVal.gs_specMap ev p _).symm.trans (hA c T p J hJ)
  have e₃ := psi_pow (hb c) (Ψ c) (hΨ c) hκ (nΨ c κ hκ) (toUnit T ≫ D.c (e mu)) p J hJ
  have e₄ := lift_pow (hy i) (U i) (hU i) α hα hκ.1 (toUnit T ≫ D.c a) p J hJ
  rw [ez, hc'] at e₄
  rw [map_pow]
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((congrArg (· * _) (GlobalTheory.RatioVal.gs_id_const p (v i)).symm).trans e₁.symm) e₂
    ((congrArg _ r₂).trans (map_mul _ _ _)) e₃ e₄

end GlobalTheory.USep.Coords

open NumberField ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef GlobalTheory GlobalTheory.USep

theorem GlobalTheory.USep.coords_scalar_mul_rational : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (I : Type) (y : I → (Over.mk (spMap ev) ⟶ D.P.A)), (∀ i, y i ^ (n ^ j) ^ 2 = 1) → ∀ (a : D.X) (z : Over.mk (spMap ev) ⟶ D.P.A), z.left = spMap ev ≫ (D.c a).left → ∃ (v : I → K) (l : K) (r : I → K), GlobalTheory.Ex.IsCoordPt D.P (n ^ j) y z (fun i => GlobalTheory.Ex.fnOf (v i)) ∧ (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  intro g n hn hodd
  refine ⟨0, fun j _ V₁ _ _ _ hV hunit D _ X C _ e u mo hu hT K _ _ ev k₀ hk₀ hr I y hy a z hz => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hm : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have hK : ((n ^ j : ℕ) : K) ≠ 0 := by
    have := ((hunit (n ^ j) (by omega)).map ev).ne_zero
    rwa [map_natCast] at this
  obtain rfl : z = toUnit _ ≫ D.c a := Over.OverMorphism.ext hz
  obtain ⟨v, hv⟩ := (GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp V₁) D.P (spMap ev)
    (n ^ j) hodd.pow hK I y hy).1 (toUnit _ ≫ D.c a)
  obtain ⟨hmo, c₀, hc₀⟩ := hu (e.symm ((n ^ j) • a))
  obtain ⟨l, r, h₁, h₂⟩ := Coords.coords_scalar D hm e u mo a hmo c₀ hc₀ hT ev k₀ (fun c => hr _ c c₀ hc₀) y hy v hv
  exact ⟨v, l, r, hv, h₁, h₂⟩
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionCoordinates_scalar_mul_subfieldValued : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (I : Type) (y : I → (Over.mk (spMap ev) ⟶ D.P.A)), (∀ i, y i ^ (n ^ j) ^ 2 = 1) → ∀ (a : D.X) (z : Over.mk (spMap ev) ⟶ D.P.A), z.left = spMap ev ≫ (D.c a).left → ∃ (v : I → K) (l : K) (r : I → K), GlobalTheory.Ex.IsCoordPt D.P (n ^ j) y z (fun i => GlobalTheory.Ex.fnOf (v i)) ∧ (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  atlas_forward_decl GlobalTheory.USep.coords_scalar_mul_rational
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem defOver_of_coord_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 →
    ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K)
      (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K),
      GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) →
      (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  intro K _ _ k₀ hk₀ P₀ m hm hm3 hmK z v l r H hr hv
  classical
  let Ix := {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1}
  have Lw := GlobalTheory.abelianSchemeLaws_all
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hm2K : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hmK
  have hcard := (Lw.1.mulN (Sp k₀) P₀ (m ^ 2) hm1).2.2.2.2 K (spMap k₀.subtype) hm2K
  have hfin : Finite Ix := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))

  have hσs : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
    intro σ hσ
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ w.2

  have hfix : ∀ (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) (y : Ix),
      (Over.homMk (spMap σ.toRingHom) (hσs σ hσ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1 = y.1 := by
    intro σ hσ y
    have hdef : DefOver k₀ y.1.left := by
      refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y' : Ix => y'.1.left).subset ?_)
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨⟨(Over.homMk (spMap τ.toRingHom) (hσs τ hτ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1, ?_⟩, ?_⟩
      · rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      · rfl
    obtain ⟨y₀, hy₀⟩ := hdef
    apply Over.OverMorphism.ext
    show spMap σ.toRingHom ≫ y.1.left = y.1.left
    rw [← hy₀, ← Category.assoc, hσs σ hσ]

  obtain ⟨-, U₂, -, U₄⟩ := CoordSep.coord_exists_unique_separate Lw.1 K (Sp k₀) P₀ (spMap k₀.subtype) m hm hmK Ix
    (fun i => i.1) (fun i => i.2)
  have hall : ∀ y : Over.mk (spMap k₀.subtype) ⟶ P₀.A, y ^ m ^ 2 = 1 → ∃ i : Ix, i.1 = y := fun y hy => ⟨⟨y, hy⟩, rfl⟩
  have hv0 : v ≠ 0 := (U₄ hm3 hall z z v H H).2
  have hl : l ≠ 0 := by
    intro h0
    apply hv0
    funext i
    rw [hv i, h0, zero_mul, Pi.zero_apply]
  have horb : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ z.left = z.left := by
    intro σ hσ
    let h : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype) := Over.homMk (spMap σ.toRingHom) (hσs σ hσ)
    have H2 := CoordReduce.isCoordPt_map Lw.2 P₀ σ.toRingHom (hσs σ hσ) (p := fun i : Ix => i.1)
      (fun i => i.2) (w := v) H
    have hp : (fun i : Ix => h ≫ i.1) = fun i => i.1 := funext fun i => hfix σ hσ i
    change GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => h ≫ i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (σ (v i))) at H2
    rw [hp] at H2
    have hσl : σ l ≠ 0 := (map_ne_zero σ).2 hl
    have H3 : GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (v i)) := by
      refine (U₂ (h ≫ z) (fun i => σ (v i)) v H2).2 ⟨Units.mk0 (l / σ l) (div_ne_zero hl hσl), ?_⟩
      funext i
      simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
      rw [hv i, map_mul, hσ _ (hr i)]
      field_simp
    have := (U₄ hm3 hall (h ≫ z) z v H3 H).1
    have e2 := congrArg CommaMorphism.left this
    exact e2
  refine defOver_of_finite_orbit K k₀ hk₀ _ z.left ((Set.finite_singleton z.left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  exact horb σ hσ

end GlobalTheory.Poinc.Sep
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polAV_point_defined_over_of_coords_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 → ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K) (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K), GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) → (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.defOver_of_coord_proportional
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem points_defOver : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' D.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → ∀ (a : D.X) (x : Sp K ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ev ≫ (D.c a).left → GlobalTheory.Poinc.Sep.DefOver k₀ (x ≫ π₀) := by
  intro g n hn hodd
  obtain ⟨j₁, hC⟩ := GlobalTheory.T.torsionCoordinates_scalar_mul_subfieldValued g n hn hodd
  refine ⟨max j₁ 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat B₀ _ _ M₀ B' _ π₁ π₀ w hB₀ hM₀ h₁ h₀ hw a x hx hxa
  have hj₁ : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases Nat.lt_or_ge n 3 with h | h
    · have : n = 2 := by omega
      subst this; exact absurd hodd (by decide)
    · exact h
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ j := Nat.pow_le_pow_right hn.pos hj1)
  have hmK : ((n ^ j : ℕ) : K) ≠ 0 := by
    have h := (hunit (n ^ j) (by positivity)).map ev
    rw [map_natCast] at h
    exact h.ne_zero
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsCommMonObj D.P.A := D.P.isAb.comm
  haveI : IsCommMonObj B' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h₁
  let P' : PolAV (Sp K) := GlobalTheory.TorsionTauCompare.polOfPullback D.P B' h₁
  have hw' : LBIso P'.L (M₀.pull π₀) := ⟨w, hw⟩
  have hSym : Out.Sym B₀ M₀ := (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend k₀ K k₀.subtype B₀ B' π₀ M₀ P'.L hB₀ h₀
    hM₀ P'.isLB hw').2.1 P'.sym
  have h₀' : IsGrpPullback P'.A B₀ (spMap (algebraMap k₀ K)) π₀ := h₀
  have : Flat (spMap k₀.subtype) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  let P₀ : PolAV (Sp k₀) :=
    { A := B₀, isAb := hB₀, g := P'.g,
      smoothDim := GlobalTheory.CM.smoothOfRelativeDimension_of_fibre k₀ K k₀.subtype B₀ P'.A.left π₀ P'.A.hom P'.g hB₀ h₀.1
        P'.smoothDim,
      L := M₀, isLB := hM₀, rigid := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local M₀ hM₀ _ _, sym := hSym,
      ample := GlobalTheory.AmpleDescent.relAmple_of_faithfullyFlat k₀ K B₀ P'.A π₀ M₀ P'.L hB₀ h₀' hM₀ P'.isLB hw' P'.ample,
      ktriv := GlobalTheory.AmpleDescent.kTriv_of_pull h₀ hM₀ P'.isLB hw' P'.ktriv }
  obtain ⟨Φ₀, hΦ₀⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := B₀) (G' := B') h₀
    (𝟙 (Sp K)) (spMap k₀.subtype) (Category.id_comp _)
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := D.P.A) (G' := B') h₁
    (𝟙 (Sp K)) (spMap ev) (Category.id_comp _)
  let t₀ : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  let t₁ : Sp K ⟶ Sp V₁ := spMap ev
  let Ix := {y : Over.mk t₀ ⟶ B₀ // y ^ (n ^ j) ^ 2 = 1}
  let X' : Ix → (baseOver (Sp K) ⟶ B') := fun i => Φ₀.symm i.1
  have hX' : ∀ i, X' i ^ (n ^ j) ^ 2 = 1 := fun i => Φ₀.injective (by
    rw [map_pow, MulEquiv.apply_symm_apply, i.2, map_one])
  let z' : baseOver (Sp K) ⟶ B' := Over.homMk x hx
  let yD : Ix → (Over.mk t₁ ⟶ D.P.A) := fun i => Φ₁ (X' i)
  have hyD : ∀ i, yD i ^ (n ^ j) ^ 2 = 1 := fun i => by
    simp only [yD]; rw [← map_pow, hX' i, map_one]
  have hzD : (Φ₁ z').left = t₁ ≫ (D.c a).left := by
    rw [hΦ₁]; simp [t₁, z', hxa]
  obtain ⟨vD, l, r, hvD, hr, hvr⟩ := hC j hj₁ V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hrat
    Ix yD hyD a (Φ₁ z') hzD
  have HD := GlobalTheory.FullExtend.isCoordPt_move (f := spMap ev) (T := baseOver (Sp K)) (T₀ := Over.mk t₁) (𝟙 _)
    (P₀ := D.P) (P := P') (φ := π₁) h₁ (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.P.isLB π₁)) (B := Over.mk t₁)
    (𝟙 _) (𝟙 _) (by simp) (by simp [t₁])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS D.P.isLB (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := yD)
    (fun i => (Category.id_comp _).trans (hΦ₁ _)) hX' (z := z') (z₀ := Φ₁ z') ((Category.id_comp _).trans (hΦ₁ z')) hvD
  obtain ⟨v₀, hv₀⟩ := (GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp k₀) P₀ t₀ (n ^ j)
    hmodd hmK Ix (fun i => i.1) (fun i => i.2)).1 (Φ₀ z')
  have H0 := GlobalTheory.FullExtend.isCoordPt_move (f := spMap k₀.subtype) (T := baseOver (Sp K)) (T₀ := Over.mk t₀) (𝟙 _)
    (P₀ := P₀) (P := P') (φ := π₀) h₀ hw' (B := Over.mk t₀) (𝟙 _) (𝟙 _) (by simp) (by simp [t₀])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS hM₀ (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := fun i => i.1)
    (fun i => (Category.id_comp _).trans ((congrArg Over.Hom.left (Φ₀.apply_symm_apply i.1)).symm.trans (hΦ₀ _)))
    hX' (z := z') (z₀ := Φ₀ z') ((Category.id_comp _).trans (hΦ₀ z')) hv₀
  have HD' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (vD i)) := by
    convert HD using 2 with i
    simp
  have H0' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (v₀ i)) := by
    convert H0 using 2 with i
    simp
  obtain ⟨-, U₂, -, -⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp K) P' (𝟙 _)
    (n ^ j) hmodd hmK Ix X' hX'
  obtain ⟨c, hc⟩ := (U₂ z' v₀ vD H0').1 HD'
  have hv₀r : ∀ i, v₀ i = ((c⁻¹ : Kˣ) * l) * r i := fun i => by
    have := congrFun hc i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [_root_.mul_assoc, ← hvr i, this, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hD := GlobalTheory.T.polAV_point_defined_over_of_coords_proportional K k₀ hk₀ P₀ (n ^ j) hmodd hm3 hmK (Φ₀ z') v₀ _ r hv₀ hr hv₀r
  rwa [hΦ₀] at hD

end GlobalTheory.USep
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoints_defined_over_subfield_abelianModel : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' D.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → ∀ (a : D.X) (x : Sp K ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ev ≫ (D.c a).left → GlobalTheory.Poinc.Sep.DefOver k₀ (x ≫ π₀) := by
  atlas_forward_decl GlobalTheory.USep.points_defOver
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem descAt_of_thetaTerms : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → DescAt D ev k₀ := by
  intro g n hn hodd
  obtain ⟨j₁, h₁⟩ := GlobalTheory.T.polarisedAbelianPart_model_over_subfield g n hn hodd
  obtain ⟨j₂, h₂⟩ := GlobalTheory.T.torsionPoints_defined_over_subfield_abelianModel g n hn hodd
  refine ⟨max j₁ j₂, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hr
  obtain ⟨B₀, iG₀, iC₀, M₀, B', iG', π₁, π₀, w, hA, hM, hp1, hp0, hw⟩ :=
    h₁ j (le_trans (le_max_left _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
  have hP := h₂ j (le_trans (le_max_right _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
    B₀ M₀ B' π₁ π₀ w hA hM hp1 hp0 hw
  have hsq : ∀ a : D.X, (spMap ev ≫ (D.c a).left) ≫ D.P.A.hom = 𝟙 (Sp K) ≫ spMap ev := by
    intro a
    rw [Category.assoc, Over.w (D.c a)]
    simp
  let c' : D.X → (Sp K ⟶ B'.left) := fun a => hp1.1.lift (spMap ev ≫ (D.c a).left) (𝟙 _) (hsq a)
  have hc1 : ∀ a, c' a ≫ B'.hom = 𝟙 _ := fun a => hp1.1.lift_snd _ _ _
  have hc2 : ∀ a, c' a ≫ π₁ = spMap ev ≫ (D.c a).left := fun a => hp1.1.lift_fst _ _ _
  choose c₀ hc₀ using fun a => hP a (c' a) (hc1 a) (hc2 a)
  exact ⟨B₀, iG₀, iC₀, M₀, c₀, B', iG', π₁, π₀, w, c', hA, hM, hp1, hp0, hw, fun a => ⟨hc1 a, hc2 a, (hc₀ a).symm⟩⟩

end GlobalTheory.USep
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_descends_of_thetaTerms_ratios : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → DescAt D ev k₀ := by
  atlas_forward_decl GlobalTheory.USep.descAt_of_thetaTerms
end
