import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsOfGenericLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisFrameMap

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.ModelNoeth

theorem isLocallyNoetherian_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → IsLocallyNoetherian Y.X := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ _
  obtain ⟨⟨_, hD⟩, -, -⟩ :=
    (GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion E H l' c' (c'.V W)).1
  haveI : IsNoetherianRing (c'.V W) := hD.toIsNoetherian
  obtain ⟨N, i, hi, hcomp⟩ := Y.proj
  haveI := hi
  haveI := isProper_str (c'.V W) N
  haveI : LocallyOfFiniteType (i ≫ PSpace.str (c'.V W) N) := inferInstance
  haveI : LocallyOfFiniteType Y.s := hcomp ▸ this
  exact LocallyOfFiniteType.isLocallyNoetherian Y.s

end GlobalTheory.ModelNoeth
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_locally_noetherian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → IsLocallyNoetherian Y.X := by
  atlas_forward_decl GlobalTheory.ModelNoeth.isLocallyNoetherian_model
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.GenericFactor

theorem exists_factor_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (R : Type) [CommRing R] [IsDomain R] (ξ : Sp R ⟶ Y.X),
    ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range Y.j →
    ∃ y : Sp (FractionRing R) ⟶ Xo'.XF c', spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ _ R _ _ ξ hξ
  haveI := Y.jQ_open
  obtain ⟨u, hu⟩ := hξ
  let g₀ : Sp (FractionRing R) ⟶ Y.X := spMap (algebraMap R (FractionRing R)) ≫ ξ
  let φ : c'.V W →+* FractionRing R := (Spec.preimage (g₀ ≫ Y.s)).hom
  have hφ : spMap φ = g₀ ≫ Y.s := Spec.map_preimage _
  have hpt : ∀ q : Sp (FractionRing R), g₀ q = Y.j u := by
    intro q
    rw [hu]
    show ξ ((spMap (algebraMap R (FractionRing R))) q) = _
    congr 1
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R (FractionRing R)) q.asIdeal = ⊥
    rw [@Ideal.eq_bot_of_prime _ _ q.asIdeal (PrimeSpectrum.isPrime (self := q)), ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    let q : Sp (FractionRing R) := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 : ((spMap φ) q).asIdeal = RingHom.ker φ := by
      show Ideal.comap φ ⊥ = _
      exact (RingHom.ker_eq_comap_bot φ).symm
    have h2 : (spMap φ) q = Y.s (Y.j u) := by
      rw [hφ, ← hpt q]; rfl
    have h3 : Y.s (Y.j u) = (spMap (c'.V W).subtype) ((pullback.snd Y.s (spMap (c'.V W).subtype)) (Y.jQ u)) := by
      change (Y.j ≫ Y.s) u = (Y.jQ ≫ pullback.snd _ _ ≫ spMap (c'.V W).subtype) u
      rw [Model.j_s, ← Category.assoc, Y.jQ_over]
    rw [← h1, h2, h3]
    show Ideal.comap (c'.V W).subtype _ = ⊥
    have hF : ∀ z : Sp c'.F, z.asIdeal = ⊥ := fun z => @Ideal.eq_bot_of_prime _ _ z.asIdeal (PrimeSpectrum.isPrime (self := z))
    rw [hF, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective
  let ψ : c'.F →+* FractionRing R := IsFractionRing.lift hinj
  have hψ : ψ.comp (c'.V W).subtype = φ := IsLocalization.lift_comp _
  have hw : g₀ ≫ Y.s = spMap ψ ≫ spMap (c'.V W).subtype := by
    rw [← hφ, ← spMap_comp, hψ]
  let w : Sp (FractionRing R) ⟶ pullback Y.s (spMap (c'.V W).subtype) := pullback.lift g₀ (spMap ψ) hw
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen]
    show (w ≫ pullback.fst _ _) q ∈ abLocus Y.t.G
    rw [pullback.lift_fst, hpt q]
    have : Y.jQ u ∈ Set.range Y.jQ := ⟨u, rfl⟩
    rw [← Y.ab_gen] at this
    exact this
  refine ⟨IsOpenImmersion.lift Y.jQ w hr, ?_⟩
  show g₀ = _
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.GenericFactor
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_lift_to_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (R : Type) [CommRing R] [IsDomain R] (ξ : Sp R ⟶ Y.X),
    ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range Y.j →
    ∃ y : Sp (FractionRing R) ⟶ Xo'.XF c', spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j := by
  atlas_forward_decl GlobalTheory.GenericFactor.exists_factor_generic
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.HTLocWeil

theorem unit_of_root {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {N : ℕ} (hN : 0 < N)
    (c : Γ(Sp (FractionRing R), ⊤)ˣ) (hc : c ^ N = 1) :
    ∃ u : Rˣ, unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = c := by
  let c' : (FractionRing R)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c
  have hc' : c' ^ N = 1 := by rw [← map_pow, hc, map_one]
  have hint : ∀ x : (FractionRing R)ˣ, x ^ N = 1 → ∃ r : R, algebraMap R (FractionRing R) r = x := fun x hx => by
    have : IsIntegral R (x : FractionRing R) := IsIntegral.of_pow hN (by
      rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]; exact isIntegral_one)
    exact IsIntegrallyClosed.isIntegral_iff.1 this
  obtain ⟨r, hr⟩ := hint c' hc'
  obtain ⟨r', hr'⟩ := hint c'⁻¹ (by rw [inv_pow, hc', inv_one])
  have h1 : r * r' = 1 := IsFractionRing.injective R (FractionRing R) (by
    rw [map_mul, hr, hr', map_one, Units.mul_inv])
  refine ⟨⟨r, r', h1, by rw [mul_comm, h1]⟩, ?_⟩
  have : Units.map (algebraMap R (FractionRing R)).toMonoidHom ⟨r, r', h1, by rw [mul_comm, h1]⟩ = c' := Units.ext hr
  rw [this]
  ext : 1
  show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom (c : Γ(Sp (FractionRing R), ⊤))) = c
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

theorem unitOn_inj {R : Type} [CommRing R] {u v : Rˣ} (h : unitOn u = unitOn v) : u = v := by
  ext : 1
  have := congrArg (fun z : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z : Γ(Sp R, ⊤))) h
  simpa [unitOn, ← CommRingCat.comp_apply] using this

end GlobalTheory.HTLocWeil

namespace GlobalTheory.HTLocWeil

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
  {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype)
  {T : Scheme.{0}} (y : T ⟶ Xo'.XF c')

theorem lift_ex (w : Over.mk (y ≫ Y.j) ⟶ Y.t.G) : ∃ σ : Over.mk y ⟶ Y.oF.t.G, σ.left ≫ Y.m.φ = w.left :=
  ⟨Over.homMk (Y.m.cart.1.lift w.left y (Over.w w)) (Y.m.cart.1.lift_snd _ _ _), Y.m.cart.1.lift_fst _ _ _⟩

variable {Y y}

theorem lift_uniq {σ σ' : Over.mk y ⟶ Y.oF.t.G} (h : σ.left ≫ Y.m.φ = σ'.left ≫ Y.m.φ) : σ = σ' :=
  Over.OverMorphism.ext (Y.m.cart.1.hom_ext h (by rw [Over.w σ, Over.w σ']))

theorem mul_map {σ σ' : Over.mk y ⟶ Y.oF.t.G} {w w' : Over.mk (y ≫ Y.j) ⟶ Y.t.G} (h : w.left = σ.left ≫ Y.m.φ)
    (h' : w'.left = σ'.left ≫ Y.m.φ) : (w * w').left = (σ * σ').left ≫ Y.m.φ :=
  Y.m.cart.2 (Over.mk y) σ σ' w w' h h'

theorem one_map : (1 : Over.mk (y ≫ Y.j) ⟶ Y.t.G).left = (1 : Over.mk y ⟶ Y.oF.t.G).left ≫ Y.m.φ := by
  let z : Over.mk (y ≫ Y.j) ⟶ Y.t.G := Over.homMk ((1 : Over.mk y ⟶ Y.oF.t.G).left ≫ Y.m.φ) (by
    rw [Category.assoc, Y.m.cart.1.w, ← Category.assoc, Over.w (1 : Over.mk y ⟶ Y.oF.t.G)]; rfl)
  have hz : (z * z).left = z.left := by
    rw [mul_map (σ := 1) (σ' := 1) rfl rfl, _root_.mul_one]; rfl
  have : z = 1 := by
    have e : z * z = z * 1 := by rw [_root_.mul_one]; exact Over.OverMorphism.ext hz
    exact mul_left_cancel e
  rw [← this]; rfl

theorem pow_map {σ : Over.mk y ⟶ Y.oF.t.G} {w : Over.mk (y ≫ Y.j) ⟶ Y.t.G} (h : w.left = σ.left ≫ Y.m.φ) (k : ℕ) :
    (w ^ k).left = (σ ^ k).left ≫ Y.m.φ := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact one_map
  | succ k ih => rw [pow_succ, pow_succ]; exact mul_map ih h

theorem tors_lift {σ : Over.mk y ⟶ Y.oF.t.G} {w : Over.mk (y ≫ Y.j) ⟶ Y.t.G} (h : w.left = σ.left ≫ Y.m.φ) {k : ℕ}
    (hw : w ^ k = 1) : σ ^ k = 1 :=
  lift_uniq (by rw [← pow_map h, hw, one_map])

end GlobalTheory.HTLocWeil

namespace GlobalTheory.HTLocWeil

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
    {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype) (a : Dw.La)
    (k : ℕ) : Y.oF.etaA a ^ k = Y.oF.etaA (k • a) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_smul]
    have := Y.oF.etaA_ker 0
    rw [smul_zero] at this
    exact this.symm
  | succ k ih => rw [pow_succ, ih, succ_nsmul, Y.oF.etaA_add]

theorem weil_kappa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ a : Dw.La,
    ∃ κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ, GlobalTheory.HTMap.Mult Y.t ξ (p ^ n) κ ∧
      ∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ)))) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n hA R _ _ _ ξ y hy a
  classical
  have hN : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  let P : Out.PolAV (Xo'.XF c') := GlobalTheory.Obj.toPolAV Y.oF
  have hG := GlobalTheory.laws_without_cohomology.1
  let e0 : Over.mk y ⟶ Y.oF.t.G := toUnit (Over.mk y) ≫ Y.oF.etaA a
  have he0 : e0 ^ (p ^ n) = 1 := by
    show (toUnit (Over.mk y) ≫ Y.oF.etaA a) ^ (p ^ n) = 1
    rw [← MonObj.comp_pow, etaA_pow, ← hA, Y.oF.etaA_ker, MonObj.comp_one]
  let good : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ → Prop := fun w u =>
    ∃ σ : Over.mk y ⟶ Y.oF.t.G, σ.left ≫ Y.m.φ = w ∧ σ ^ (p ^ n) = 1 ∧
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u))
  let κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ := fun w => if h : ∃ u, good w u then h.choose else 1

  have ex : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 → ∃ u, good (σ.left ≫ Y.m.φ) u := fun σ hσ => by
    obtain ⟨c, hc, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) e0 σ he0 hσ
    obtain ⟨u, hu⟩ := unit_of_root hN c (GlobalTheory.TorsCoord.pow_eq_one_of_weilIs hG P hc he0)
    exact ⟨u, σ, rfl, hσ, hu ▸ hc⟩
  have val : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 →
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ)))) := fun σ hσ => by
    have h := ex σ hσ
    have hk : κ (σ.left ≫ Y.m.φ) = h.choose := dif_pos h
    obtain ⟨σ', e1, -, h2⟩ := h.choose_spec
    rw [hk]
    exact (lift_uniq e1) ▸ h2
  have uniq : ∀ σ : Over.mk y ⟶ Y.oF.t.G, σ ^ (p ^ n) = 1 → ∀ u v : Rˣ,
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom u)) →
      Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e0 σ
        (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom v)) → u = v := fun σ hσ u v hu hv => by
    have := (GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) e0 σ he0 hσ).unique hu hv
    have := unitOn_inj this
    ext : 1
    exact IsFractionRing.injective R (FractionRing R) (congrArg Units.val this)
  refine ⟨κ, fun w w' hw hw' => ?_, fun e σ he hσ => ?_⟩
  ·
    have hwy : ∀ v : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ ξ) ⟶ Y.t.G,
        v.left ≫ Y.t.G.hom = y ≫ Y.j := fun v => by rw [Over.w v]; exact hy
    let w₁ : Over.mk (y ≫ Y.j) ⟶ Y.t.G := Over.homMk w.left (hwy w)
    let w₁' : Over.mk (y ≫ Y.j) ⟶ Y.t.G := Over.homMk w'.left (hwy w')
    obtain ⟨σ, hσ⟩ := lift_ex Y y w₁
    obtain ⟨σ', hσ'⟩ := lift_ex Y y w₁'
    have t1 : σ ^ (p ^ n) = 1 := tors_lift hσ.symm (HTMap.tors_of (g := 𝟙 _)
      (show w₁.left = 𝟙 _ ≫ w.left from (Category.id_comp _).symm) hw)
    have t2 : σ' ^ (p ^ n) = 1 := tors_lift hσ'.symm (HTMap.tors_of (g := 𝟙 _)
      (show w₁'.left = 𝟙 _ ≫ w'.left from (Category.id_comp _).symm) hw')
    have t3 : (σ * σ') ^ (p ^ n) = 1 := by rw [mul_pow, t1, t2, _root_.one_mul]
    have hm : (w * w').left = (σ * σ').left ≫ Y.m.φ := by
      rw [HTMap.mul_of (g := 𝟙 _) (w₁ := w₁) (w₂ := w₁') (w₁' := w) (w₂' := w') (Category.id_comp _).symm (Category.id_comp _).symm,
        Category.id_comp]
      exact mul_map hσ.symm hσ'.symm
    have v1 := val σ t1
    have v2 := val σ' t2
    rw [hσ] at v1
    rw [hσ'] at v2
    have v3 := val (σ * σ') t3
    rw [← hm] at v3
    have sk := (GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk y)).1
    have v4 := sk _ _ _ (GlobalTheory.weilIs_mul_left hG _ P (p ^ n) (Over.mk y) σ σ' e0 _ _ (sk _ _ _ v1) (sk _ _ _ v2))
    refine uniq _ t3 _ _ v3 ?_
    have ceq : unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w.left * κ w'.left)) =
        ((unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w.left)))⁻¹ *
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ w'.left)))⁻¹)⁻¹ := by
      simp only [mul_inv, inv_inv, unitOn, map_mul]
    rw [ceq]
    exact v4
  · have he' : e = e0 := Over.OverMorphism.ext (by
      rw [he]; show _ = (toUnit (Over.mk y)).left ≫ _; congr 1)
    rw [he']
    exact val σ hσ

end GlobalTheory.HTLocWeil
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrally_closed_generic_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ a : Dw.La,
    ∃ κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ, GlobalTheory.HTMap.Mult Y.t ξ (p ^ n) κ ∧
      ∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ)))) := by
  atlas_forward_decl GlobalTheory.HTLocWeil.weil_kappa
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory

theorem spec_factor_localization_of_field_point : ∀ (U X : Scheme.{0}) (j : U ⟶ X) [IsOpenImmersion j] (R : Type) [CommRing R] (ξ : Sp R ⟶ X)
    (K' : Type) [Field K'] (χ : R →+* K') (yy : Sp K' ⟶ U), spMap χ ≫ ξ = yy ≫ j →
    ∀ (q : Ideal R) [q.IsPrime], RingHom.ker χ = q →
      ∃ yq : Sp (Localization.AtPrime q) ⟶ U, spMap (algebraMap R (Localization.AtPrime q)) ≫ ξ = yq ≫ j := by
  intro U X j _ R _ ξ K' _ χ yy h q _ hq
  have hopen : IsOpen (Set.range j) := j.isOpenEmbedding.isOpen_range
  let pt : Sp K' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K')
  have hpt : (spMap χ pt : PrimeSpectrum R) = (⟨q, inferInstance⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    change Ideal.comap χ ⊥ = q
    rw [← hq]; rfl
  have hmem : ξ (⟨q, inferInstance⟩ : PrimeSpectrum R) ∈ Set.range j := by
    refine ⟨yy pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
    exact congrArg ξ hpt
  refine ⟨IsOpenImmersion.lift j (spMap (algebraMap R (Localization.AtPrime q)) ≫ ξ) ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have hle : (spMap (algebraMap R (Localization.AtPrime q)) x : PrimeSpectrum R) ⤳
        (⟨q, inferInstance⟩ : PrimeSpectrum R) := by
      have hle' : Ideal.comap (algebraMap R (Localization.AtPrime q)) (x : PrimeSpectrum _).asIdeal ≤ q := by
        intro r hr
        by_contra hrq
        have hu : IsUnit (algebraMap R (Localization.AtPrime q) r) :=
          IsLocalization.map_units (Localization.AtPrime q) (⟨r, hrq⟩ : q.primeCompl)
        exact (x : PrimeSpectrum _).isPrime.ne_top ((Ideal.eq_top_of_isUnit_mem _ hr hu))
      exact (PrimeSpectrum.le_iff_specializes
        (spMap (algebraMap R (Localization.AtPrime q)) x : PrimeSpectrum R) ⟨q, inferInstance⟩).1 hle'
    exact (hle.map ξ.continuous).mem_open hopen hmem
  · exact (IsOpenImmersion.lift_fac _ _ _).symm

end GlobalTheory
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_to_prime_localization : ∀ (U X : Scheme.{0}) (j : U ⟶ X) [IsOpenImmersion j] (R : Type) [CommRing R] (ξ : Sp R ⟶ X)
    (K' : Type) [Field K'] (χ : R →+* K') (yy : Sp K' ⟶ U), spMap χ ≫ ξ = yy ≫ j →
    ∀ (q : Ideal R) [q.IsPrime], RingHom.ker χ = q →
      ∃ yq : Sp (Localization.AtPrime q) ⟶ U, spMap (algebraMap R (Localization.AtPrime q)) ≫ ξ = yq ≫ j := by
  atlas_forward_decl GlobalTheory.spec_factor_localization_of_field_point
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

theorem GlobalTheory.grpPullback_lift_torsion : ∀ (S S' : Scheme.{0}) (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (T : Over S') (w : Over.mk (T.hom ≫ f) ⟶ G),
      ∃ σ : T ⟶ G', σ.left ≫ φ = w.left ∧ ∀ k : ℕ, w ^ k = 1 → σ ^ k = 1 := by
  intro S S' G' _ G _ f φ h T w
  have uniq : ∀ a b : T ⟶ G', a.left ≫ φ = b.left ≫ φ → a = b := by
    intro a b e
    ext
    exact h.1.hom_ext e (by rw [Over.w a, Over.w b])
  let push : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w x])
  have push_left : ∀ x : T ⟶ G', (push x).left = x.left ≫ φ := fun x => rfl
  have hmul : ∀ x y : T ⟶ G', push (x * y) = push x * push y := by
    intro x y
    ext
    exact (h.2 T x y (push x) (push y) rfl rfl).symm
  have hone : push 1 = 1 := by
    have e : push 1 * push 1 = push 1 := by rw [← hmul, _root_.mul_one]
    simpa using e
  have hpow : ∀ (x : T ⟶ G') (k : ℕ), push (x ^ k) = push x ^ k := by
    intro x k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, pow_succ, hmul, ih]
  let σ : T ⟶ G' := Over.homMk (h.1.lift w.left T.hom (by simpa using Over.w w)) (h.1.lift_snd _ _ _)
  have hσ : σ.left ≫ φ = w.left := h.1.lift_fst _ _ _
  have hpσ : push σ = w := by ext; exact hσ
  refine ⟨σ, hσ, fun k hk => uniq _ _ ?_⟩
  rw [← push_left, ← push_left, hpow, hpσ, hk, hone]
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_section_pullback : ∀ (S S' : Scheme.{0}) (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (T : Over S') (w : Over.mk (T.hom ≫ f) ⟶ G),
      ∃ σ : T ⟶ G', σ.left ≫ φ = w.left ∧ ∀ k : ℕ, w ^ k = 1 → σ ^ k = 1 := by
  first | exact @GlobalTheory.grpPullback_lift_torsion | exact GlobalTheory.grpPullback_lift_torsion | (intros; apply GlobalTheory.grpPullback_lift_torsion <;> assumption)
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.WeilSpec

set_option maxHeartbeats 1000000 in
theorem weil_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ (a : Dw.La)
      (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ),
      (∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ))))) →
    ∀ (f : R) (wf : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ ξ) ⟶ Y.t.G), wf ^ (p ^ n) = 1 →
    ∀ (g : Localization.Away f →+* FractionRing R), g.comp (algebraMap R _) = algebraMap R (FractionRing R) →
    ∀ (x0 : R →+* 𝓞_ℂ_[p]) (φ : Localization.Away f →+* ℂ_[p]),
      φ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0 →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c'), spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap x0 ≫ ξ = yy ≫ Y.j →
    ∀ (e σ : Over.mk yy ⟶ Y.oF.t.G), e.left = yy ≫ (Y.oF.etaA a).left → σ.left ≫ Y.m.φ = spMap φ ≫ wf.left →
      σ ^ (p ^ n) = 1 ∧ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
        (unitOn (Units.map ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0).toMonoidHom (κ (spMap g ≫ wf.left)))) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n hp hA R _ _ _ ξ y hy a κ hκ f wf hwf g hg x0 φ hφ yy hyy e σ he hσ
  set χ : R →+* ℂ_[p] := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0 with hχ
  set q : Ideal R := RingHom.ker χ with hq
  haveI : q.IsPrime := RingHom.ker_isPrime χ
  haveI hj : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j (Fact.out) hp Y
  haveI hmono : Mono Y.j := GlobalTheory.PolArc.mono_j_of_valuationSubring _ Y
  have hyy' : spMap χ ≫ ξ = yy ≫ Y.j := by rw [← hyy, sp_sp]
  obtain ⟨yq, hyq⟩ := GlobalTheory.T.lift_to_prime_localization (Xo'.XF c') Y.X Y.j R ξ ℂ_[p] χ yy hyy' q rfl
  have hfq : f ∉ q := by
    intro hf
    have h1 : φ (algebraMap R (Localization.Away f) f) = χ f := by
      rw [← RingHom.comp_apply, hφ]
    have h2 : χ f = 0 := RingHom.mem_ker.1 hf
    have hu : IsUnit (algebraMap R (Localization.Away f) f) := IsLocalization.Away.algebraMap_isUnit f
    exact (hu.map φ).ne_zero (h1.trans h2)
  let Rq := Localization.AtPrime q
  let hf' : Localization.Away f →+* Rq :=
    IsLocalization.Away.lift f (g := algebraMap R Rq) (IsLocalization.map_units Rq (⟨f, hfq⟩ : q.primeCompl))
  have hhf' : hf'.comp (algebraMap R (Localization.Away f)) = algebraMap R Rq := IsLocalization.Away.lift_comp _ _
  have hχu : ∀ s : q.primeCompl, IsUnit (χ s) := fun s => by
    refine IsUnit.mk0 _ fun h0 => s.2 ?_
    exact RingHom.mem_ker.2 h0
  let ψq : Rq →+* ℂ_[p] := IsLocalization.lift (M := q.primeCompl) hχu
  have hψq : ψq.comp (algebraMap R Rq) = χ := IsLocalization.lift_comp _
  have hKu : ∀ s : q.primeCompl, IsUnit (algebraMap R (FractionRing R) s) := fun s => by
    refine IsUnit.mk0 _ fun h0 => s.2 ?_
    have : (s : R) = 0 := (IsFractionRing.injective R (FractionRing R)) (by rw [h0, map_zero])
    rw [this]; exact q.zero_mem
  let ιK : Rq →+* FractionRing R := IsLocalization.lift (M := q.primeCompl) hKu
  have hιK : ιK.comp (algebraMap R Rq) = algebraMap R (FractionRing R) := IsLocalization.lift_comp _
  have hιinj : Function.Injective ιK := by
    rw [IsLocalization.lift_injective_iff]
    intro u v
    rw [(IsLocalization.injective Rq q.primeCompl_le_nonZeroDivisors).eq_iff,
      (IsFractionRing.injective R (FractionRing R)).eq_iff]
  have hK : spMap ιK ≫ yq = y := by
    rw [← cancel_mono Y.j, Category.assoc, ← hyq, sp_sp, hιK, hy]
  have hC : spMap ψq ≫ yq = yy := by
    rw [← cancel_mono Y.j, Category.assoc, ← hyq, sp_sp, hψq, hyy']
  have hgK : ιK.comp hf' = g := IsLocalization.ringHom_ext (Submonoid.powers f) (by
    rw [RingHom.comp_assoc, hhf', hιK, hg])
  have hgC : ψq.comp hf' = φ := IsLocalization.ringHom_ext (Submonoid.powers f) (by
    rw [RingHom.comp_assoc, hhf', hψq, hφ])
  have hwq : (spMap hf' ≫ wf.left) ≫ Y.t.G.hom = yq ≫ Y.j := by
    rw [Category.assoc, Over.w wf]
    change spMap hf' ≫ spMap (algebraMap R (Localization.Away f)) ≫ ξ = _
    rw [sp_sp, hhf', hyq]
  let wq : Over.mk (yq ≫ Y.j) ⟶ Y.t.G := GlobalTheory.HTMap.mkPt (spMap hf' ≫ wf.left) hwq
  have hwqt : wq ^ (p ^ n) = 1 := GlobalTheory.HTMap.tors_of (g := spMap hf') (w := wf) rfl hwf
  obtain ⟨σq, hσq, htq⟩ := GlobalTheory.T.exists_torsion_section_pullback _ _ Y.oF.t.G Y.t.G _ Y.m.cm.F Y.m.cart (Over.mk yq) wq
  have hσqt : σq ^ (p ^ n) = 1 := htq _ hwqt
  let P := GlobalTheory.Obj.toPolAV Y.oF
  have tu : ∀ {T : Scheme.{0}} (z : T ⟶ Xo'.XF c'), (toUnit (Over.mk z)).left = z := fun z => by
    simpa using Over.w (toUnit (Over.mk z))
  let eq : Over.mk yq ⟶ Y.oF.t.G := toUnit _ ≫ Y.oF.etaA a
  have heq : eq ^ (p ^ n) = 1 := by
    rw [← MonObj.comp_pow, ← hA, GlobalTheory.ArcExt.etaA_pow_eq_one, MonObj.comp_one]
  obtain ⟨cq, hcq, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) eq σq heq hσqt
  obtain ⟨uq, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 cq

  let hKo : Over.mk y ⟶ Over.mk yq := Over.homMk (spMap ιK) hK
  have hN := (GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk yq)).2 (Over.mk y) hKo eq σq (unitOn uq) hcq
  have hKl : hKo.left = spMap ιK := rfl
  rw [hKl, GlobalTheory.Ex.Specialise.map_unitOn] at hN
  have t1 : (hKo ≫ eq) ^ (p ^ n) = 1 := by rw [← MonObj.comp_pow, heq, MonObj.comp_one]
  have t2 : (hKo ≫ σq) ^ (p ^ n) = 1 := by rw [← MonObj.comp_pow, hσqt, MonObj.comp_one]
  have hKe : (hKo ≫ eq).left = y ≫ (Y.oF.etaA a).left := by
    simp only [eq, Over.comp_left, tu, hKo, Over.homMk_left]
    rw [← Category.assoc, hK]
  have hKσ : (hKo ≫ σq).left ≫ Y.m.φ = spMap g ≫ wf.left := by
    rw [Over.comp_left, Category.assoc]
    change spMap ιK ≫ σq.left ≫ Y.m.cm.F = _
    rw [hσq]
    change spMap ιK ≫ spMap hf' ≫ wf.left = _
    rw [sp_sp, hgK]
  have hκK := hκ (hKo ≫ eq) (hKo ≫ σq) hKe t2
  rw [hKσ] at hκK
  have huK := (GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) (hKo ≫ eq) (hKo ≫ σq) t1 t2).unique hN hκK
  have huK' := GlobalTheory.Ex.Specialise.unitOn_bijective.1 huK
  set κK := κ (spMap g ≫ wf.left) with hκKdef
  have huq : uq = Units.map (algebraMap R Rq).toMonoidHom κK := by
    ext
    apply hιinj
    have := congrArg (fun u : (FractionRing R)ˣ => (u : FractionRing R)) huK'
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe] at this ⊢
    rw [this, ← RingHom.comp_apply, hιK]

  let hCo : Over.mk yy ⟶ Over.mk yq := Over.homMk (spMap ψq) hC
  have hN2 := (GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk yq)).2 (Over.mk yy) hCo eq σq (unitOn uq) hcq
  have hCl : hCo.left = spMap ψq := rfl
  rw [hCl, GlobalTheory.Ex.Specialise.map_unitOn] at hN2
  have hCe : hCo ≫ eq = e := by
    ext1
    simp only [eq, Over.comp_left, tu, hCo, Over.homMk_left]
    rw [← Category.assoc, hC, he]
  have hCσ : hCo ≫ σq = σ := by
    ext1
    refine Y.m.cart.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc]
      change spMap ψq ≫ σq.left ≫ Y.m.cm.F = σ.left ≫ Y.m.φ
      rw [hσq, hσ]
      change spMap ψq ≫ spMap hf' ≫ wf.left = _
      rw [sp_sp, hgC]
    · rw [Over.w (hCo ≫ σq), Over.w σ]
  refine ⟨?_, ?_⟩
  · rw [← hCσ, ← MonObj.comp_pow, hσqt, MonObj.comp_one]
  · rw [← hCe, ← hCσ]
    have hval : Units.map (ψq : Rq →* ℂ_[p]) uq = Units.map χ.toMonoidHom κK := by
      rw [huq]
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
      rw [← RingHom.comp_apply, hψq]
    have hN3 : Out.WeilIs P.A P.L ((p ^ n : ℕ) : ℤ) (hCo ≫ eq) (hCo ≫ σq) (unitOn (Units.map χ.toMonoidHom κK)) := by
      rw [← hval]; exact hN2
    exact hN3

end GlobalTheory.WeilSpec
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrally_closed_point_level_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ (a : Dw.La)
      (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ),
      (∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ))))) →
    ∀ (f : R) (wf : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ ξ) ⟶ Y.t.G), wf ^ (p ^ n) = 1 →
    ∀ (g : Localization.Away f →+* FractionRing R), g.comp (algebraMap R _) = algebraMap R (FractionRing R) →
    ∀ (x0 : R →+* 𝓞_ℂ_[p]) (φ : Localization.Away f →+* ℂ_[p]),
      φ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0 →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c'), spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap x0 ≫ ξ = yy ≫ Y.j →
    ∀ (e σ : Over.mk yy ⟶ Y.oF.t.G), e.left = yy ≫ (Y.oF.etaA a).left → σ.left ≫ Y.m.φ = spMap φ ≫ wf.left →
      σ ^ (p ^ n) = 1 ∧ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
        (unitOn (Units.map ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0).toMonoidHom (κ (spMap g ≫ wf.left)))) := by
  atlas_forward_decl GlobalTheory.WeilSpec.weil_spec
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.ModelPointWeil

theorem weil_eq_of_weilIs_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ → ∀ (a : Dw.La) (tt : P.T),
    (tt.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA a).left → ∀ (z : GlobalTheory.ChTor.Pts P.A.A) (e σ : Over.mk yy ⟶ Y.oF.t.G),
    e.left = yy ≫ (Y.oF.etaA a).left → σ.left = z.left ≫ ψ → σ ^ (p ^ n) = 1 → ∀ c : ℂ_[p]ˣ,
    Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ (unitOn c) → (c : ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ yb yy P π ψ hP a tt hlev z e σ he hσ hσp c hW
  obtain ⟨-, -, -, hpb, -, hL⟩ := hP
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨r, hr, ⟨cu⟩⟩ := GlobalTheory.PolAV_exists_cubical hLaws.cube P.A
  obtain ⟨w, hw⟩ := hL
  have hx : Tate.lev tt n ^ p ^ n = 1 := Tate.lev_pow tt n
  let T : Over (Sp ℂ_[p]) := Over.mk (𝟙 (Sp ℂ_[p]))
  have inj : ∀ {x y : T ⟶ P.A.A}, x.left ≫ ψ = y.left ≫ ψ → x = y := fun {x y} h =>
    Over.OverMorphism.ext (hpb.1.hom_ext h (by rw [Over.w, Over.w]))
  let U : Over.mk yy ⟶ Over.mk (T.hom ≫ yy) := Over.homMk (𝟙 _) (by simp [T])
  have hUz : U ≫ pushHom hpb T z = σ := Over.OverMorphism.ext (by
    show 𝟙 _ ≫ (z.left ≫ ψ) = σ.left
    rw [Category.id_comp, hσ])
  have hz : z ^ p ^ n = 1 := by
    apply inj
    have h1 : U ≫ pushHom hpb T (z ^ p ^ n) = U ≫ pushHom hpb T 1 := by
      rw [map_pow, map_one, MonObj.comp_pow, MonObj.comp_one, hUz, hσp]
    have h2 := congrArg (fun q => q.left) h1
    simpa using (show 𝟙 _ ≫ ((z ^ p ^ n).left ≫ ψ) = 𝟙 _ ≫ ((1 : T ⟶ P.A.A).left ≫ ψ) from h2)
  have hk : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have h := GlobalTheory.WeilCube.weilIs_pull cu hLaws.globalFns P.A.isAb Y.oF.t.PP.isLB hpb w hw
    (T := T) (T₀ := Over.mk yy) (𝟙 _) (by rw [Category.id_comp]; exact (Category.id_comp yy).symm) hx hz
    (x₀ := e) (y₀ := σ) (by simp [he, hlev]) (by simp [hσ]) hW
  have hu : ∀ u : Γ(Sp ℂ_[p], ⊤)ˣ, Units.map (Scheme.Hom.appTop (𝟙 (Sp ℂ_[p]))).hom.toMonoidHom u = u := by
    intro u; ext; simp
  erw [hu] at h
  exact_mod_cast (GlobalTheory.HTLat.weilIs_iff hk hx hz c).1 h

end GlobalTheory.ModelPointWeil
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_lattice_evaluation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ → ∀ (a : Dw.La) (tt : P.T),
    (tt.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA a).left → ∀ (z : GlobalTheory.ChTor.Pts P.A.A) (e σ : Over.mk yy ⟶ Y.oF.t.G),
    e.left = yy ≫ (Y.oF.etaA a).left → σ.left = z.left ≫ ψ → σ ^ (p ^ n) = 1 → ∀ c : ℂ_[p]ˣ,
    Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ (unitOn c) → (c : ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  atlas_forward_decl GlobalTheory.ModelPointWeil.weil_eq_of_weilIs_model
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_weil_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ a : Dw.La,
    ∃ κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ, GlobalTheory.HTMap.Mult Y.t ξ (p ^ n) κ ∧
      ∀ (P' : GlobalTheory.HTMap.FP Y.t ξ (p ^ n)) (b : P'.Bˣ), P'.Gl κ b → ∀ (x0 : R →+* 𝓞_ℂ_[p])
        (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
        PtOn Y (spMap x0 ≫ ξ) yy P π ψ → ∀ tt : P.T, (tt.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA a).left →
        ∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ Y.t.G.left), P'.At x0 w β →
        ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w →
          algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hstar hpW hA R _ _ _ ξ y hy a
  obtain ⟨κ, hκM, hκW⟩ := GlobalTheory.T.integrally_closed_generic_extension E H Dw l' Xo' c' W Y p n hA R ξ y hy a
  refine ⟨κ, hκM, ?_⟩
  intro P' b hb x0 yy P π ψ hPt tt hlev β w hAt z hz
  have hAt' := hAt.map (algebraMap 𝓞_ℂ_[p] ℂ_[p])
  obtain ⟨φ, hφ⟩ := GlobalTheory.HTMap.FP.ex_lift (P := P') hAt'.unit
  rw [← hφ] at hAt'
  obtain ⟨σ, hσ⟩ := hAt'.sect
  let wf : Over.mk (spMap (algebraMap R (Localization.Away P'.f)) ≫ ξ) ⟶ Y.t.G :=
    GlobalTheory.HTMap.mkPt (spMap σ.toRingHom ≫ P'.u.left) (P'.at_sect σ).over
  have hwf : wf ^ (p ^ n) = 1 := (P'.at_sect σ).tors (w := wf)
  have hgl := hb.1 _ _ (P'.at_sectK σ)
  have hsb : σ b = algebraMap R (Localization.Away P'.f) (κ (spMap (P'.toK.comp σ.toRingHom) ≫ P'.u.left)) := by
    apply P'.toK_inj
    rw [← RingHom.comp_apply P'.toK (algebraMap R _), P'.toK_comp]
    exact hgl
  let eyy : Over.mk yy ⟶ Y.oF.t.G := Over.homMk (yy ≫ (Y.oF.etaA a).left) (by
    rw [Category.assoc, Over.w (Y.oF.etaA a)]; exact Category.comp_id _)
  let σyy : Over.mk yy ⟶ Y.oF.t.G := Over.homMk (z.left ≫ ψ) (by
    rw [Category.assoc, hPt.2.2.2.1.1.w, ← Category.assoc, Over.w z]; simp)
  have hσyy : σyy.left ≫ Y.m.φ = spMap φ ≫ wf.left := by
    show (z.left ≫ ψ) ≫ Y.m.φ = spMap φ ≫ spMap σ.toRingHom ≫ P'.u.left
    rw [Category.assoc, hPt.2.2.2.2.1, hz, ← hAt'.2, hσ]
    exact (GlobalTheory.HTMap.spc_assoc _ _ _).symm
  obtain ⟨hσt, hW⟩ := GlobalTheory.T.integrally_closed_point_level_extends E H Dw l' Xo' c' W Y p n hpW hA R ξ y hy a κ hκW P'.f wf hwf P'.toK P'.toK_comp x0 φ hφ
    yy hPt.1 eyy σyy rfl hσyy
  have hc := GlobalTheory.T.p_adic_point_lattice_evaluation E H Dw l' Xo' c' W Y p n _ yy P π ψ hPt a tt hlev z eyy σyy rfl rfl hσt _ hW
  rw [← hc]
  have e1 : spMap P'.toK ≫ wf.left = spMap (P'.toK.comp σ.toRingHom) ≫ P'.u.left := GlobalTheory.HTMap.spc_assoc _ _ _
  rw [e1]
  show algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0) _
  rw [← hφ, RingHom.comp_apply, ← hsb]
  exact RingHom.congr_fun hσ _

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrally_closed_point_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ a : Dw.La,
    ∃ κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ, GlobalTheory.HTMap.Mult Y.t ξ (p ^ n) κ ∧
      ∀ (P' : GlobalTheory.HTMap.FP Y.t ξ (p ^ n)) (b : P'.Bˣ), P'.Gl κ b → ∀ (x0 : R →+* 𝓞_ℂ_[p])
        (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
        PtOn Y (spMap x0 ≫ ξ) yy P π ψ → ∀ tt : P.T, (tt.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA a).left →
        ∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ Y.t.G.left), P'.At x0 w β →
        ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w →
          algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  atlas_forward_decl GlobalTheory.FlatModel.exists_weil_character
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem charZero_of_pt {R : Type} [CommRing R] [IsDomain R] (F : IntermediateField ℚ ℂ)
    (f : Sp (FractionRing R) ⟶ Sp F) : CharZero R := by
  letI : Algebra F (FractionRing R) := (Spec.preimage f).hom.toAlgebra
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (algebraMap F (FractionRing R)).injective
  exact (algebraMap R (FractionRing R)).charZero_iff (IsFractionRing.injective R (FractionRing R)) |>.2 inferInstance

theorem htLocSt_of_hodgeTateKernel (hK : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint) : HTLocSt := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hstar hpW hA R _ _ _ ξ hgen g e he N a 𝔭 h𝔭
  have hp : p.Prime := Fact.out
  obtain ⟨y, hy⟩ := GlobalTheory.T.generic_point_lift_to_field E H Dw l' Xo' c' W Y p hp hpW R ξ hgen
  haveI : IsLocallyNoetherian Y.X := GlobalTheory.T.integral_model_locally_noetherian E H Dw l' Xo' c' W Y p hp hpW
  haveI : CharZero R := charZero_of_pt c'.F (y ≫ pullback.snd _ _)
  have hS : SplitTors Y.t ξ (p ^ n) :=
    GlobalTheory.T.splitTors_of_generic_level E H Dw l' Xo' c' _ _ Y R ξ y hy (p ^ n) (hA ▸ dvd_rfl)
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hF := GlobalTheory.HTMap.ex_full hq hS
  choose κ hκ hW using fun m => GlobalTheory.T.integrally_closed_point_extension E H Dw l' Xo' c' W Y p n hstar hpW hA R ξ y hy (a m)
  choose h' hh' using fun m => GlobalTheory.HTMap.ex_dlog hF (hκ m) he.1
  refine ⟨1, fun m k => algebraMap R _ (-(h' m k)), fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), ?_⟩
  intro φ yy P π ψ hPt m tt hlev k x hx
  let x0 : R →+* 𝓞_ℂ_[p] := φ.comp (algebraMap R _)
  obtain ⟨P', hP'⟩ := hF ((IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap x0) inferInstance
  obtain ⟨b, hb⟩ := P'.ex_gl (hκ m)
  obtain ⟨c, hc⟩ := GlobalTheory.HTMap.ex_char hP' hb
  have hd := hh' m 𝓞_ℂ_[p] x0 P' b hP' hb c hc
  have htan : ∀ i, IsTanAtG Y.t (spMap x0 ≫ ξ) (spMap (dualMap x0) ≫ e i) := (isTanBasis_bc he x0).1
  have hD : ∀ (k : Fin g) (β : P'.B →+* DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})),
      P'.At ((algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0)
        (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k) β →
      (β b).snd = Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (x0 (h' m k)) := by
    intro k β hβ
    let w := GlobalTheory.HTMap.mkPt (G := Y.t.G) _ (hβ.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
    have h2 := hd _ _ (GlobalTheory.HTMap.comb_single htan k) w rfl
    rw [hc _ w β hβ] at h2
    rw [h2]
    simp [Pi.single_apply]
  have key := GlobalTheory.T.tangent_basis_frame_map E H Dw l' Xo' c' W Y p n R ξ g e he P' (κ m) b hb x0 hP' yy P π ψ hPt
    (hK p ℂ_[p] Valued.v 𝓞_ℂ_[p] (𝓞 E) P).1 tt (hW m P' b hb x0 yy P π ψ hPt tt hlev) (fun k => x0 (h' m k)) hD
    k x hx
  have e1 : φ (algebraMap R _ (-(h' m k))) - (P.al₀ tt).1 x = -(x0 (h' m k) + (P.al₀ tt).1 x) := by
    simp only [x0, RingHom.comp_apply, map_neg]; ring
  rw [e1]
  exact neg_mem key

end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_local_of_kernel_at_point : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → HTLocSt := by
  atlas_forward_decl GlobalTheory.FlatModel.htLocSt_of_hodgeTateKernel
end
