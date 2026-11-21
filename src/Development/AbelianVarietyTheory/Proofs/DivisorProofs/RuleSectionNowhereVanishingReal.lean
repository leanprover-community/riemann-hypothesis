import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModel

section
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

set_option autoImplicit false

noncomputable section

open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntEigTransport

theorem isTan_iff_isTangent' {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

theorem transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (G : SAB H (Sp T.V)) (S : Scheme.{0}) (t : SAB H S) (x : Sp T.V ⟶ S) (n : SABMap G t x) (τ : E →+* ℂ) (k : ℕ) (ub : Fin k → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i, IsEigV c io G τ (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin k → T.V, IsComb ub a w) → ∃ v : Fin k → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt x ⟶ t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis t.act x (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (v i).left = (ub i).left ≫ n.φ := by
  intro E _ _ _ H l c T io φ hio G S t x n τ k ub htan heig hbas
  have hz : ∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) → z = φ (embK c τ a) := by
    intro a z hz
    apply IsFractionRing.injective T.V T.Fr
    rw [hz, ← hio]; rfl
  have hE : ∀ w : epsR T.V ⟶ G.G, IsEigV c io G τ w ↔
      ∀ a, (w ≫ G.act.act a).left = spMap (epsScaleR (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ a)) ≫ w.left := by
    intro w
    constructor
    · intro h a
      exact h a (φ (embK c τ a)) (by rw [← hio]; rfl)
    · intro h a z hz'
      rw [hz a z hz']
      exact h a
  have hC : ∀ (a : Fin k → T.V) (w : epsR T.V ⟶ G.G), IsComb ub a w ↔ IsLieComb a ub w := fun a w => Iff.rfl
  have hv : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsEigBasis G.act (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) ub := by
    refine ⟨fun i => ⟨(isTan_iff_isTangent' _).1 (htan i), (hE _).1 (heig i)⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => hC a w).1 (hbas w ((isTan_iff_isTangent' _).2 hw.1) ((hE w).2 hw.2))
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.FlatRow.exists_eigenBasis n hv
  exact ⟨u, hu, fun i => (hu' i).symm⟩

end GlobalTheory.IntEigTransport
end
end

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralEigenBasis_transport_pullback_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (G : SAB H (Sp T.V)) (S : Scheme.{0}) (t : SAB H S) (x : Sp T.V ⟶ S) (n : SABMap G t x) (τ : E →+* ℂ) (k : ℕ) (ub : Fin k → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i, IsEigV c io G τ (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin k → T.V, IsComb ub a w) → ∃ v : Fin k → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt x ⟶ t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis t.act x (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (v i).left = (ub i).left ≫ n.φ := by
  atlas_forward_decl GlobalTheory.IntEigTransport.transport
end

section
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace GlobalTheory.IntFrameLift

open ReciprocityTheory.ChartRestriction.G.Semi

theorem exists_eigenBasis_sameVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), Integral T io y → ∀ (χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y), χ ≫ pullback.snd _ _ = spMap φ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) → ∀ (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n), ∃ v : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt (χ ≫ pullback.fst _ _) ⟶ Y.t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis Y.t.act (χ ≫ pullback.fst _ _) (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (letI := io.toAlgebra; SameVec Y y (y.u τ (Fin.cast hn.symm i)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (v i).left)) := by
  intro E _ _ _ H Dw l Xo c Y T io φ hφ y hI χ hχ1 hχ2 τ n hn
  subst hn
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hu⟩, -⟩ := hI
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ ≫ pullback.fst _ _) Y.t
  have hx : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  let mK : SABMap t' Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast m1 hx.symm
  obtain ⟨a, mF, hF0, hFm⟩ := GlobalTheory.CuspFrom.exists_genIdent Y hχ2 mK m
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map T.V T.Fr G t t' m2 a
  obtain ⟨nC, hnC⟩ := sabComp pullCubComp E H _ _ _ Y.t t G (χ ≫ pullback.fst _ _) (𝟙 _) m ψ
  let n' : SABMap G Y.t (χ ≫ pullback.fst _ _) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast nC (Category.id_comp _)
  obtain ⟨v, hv, hvl⟩ := GlobalTheory.T.integralEigenBasis_transport_pullback_dvr E H l c T io φ hφ G Y.X Y.t (χ ≫ pullback.fst _ _) n' τ _ (ub τ) (htan τ)
    (heig τ) (hbas τ)
  refine ⟨v, hv, fun i => ?_⟩
  obtain ⟨u', hu1, hu2⟩ := hu τ i
  have hmono : Mono (spMap (algebraMap T.V T.Fr)) := by
    have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
    exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  have hbase : spMap (dualMap (algebraMap T.V T.Fr)) ≫ (epsOver T.V T.V).hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = _
    rw [GlobalTheory.ShFam.OpenReg.spMap_comp, GlobalTheory.ShFam.OpenReg.spMap_comp]
    congr 1
    ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hut : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply (cancel_mono (spMap (algebraMap T.V T.Fr))).1
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub τ i), hbase]
  have htan' : IsTanAtG t' (𝟙 _) u' := by
    have h1 := (GlobalTheory.ShFam.OpenReg.tan_iff m1 (Category.id_comp y.x) hut).1
    rw [hu1] at h1
    exact h1 (y.tan τ i)
  refine ⟨u' ≫ mF.φ, (GlobalTheory.ShFam.OpenReg.tan_iff mF (Category.id_comp _) hut).2 htan', ?_, ?_⟩
  · rw [Category.assoc, hF0, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hu1]
    rfl
  · rw [Category.assoc, hFm, ← hψ, hvl i, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hnC]
    simp only [← Category.assoc]
    rw [hu2]
    rfl

end GlobalTheory.IntFrameLift
end
end

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), Integral T io y → ∀ (χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y), χ ≫ pullback.snd _ _ = spMap φ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) → ∀ (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n), ∃ v : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt (χ ≫ pullback.fst _ _) ⟶ Y.t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis Y.t.act (χ ≫ pullback.fst _ _) (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (letI := io.toAlgebra; SameVec Y y (y.u τ (Fin.cast hn.symm i)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (v i).left)) := by
  atlas_forward_decl GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec
end

section
namespace GlobalTheory.LiftAndFactorization

open Formalism.L2.Pj

theorem exists_lift (T : CDVR) (x : T.Fr) (hx : x ≠ 0 → vV T.V x = 0) :
    ∃ b : T.V, algebraMap T.V T.Fr b = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have hne : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x ≠ 0 :=
    (Valuation.ne_zero_iff _).2 h0
  have hlog : WithZero.log ((IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x) = 0 := by
    have := hx h0
    unfold vV valV at this
    exact neg_eq_zero.1 this
  have := WithZero.exp_log hne
  rw [hlog, WithZero.exp_zero] at this
  exact this.ge

theorem exists_factor (T : CDVR) {F : Type} [Field F] (io : F →+* T.Fr)
    (h : ∀ a : F, a ≠ 0 → vV T.V (io a) = 0) :
    ∃ φ : F →+* T.V, (algebraMap T.V T.Fr).comp φ = io := by
  have key : ∀ a : F, ∃ b : T.V, algebraMap T.V T.Fr b = io a := fun a =>
    exists_lift T (io a) (fun ha => h a (fun h0 => ha (by rw [h0, map_zero])))
  choose f hf using key
  have inj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => inj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => inj (by rw [map_add, hf, hf, hf, map_add]) }, ?_⟩
  ext a
  exact hf a

end GlobalTheory.LiftAndFactorization
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.BdryUnitVal

theorem pt_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), (letI := io.toAlgebra; ∀ s, GlobalTheory.AllWt.ptF y s ∈ (V : Set (Xo.XF c))) → ∃ χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y, χ ≫ pullback.snd _ _ = spMap φ ∧ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) ∧ Set.range χ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.compactification Y V := by
  intro E _ _ _ H Dw l Xo c Y V T io φ hφ y hy
  letI := io.toAlgebra
  obtain ⟨χ, h1, h2⟩ := GlobalTheory.CuspFrom.exists_genPt (K := T.Fr) Y φ hφ y
  refine ⟨χ, h1, h2, ?_⟩
  rintro _ ⟨p, rfl⟩
  let η : Sp T.Fr := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)
  have hη : χ (spMap (algebraMap T.V T.Fr) η) ∈ Y.jQ '' (V : Set (Xo.XF c)) := by
    rw [← Scheme.Hom.comp_apply, ← h2, Scheme.Hom.comp_apply]
    exact ⟨_, hy η, rfl⟩
  have hp : p ∈ closure {spMap (algebraMap T.V T.Fr) η} := by
    apply (PrimeSpectrum.le_iff_mem_closure _ _).1
    show Ideal.comap (algebraMap T.V T.Fr) (⊥ : Ideal T.Fr) ≤ (p : PrimeSpectrum T.V).asIdeal
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective T.V T.Fr)]
    exact bot_le
  exact map_mem_closure χ.continuous hp (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hη)

end GlobalTheory.BdryUnitVal

namespace GlobalTheory.BdryUnitVal

theorem vV_unit (T : CDVR) (u : T.V) (hu : IsUnit u) : vV T.V (algebraMap T.V T.Fr u) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    refine le_antisymm (HeightOneSpectrum.intValuation_le_one _ _) (not_lt.1 fun h => ?_)
    exact (IsDiscreteValuationRing.maximalIdeal T.V).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).1 h) hu)
  rw [vV, h1, WithZero.log_one, neg_zero]

theorem nval_unit (T : CDVR) (u : T.V) (hu : IsUnit u) : nval T.V 1 (algebraMap T.V T.Fr u) = 0 := by
  have hne : algebraMap T.V T.Fr u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hu.ne_zero
  rw [nval_of_ne hne, vV_unit T u hu]
  simp

theorem exists_factor (T : CDVR) {F : Type} [Field F] (io : F →+* T.Fr) (hio : ∀ a, a ≠ 0 → vV T.V (io a) = 0) :
    ∃ φ : F →+* T.V, (algebraMap T.V T.Fr).comp φ = io := by
  first
  | exact @_root_.GlobalTheory.LiftAndFactorization.exists_factor
  | exact _root_.GlobalTheory.LiftAndFactorization.exists_factor
  | (apply _root_.GlobalTheory.LiftAndFactorization.exists_factor <;> assumption)
  | (intros; apply _root_.GlobalTheory.LiftAndFactorization.exists_factor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LiftAndFactorization.exists_factor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LiftAndFactorization.exists_factor ..)

end GlobalTheory.BdryUnitVal

namespace GlobalTheory.BdryUnitVal

theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (τ : Psi H) :
    conjEmb τ.1 (H.rt : E) ≠ H.rt0 := fun h3 => by
  have h3' : starRingEnd ℂ (τ.1 (H.rt : E)) = H.rt0 := h3
  rw [τ.2] at h3'
  have h4 := H.sqrt_neg_disc_sq
  have h5 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h3'
  have h6 := congrArg Complex.re h4
  have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  simp [pow_two, h5] at h6
  nlinarith [mul_self_nonneg H.rt0.re]

theorem unit_at_integral : GlobalTheory.CovTop.Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → Reads Y V τ sig f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ f) = 0 := by
  intro _ E _ _ _ H Dw l Xo c Y Z V τ sig f hVZ hsig hvn hrd T io y₀ hio hlies
  letI := io.toAlgebra
  obtain ⟨φ, hφ⟩ := exists_factor T io hio
  have hy : ∀ s, GlobalTheory.AllWt.ptF y₀.1 s ∈ (V : Set (Xo.XF c)) := fun s => hVZ ▸ hlies s
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := pt_ext E H Dw l Xo c Y V T io φ hφ y₀.1 hy
  have hp : Dw.mult τ.1 = Dw.p := by rw [Datum.mult, if_pos τ.2]
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := by rw [Datum.mult, if_neg (conj_ne τ)]
  obtain ⟨v, hv, hsv⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 τ.1 Dw.p hp
  obtain ⟨w, hw, hsw⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 (conjEmb τ.1) Dw.q hq
  let aT : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.V φ := ⟨χ, hχ1, hχ3, v, w, hv, hw⟩
  have hx : (spMap (algebraMap T.V T.Fr) ≫ χ) ≫ pullback.fst _ _ =
      spMap (algebraMap T.V T.Fr) ≫ (χ ≫ pullback.fst _ _) := Category.assoc _ _ _
  obtain ⟨v', hv', ev⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hv
  obtain ⟨w', hw', ew⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hw
  rw [hφ] at hv' hw'
  let aK : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.Fr io :=
    ⟨spMap (algebraMap T.V T.Fr) ≫ χ, by rw [Category.assoc, hχ1, ← GlobalTheory.DetExtendZero.spMap_comp, hφ], by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hχ3 ⟨_, rfl⟩, v', w', hv', hw'⟩
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsChange aT aK (algebraMap T.V T.Fr) 1 1 := by
    refine ⟨hφ, rfl, fun i => ?_, fun i => ?_⟩
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.v_basis.1 k).1) i
      convert this using 2 with k
      exact (ev k).symm
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.w_basis.1 k).1) i
      convert this using 2 with k
      exact (ew k).symm
  have e := hsig T.V T.Fr φ io aT aK (algebraMap T.V T.Fr) 1 1 hc
  simp only [Matrix.det_one, mul_one] at e
  have hm : Matches Y V τ y₀.1 aK :=
    ⟨hχ2.symm, fun i => ⟨Fin.cast hp.symm i, rfl, by
      change SameVec Y y₀.1 _ (v' i).left
      rw [ev]; exact hsv i⟩, fun i => ⟨Fin.cast hq.symm i, rfl, by
      change SameVec Y y₀.1 _ (w' i).left
      rw [ew]; exact hsw i⟩⟩
  have hr := hrd T.Fr y₀.1 y₀.2.1 aK hm
  change nval T.V 1 (evR Xo c f y₀.1) = 0
  rw [hr]
  change nval T.V 1 (sig T.Fr io aK) = 0
  rw [e]
  exact nval_unit T _ (hvn T.V φ aT)

end GlobalTheory.BdryUnitVal
end
end
