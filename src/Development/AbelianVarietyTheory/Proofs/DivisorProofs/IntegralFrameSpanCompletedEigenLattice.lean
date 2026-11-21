import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.HnStepEqOfNorm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCdvrCompletionIntegralIff

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open Limits MonObj

noncomputable section
namespace GlobalTheory.EigLatSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem lieComb_of_combAt {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S]
    {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x) {k : ℕ} (q : Fin k → (epsR S ⟶ t.G))
    (a : Fin k → S) (z : epsR S ⟶ t.G) (h : IsCombAt x (fun j => (q j).left ≫ m.φ) a (z.left ≫ m.φ)) :
    IsLieComb a q z := by
  obtain ⟨U, hU, hprod⟩ := h
  let Q : Fin k → (epsR S ⟶ t.G) := fun j => Over.homMk (spMap (epsMul (a j)) ≫ (q j).left) (by
    show (spMap (epsMul (a j)) ≫ (q j).left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S))
    rw [Category.assoc, Over.w (q j)]
    exact (GlobalTheory.IntLie.spMap_comp₂ _ _).trans (congrArg spMap (GlobalTheory.IntLie.epsMul_alg (a j))))
  refine ⟨Q, fun j => rfl, ?_⟩
  have hP := GlobalTheory.IntLie.prod_push m.cart (epsR S) (tEps x) (𝟙 _) (Category.id_comp _) Q U (fun j => by
    rw [Category.id_comp, hU j]; exact Category.assoc _ _ _)
  apply Over.OverMorphism.ext
  apply m.cart.1.hom_ext
  · rw [hP, Category.id_comp, hprod]
  · rw [Over.w z, Over.w ((List.ofFn Q).prod)]

end GlobalTheory.EigLatSpan

noncomputable section
namespace GlobalTheory.EigLatSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem baseChange_basis {K : Type} [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K))
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) {L : Type} [Field L] (iK : K →+* L)
    (t' : SAB H (Sp L)) (n' : SABMap t' t₀ (spMap iK)) :
    ∃ e : Fin F.P₀.g → (epsR L ⟶ t'.G), IsLieBasis e ∧
      ∀ (d : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (z : epsR L ⟶ t'.G), IsLieComb d F.v w →
        z.left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ → IsLieComb (fun k => iK (d k)) e z := by
  haveI : IsCommMonObj F.P₀.A := F.P₀.isAb.comm
  haveI := F.P₀.smoothDim
  have hs : Smooth F.P₀.A.hom := SmoothOfRelativeDimension.smooth F.P₀.g _
  have hF := F.fib.2.1
  have hc : (n'.φ ≫ m2.φ) ≫ B.pol.A.hom = (t'.G.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [Category.assoc, m2.cart.1.w, ← Category.assoc, n'.cart.1.w, Category.assoc]
  let ψ : t'.G.left ⟶ F.P₀.A.left := hF.1.lift (n'.φ ≫ m2.φ) (t'.G.hom ≫ spMap iK) hc
  have hψ1 : ψ ≫ F.φ = n'.φ ≫ m2.φ := hF.1.lift_fst _ _ _
  have hψ2 : ψ ≫ F.P₀.A.hom = t'.G.hom ≫ spMap iK := hF.1.lift_snd _ _ _
  have hout : IsPullback (ψ ≫ F.φ) t'.G.hom B.pol.A.hom (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) := by
    rw [hψ1]
    exact IsPullback.paste_horiz n'.cart.1 m2.cart.1
  have hpull : IsGrpPullback t'.G F.P₀.A (spMap iK) ψ := by
    refine ⟨IsPullback.of_right hout hψ2 hF.1, ?_⟩
    intro T x y x₀ y₀ hx hy
    let T₁ : Over (Sp K) := Over.mk (T.hom ≫ spMap iK)
    let x' : T₁ ⟶ t₀.G := Over.homMk (x.left ≫ n'.φ) (by
      show (x.left ≫ n'.φ) ≫ t₀.G.hom = T.hom ≫ spMap iK
      rw [Category.assoc, n'.cart.1.w, ← Category.assoc, Over.w x])
    let y' : T₁ ⟶ t₀.G := Over.homMk (y.left ≫ n'.φ) (by
      show (y.left ≫ n'.φ) ≫ t₀.G.hom = T.hom ≫ spMap iK
      rw [Category.assoc, n'.cart.1.w, ← Category.assoc, Over.w y])
    let x'' : Over.mk (T₁.hom ≫ spMap (algebraMap (𝓞 K) K)) ⟶ B.t.G := Over.homMk (x.left ≫ n'.φ ≫ m2.φ) (by
      show (x.left ≫ n'.φ ≫ m2.φ) ≫ B.t.G.hom = (T.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K)
      rw [Category.assoc, Category.assoc, m2.cart.1.w, ← Category.assoc n'.φ, n'.cart.1.w, ← Category.assoc,
        ← Category.assoc, Over.w x, Category.assoc])
    let y'' : Over.mk (T₁.hom ≫ spMap (algebraMap (𝓞 K) K)) ⟶ B.t.G := Over.homMk (y.left ≫ n'.φ ≫ m2.φ) (by
      show (y.left ≫ n'.φ ≫ m2.φ) ≫ B.t.G.hom = (T.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K)
      rw [Category.assoc, Category.assoc, m2.cart.1.w, ← Category.assoc n'.φ, n'.cart.1.w, ← Category.assoc,
        ← Category.assoc, Over.w y, Category.assoc])
    have k1 : (x' * y').left = (x * y).left ≫ n'.φ := n'.cart.2 T x y x' y' rfl rfl
    have k2 : (x'' * y'').left = (x' * y').left ≫ m2.φ := m2.cart.2 T₁ x' y' x'' y'' rfl rfl
    have k3 : (x'' * y'').left = (x₀ * y₀).left ≫ F.φ := hF.2 T₁ x₀ y₀ x'' y''
      (by show x.left ≫ n'.φ ≫ m2.φ = x₀.left ≫ F.φ; rw [hx, Category.assoc, hψ1])
      (by show y.left ≫ n'.φ ≫ m2.φ = y₀.left ≫ F.φ; rw [hy, Category.assoc, hψ1])
    apply hF.1.hom_ext
    · rw [← k3, k2, k1, Category.assoc, Category.assoc, hψ1]
    · rw [Over.w (x₀ * y₀), Category.assoc, hψ2, ← Category.assoc, Over.w (x * y)]
      rfl
  obtain ⟨e, he, hev⟩ := GlobalTheory.exists_isLieBasis_baseChange K L iK F.P₀.A t'.G ψ hpull hs F.P₀.g F.v F.basis
  refine ⟨e, he, fun d w z hw hz => ?_⟩
  obtain ⟨U, hU, rfl⟩ := hw
  have hg : spMap (Formalism.L2.Pj.dualMap iK) ≫ (epsR K).hom = (epsR L).hom ≫ spMap iK := by
    show spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (algebraMap K (DualNumber K)) =
      spMap (algebraMap L (DualNumber L)) ≫ spMap iK
    rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_alg]
  let Z : Fin F.P₀.g → (epsR L ⟶ t'.G) := fun j => Over.homMk (spMap (epsMul (iK (d j))) ≫ (e j).left) (by
    show (spMap (epsMul (iK (d j))) ≫ (e j).left) ≫ t'.G.hom = spMap (algebraMap L (DualNumber L))
    rw [Category.assoc, Over.w (e j)]
    exact (GlobalTheory.IntLie.spMap_comp₂ _ _).trans (congrArg spMap (GlobalTheory.IntLie.epsMul_alg _)))
  refine ⟨Z, fun j => rfl, ?_⟩
  have hP := GlobalTheory.IntLie.prod_push hpull (epsR L) (epsR K) (spMap (Formalism.L2.Pj.dualMap iK)) hg Z U (fun j => by
    show (spMap (epsMul (iK (d j))) ≫ (e j).left) ≫ ψ = _
    rw [hU j, Category.assoc, hev j, ← Category.assoc, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂,
      GlobalTheory.IntLie.spMap_comp₂]
    congr 2
    exact (GlobalTheory.IntLie.dualMap_epsMul iK (d j)).symm)
  apply Over.OverMorphism.ext
  apply hpull.1.hom_ext
  · rw [hP]
    apply hF.1.hom_ext
    · rw [Category.assoc, hψ1, hz, Category.assoc]
    · simp only [Category.assoc]
      rw [hψ2, Over.w ((List.ofFn U).prod), ← Category.assoc, Over.w z]
      exact hg.symm
  · rw [Over.w z, Over.w ((List.ofFn Z).prod)]

theorem isTan_isEigV {l : Level H} (c : Coeff l) {K : Type} [Field K] [NumberField K] [Algebra c.F K]
    (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V)
    (hρV : (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K)) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K)
    (htt : ∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) (G : SAB H (Sp T.V)) (n : SABMap G B.t (spMap ρV))
    (u₀ : epsR (𝓞 K) ⟶ B.t.G) (hu : IsTangent u₀) (he : ∀ a, IsLieComb ![tt a] ![u₀] (u₀ ≫ B.t.act.act a))
    (W : epsOver T.V T.V ⟶ G.G) (hW : W.left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap ρV) ≫ u₀.left) :
    IsTan W ∧ IsEigV c (iK.comp (algebraMap c.F K)) G ρ W := by
  have hB1 : (1 : ptOver (𝓞 K) (𝓞 K) ⟶ B.t.G).left = η[B.t.G].left := by
    have e : (1 : ptOver (𝓞 K) (𝓞 K) ⟶ B.t.G) = CartesianMonoidalCategory.toUnit _ ≫ η[B.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (CartesianMonoidalCategory.toUnit (ptOver (𝓞 K) (𝓞 K))).left = 𝟙 (Sp (𝓞 K)) := by
      have := Over.w (CartesianMonoidalCategory.toUnit (ptOver (𝓞 K) (𝓞 K)))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  have hpt : ∀ (R : Type) [CommRing R], spMap (algebraMap R R) = 𝟙 (Sp R) := fun R _ => by
    rw [Algebra.algebraMap_self]; exact Spec.map_id _
  constructor
  · unfold IsTan
    apply n.cart.1.hom_ext
    · rw [Category.assoc, hW, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂]
      rw [GlobalTheory.IntLie.one_push n.cart (ptOver T.V T.V) (ptOver (𝓞 K) (𝓞 K)) (spMap ρV)
        (by simp only [Over.mk_hom, hpt]; exact (Category.comp_id _).trans (Category.id_comp _).symm), hB1, ← hu, ← Category.assoc,
        GlobalTheory.IntLie.spMap_comp₂]
      congr 2
      apply RingHom.ext
      intro r
      simp [Formalism.L2.Pj.dualMap]
    · rw [Category.assoc, Over.w W, Over.w (1 : ptOver T.V T.V ⟶ G.G)]
      show spMap (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom ≫
        spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = spMap (algebraMap T.V T.V)
      rw [GlobalTheory.IntLie.spMap_comp₂]
      congr 1
  · intro a z hz
    have hzρ : z = ρV (tt a) := by
      apply IsFractionRing.injective T.V T.Fr
      rw [hz]
      have := congrArg (fun f => f (tt a)) hρV
      simp only [RingHom.comp_apply] at this
      rw [this]
      show iK (algebraMap c.F K (embK c ρ a)) = iK (algebraMap (𝓞 K) K (tt a))
      rw [← htt]
    subst hzρ
    obtain ⟨U, hU, hprod⟩ := he a
    have hU0 : (u₀ ≫ B.t.act.act a).left = spMap (epsMul (tt a)) ≫ u₀.left := by
      rw [hprod]
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]
      exact hU 0
    apply n.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, hW, Category.assoc, ← Over.comp_left, hU0,
        Category.assoc (spMap (epsMul (ρV (tt a)))) W.left n.φ, hW, ← Category.assoc, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂,
        GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_epsMul]
    · rw [Over.comp_left, Category.assoc, Over.w (G.act.act a), Category.assoc, Over.w W]
      show spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
        spMap (epsMul (ρV (tt a))) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V))
      rw [GlobalTheory.IntLie.spMap_comp₂, ← RingHom.comp_assoc, GlobalTheory.IntLie.epsMul_alg]

end GlobalTheory.EigLatSpan

noncomputable section
namespace GlobalTheory.EigLatSpan

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (Formalism.L2.Pj.dualMap g).comp (Formalism.L2.Pj.dualMap f) = Formalism.L2.Pj.dualMap (g.comp f) := by
  apply RingHom.ext
  intro r
  ext <;> simp [Formalism.L2.Pj.dualMap]

theorem eigLat_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hval ρV hρV
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hmap G t' n n' m1' m2' h1 h2 C a y' hchg hint
  obtain ⟨e, he, htr⟩ := baseChange_basis B t₀ m2 F iK t' n'
  have hA := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ e he.1
  obtain ⟨ub, -, -, hubu, hl⟩ := hint
  choose u' hu1 hu2 using hl ρ
  have hδ : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫
      spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
    rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
    show spMap ((Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
    rw [GlobalTheory.IntLie.dualMap_alg]
  have hov : ∀ (z : epsOver T.V T.V ⟶ G.t.G) (z' : Sp (DualNumber T.Fr) ⟶ t'.G.left),
      z' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ z.left →
      z' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    intro z z' hz
    apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
    rw [Category.assoc, ← m2'.cart.1.w, ← Category.assoc, hz, Category.assoc, Over.w z]
    exact hδ

  let r : Fin (Dw.mult ρ) → (epsR T.Fr ⟶ t'.G) := fun i => Over.homMk (u' i) (hov _ _ (hu2 i))

  let q : Fin (Dw.mult ρ) → (epsR T.Fr ⟶ t'.G) := fun j =>
    Over.homMk (m1'.cart.1.lift (yT.u ρ j) (spMap (algebraMap T.Fr (DualNumber T.Fr))) (yT.tan ρ j).1)
      (m1'.cart.1.lift_snd _ _ _)
  have hq1 : ∀ j, (q j).left ≫ m1'.φ = yT.u ρ j := fun j => m1'.cart.1.lift_fst _ _ _
  have hrq : ∀ i, IsLieComb (C ρ i) q (r i) := by
    intro i
    apply lieComb_of_combAt m1'
    have e1 : (fun j => (q j).left ≫ m1'.φ) = yT.u ρ := funext hq1
    rw [e1]
    show IsCombAt yT.x (yT.u ρ) (C ρ i) (u' i ≫ m1'.φ)
    rw [hu1]
    exact hchg.2.1 ρ i

  choose uu ww hA1 hA2 hA3 using hu
  have huu : ∀ j, uu j ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
    intro j
    apply GlobalTheory.IntLie.spMap_frac_cancel (V := 𝓞 K)
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hA2 j, Category.assoc, F.fib.2.1.1.w, ← Category.assoc,
      Over.w (ww j)]
    rfl
  have hq : ∀ j, IsLieComb (fun k => iK (u j k)) e (q j) := by
    intro j
    refine htr (u j) (ww j) (q j) (hA3 j) ?_
    have e2 : (q j).left ≫ n'.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ uu j := by
      apply m1.cart.1.hom_ext
      · rw [Category.assoc, ← h1, hq1, hmap.2.1 ρ j, Category.assoc, hA1 j]
      · rw [Category.assoc, n'.cart.1.w, ← Category.assoc, Over.w (q j), Category.assoc, huu j]
        show spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK = _
        rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_alg]
    rw [← Category.assoc, e2, Category.assoc, hA2 j]
  have hr : ∀ i, IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) e (r i) :=
    fun i => hA.2.2.1 _ _ q (C ρ i) (r i) hq (hrq i)
  have key : ∀ cc : Fin F.P₀.g → K, (∃ u₀, F.IsCoord u₀ cc ∧ ∀ a, IsLieComb ![tt a] ![u₀] (u₀ ≫ B.t.act.act a)) →
      (fun k => iK (cc k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
    rintro cc ⟨u₀, ⟨htan, w, hwv, hwc⟩, heig⟩
    have hcond : (spMap (Formalism.L2.Pj.dualMap ρV) ≫ u₀.left) ≫ B.t.G.hom =
        (epsOver T.V T.V).hom ≫ spMap ρV := by
      rw [Category.assoc, Over.w u₀]
      show spMap (Formalism.L2.Pj.dualMap ρV) ≫ spMap (algebraMap (𝓞 K) (DualNumber (𝓞 K))) =
        spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) ≫ spMap ρV
      rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_alg, Algebra.algebraMap_self,
        RingHom.comp_id]
    let W' : epsOver T.V T.V ⟶ G.t.G := Over.homMk (n.cart.1.lift _ _ hcond) (n.cart.1.lift_snd _ _ _)
    have hW' : W'.left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap ρV) ≫ u₀.left := n.cart.1.lift_fst _ _ _
    obtain ⟨hW't, hW'e⟩ := isTan_isEigV c B T iK ρV hρV ρ tt htt G.t n u₀ htan heig W' hW'
    obtain ⟨aV, haV, -⟩ := hubu ρ W' hW't hW'e
    have hcs : (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ W'.left) ≫ G.t.G.hom =
        spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
      rw [Category.assoc, Over.w W']
      exact hδ
    let s' : epsR T.Fr ⟶ t'.G := Over.homMk (m2'.cart.1.lift _ _ hcs) (m2'.cart.1.lift_snd _ _ _)
    have hs2 : s'.left ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ W'.left :=
      m2'.cart.1.lift_fst _ _ _
    have hgen := GlobalTheory.IntLie.comb_generic m1' m2' (ub ρ) u' hu2 W' s'.left hs2 aV haV
    have hsr : IsLieComb (fun j => algebraMap T.V T.Fr (aV j)) r s' := lieComb_of_combAt m1' r _ s' hgen
    have hs := hA.2.2.1 _ _ r _ s' hr hsr
    have hc : IsLieComb (fun k => iK (cc k)) e s' := by
      refine htr cc w s' hwc ?_
      have ed : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (Formalism.L2.Pj.dualMap ρV) =
          spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap (𝓞 K) K)) := by
        rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, dualMap_comp', hρV]
        exact congrArg spMap (dualMap_comp' _ _).symm
      rw [hwv, ← h2, ← Category.assoc, hs2, Category.assoc, hW', ← Category.assoc, ed, Category.assoc]
    have heq := (he.2 s' (hA.2.1 _ _ hc)).unique hc hs
    rw [heq]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero =>
    convert Submodule.zero_mem (Submodule.span T.V _) using 1
    ext k
    simp
  | add x z _ _ hx hz =>
    have : (fun k => iK ((x + z) k)) = (fun k => iK (x k)) + fun k => iK (z k) := by
      ext k; simp
    rw [this]
    exact Submodule.add_mem _ hx hz
  | smul s x _ hx =>
    have : (fun k => iK ((s • x) k)) = ρV s • fun k => iK (x k) := by
      ext k
      have := congrArg (fun f => f s) hρV
      simp only [RingHom.comp_apply] at this
      simp [Algebra.smul_def, this]
    rw [this]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory.EigLatSpan
end
end
end
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_eigenLattice_le_span_integral_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  atlas_forward_decl GlobalTheory.EigLatSpan.eigLat_le_span
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.EigenSpanSat

def eigenSub {K : Type} [Field K] {n : ℕ} {O : Type} (r : O → Matrix (Fin n) (Fin n) K)
    (τ : O → K) : Submodule K (Fin n → K) where
  carrier := {c | ∀ a, (r a).mulVec c = τ a • c}
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [Matrix.mulVec_add, hx a, hy a, smul_add]
  zero_mem' := by
    intro a
    simp
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Matrix.mulVec_smul, hx a, smul_comm]

theorem map_mulVec {K L : Type} [Field K] [Field L] (iK : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    (M.map iK).mulVec (fun i => iK (c i)) = fun i => iK (M.mulVec c i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem eq_zero_of_eigen {K L : Type} [Field K] [Field L] (iK : K →+* L) {n : ℕ} {O : Type}
    (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) {m : ℕ} (σ : Fin m → L)
    (c : Fin m → (Fin n → K))
    (hP : ∀ d : Fin m → K, (∀ a, (r a).mulVec (∑ i, d i • c i) = τ a • ∑ i, d i • c i) →
      ∑ i, d i • c i = 0)
    (he : ∀ a, ((r a).map iK).mulVec (∑ i, σ i • fun t => iK (c i t)) =
      iK (τ a) • ∑ i, σ i • fun t => iK (c i t)) :
    ∑ i, σ i • (fun t => iK (c i t)) = 0 := by
  let _ : Algebra K L := iK.toAlgebra
  let S := Submodule.span K (Set.range σ)
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range σ)
  let b := Module.finBasis K S
  have hli : LinearIndependent K (fun k => (b k : L)) :=
    b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let D : Fin (finrank K S) → Fin m → K :=
    fun k i => b.repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩ k
  have hσ : ∀ i, σ i = ∑ k, iK (D k i) * (b k : L) := by
    intro i
    have h := congrArg Subtype.val (b.sum_repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩)
    refine h.symm.trans ?_
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Algebra.smul_def]
    rfl

  have hvan : ∀ v : Fin (finrank K S) → (Fin n → K),
      (∑ k, (b k : L) • fun t => iK (v k t)) = 0 → ∀ k, v k = 0 := by
    intro v hv k
    funext t
    have h := congrFun hv t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have := Fintype.linearIndependent_iff.1 hli (fun k => v k t) (by
      rw [← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, mul_comm]
      rfl)
    exact this k
  let u : Fin (finrank K S) → (Fin n → K) := fun k => ∑ i, D k i • c i
  have hy : (∑ i, σ i • (fun t => iK (c i t))) = ∑ k, (b k : L) • fun t => iK (u k t) := by
    funext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u, map_sum, map_mul, hσ,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hu : ∀ k, u k = 0 := by
    intro k
    apply hP
    intro a
    have h1 := hvan (fun k => (r a).mulVec (u k) - τ a • u k) (by
      have h2 := he a
      rw [hy, Matrix.mulVec_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_smul, map_mulVec, smul_comm (iK (τ a)), ← smul_sub]
      congr 1
      funext t
      simp [map_sub, map_mul])
    exact sub_eq_zero.1 (h1 k)
  rw [hy]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hu k]
  funext t
  simp

end GlobalTheory.EigenSpanSat

namespace GlobalTheory.EigenSpanSat

theorem span_eigen_sat : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (O : Type) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : Formalism.L2.Pj.CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → Λ.FG → ∀ x : Fin n → T.Fr, x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' (Λ : Set (Fin n → K))) → (∀ a, ((r a).map iK).mulVec x = iK (τ a) • x) → x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) := by
  intro K _ _ n Λ O r τ 𝔓 T iK _ hFG x hx he
  obtain ⟨C, -, hdec, hCW⟩ :=
    Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd.exists_compl_inf Λ hFG (eigenSub r τ)
  obtain ⟨m, s, g, hg⟩ := Submodule.mem_span_set'.1 hx
  choose l hl hlg using fun i => (g i).2
  choose p hp q hq hpq using fun i => hdec (l i) (hl i)
  let σ : Fin m → T.Fr := fun i => algebraMap T.V T.Fr (s i)
  have hsplit : x = ∑ i, σ i • (fun t => iK (p i t)) + ∑ i, σ i • (fun t => iK (q i t)) := by
    rw [← hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hlg i, hpq i, ← smul_add, algebraMap_smul]
    congr 1
    funext t
    simp
  have hpE : ∀ i a, (r a).mulVec (p i) = τ a • p i := fun i => (hp i).2
  have hx1 : ∀ a, ((r a).map iK).mulVec (∑ i, σ i • fun t => iK (p i t)) =
      iK (τ a) • ∑ i, σ i • fun t => iK (p i t) := by
    intro a
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, map_mulVec, hpE i a, smul_comm]
    congr 1
    funext t
    simp
  have hx2 : ∑ i, σ i • (fun t => iK (q i t)) = 0 := by
    refine eq_zero_of_eigen iK r τ σ q (fun d hd => ?_) (fun a => ?_)
    · refine hCW _ (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (hq i))) hd
    · have h := he a
      rw [hsplit, Matrix.mulVec_add, hx1 a, smul_add] at h
      exact add_left_cancel h
  rw [hsplit, hx2, add_zero]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p i, ⟨(hp i).1, (hp i).2⟩, rfl⟩)

end GlobalTheory.EigenSpanSat
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_span_eigen_vector_mem_eigen_sublattice : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (O : Type) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : Formalism.L2.Pj.CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → Λ.FG → ∀ x : Fin n → T.Fr, x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' (Λ : Set (Fin n → K))) → (∀ a, ((r a).map iK).mulVec x = iK (τ a) • x) → x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) := by
  atlas_forward_decl GlobalTheory.EigenSpanSat.span_eigen_sat
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.PtDeg.FrameEig

theorem dualMapR_epsScaleR {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) :
    spMap (Chart.dualMapR f) ≫ spMap (epsScaleR a) = spMap (epsMul (f a)) ≫ spMap (Chart.dualMapR f) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, Chart.dualMapR, mul_comm]

theorem epsScaleR_epsMul_comm {R : Type} [CommRing R] (a b : R) :
    spMap (epsScaleR a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsScaleR a) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, mul_left_comm]

theorem scale_eig {R : Type} [CommRing R] {X : Scheme.{0}} (a b : R) (x : Sp (DualNumber R) ⟶ X) (g : X ⟶ X)
    (h : x ≫ g = spMap (epsMul b) ≫ x) :
    (spMap (epsScaleR a) ≫ x) ≫ g = spMap (epsMul b) ≫ spMap (epsScaleR a) ≫ x := by
  rw [Category.assoc, h, ← Category.assoc, epsScaleR_epsMul_comm, Category.assoc]

theorem epsScaleR_eq_epsMul {R : Type} [CommRing R] (a : R) : epsScaleR a = epsMul a := rfl

theorem sc_left {R : Type} [CommRing R] {G : Over (Sp R)} (a : R) (v : epsR R ⟶ G) :
    (GlobalTheory.CM.IntCoord.sc a ≫ v).left = spMap (epsScaleR a) ≫ v.left := rfl

end GlobalTheory.PtDeg.FrameEig

open GlobalTheory.PtDeg.FrameEig in

theorem GlobalTheory.PtDeg.frameCoord_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ j, u j ∈ Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu j
  obtain ⟨u₀, w, h₁, h₂, hc⟩ := hu j
  have h₂' : u₀ ≫ m2.cm.F = w.left ≫ F.φ := h₂
  have h₁' : u₀ ≫ m1.cm.F = y.u ρ j := h₁

  have hbase : u₀ ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
    apply GlobalTheory.IntLie.spMap_frac_cancel (V := 𝓞 K)
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, h₂', Category.assoc]
    have e := F.fib.2.1.1.w
    erw [e]
    rw [← Category.assoc, Over.w w]
    rfl

  have hact0 : ∀ a : 𝓞 E, u₀ ≫ (t₀.act.act a).left = spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ u₀ := by
    intro a
    apply m1.cart.1.hom_ext
    · rw [Category.assoc, m1.act a, ← Category.assoc, h₁', y.eig ρ j a, htt a, Category.assoc, h₁']
    · rw [Category.assoc, Over.w (t₀.act.act a), hbase, Category.assoc, hbase, GlobalTheory.IntLie.spMap_comp₂,
        GlobalTheory.IntLie.epsMul_alg]

  have hw : ∀ a : 𝓞 E, w.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w.left ≫ F.φ := by
    intro a
    rw [← reassoc_of% h₂', ← m2.act a, ← Category.assoc, hact0, Category.assoc, h₂']

  have hc' : u j ∈ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) := by
    rw [(GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K B.pol F).2]; trivial
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ (u j) hc'
  rw [Submodule.span_eq, Submonoid.smul_def] at hd
  obtain ⟨-, -, -, -, hlat, heig⟩ := GlobalTheory.CM.integral_tangent_coordinates K B.pol F
  obtain ⟨U, hUt, w₁, hUv, hw₁⟩ := (hlat _).1 hd
  have := F.P₀.isAb.comm
  have hK := GlobalTheory.LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
  set dK : K := algebraMap (𝓞 K) K (d : 𝓞 K) with hdK
  have hw₁' : w₁ = GlobalTheory.CM.IntCoord.sc dK ≫ w := by
    have h3 := hK.2.2.1 1 ![u j] ![w] ![dK] _ (fun i => by fin_cases i; exact hc)
      ((GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl)
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
      Finset.sum_singleton] at h3
    rw [← algebraMap_smul K (d : 𝓞 K) (u j)] at hw₁
    exact (hK.1 _).unique hw₁ h3
  have hw₁e : ∀ a : 𝓞 E, w₁.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w₁.left ≫ F.φ := by
    intro a
    rw [hw₁', sc_left, Category.assoc, Category.assoc]
    have := scale_eig dK ((tt a : 𝓞 K) : K) (w.left ≫ F.φ) (B.t.act.act a).left (by rw [Category.assoc, hw a])
    simpa only [Category.assoc] using this

  have := B.pol.isAb.proper
  have hmem : (d : 𝓞 K) • u j ∈ F.eigLat B.t.act tt := by
    rw [heig]
    refine ⟨U, ⟨hUt, w₁, hUv, hw₁⟩, fun a => ?_⟩
    rw [GlobalTheory.CM.IntCoord.isLieComb_one_iff]
    have hv1 : IsVecOver (algebraMap (𝓞 K) K) F.φ (U ≫ B.t.act.act a)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, Over.comp_left, ← Category.assoc, ← hUv, Category.assoc, Category.assoc, hw₁e a,
        epsScaleR_eq_epsMul]
    have hv2 : IsVecOver (algebraMap (𝓞 K) K) F.φ (GlobalTheory.CM.IntCoord.sc (tt a) ≫ U)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, sc_left, Category.assoc, hUv, epsScaleR_eq_epsMul]
      have e := dualMapR_epsScaleR (algebraMap (𝓞 K) K) (tt a)
      exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.left) e).trans (Category.assoc _ _ _))).symm
    exact GlobalTheory.CM.IntCoord.eq_of_isVecOver (IsFractionRing.injective (𝓞 K) K) hv1 hv2

  have hd0 : dK ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.coe_ne_zero d)
  have h₃ := Submodule.smul_mem (Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K))) dK⁻¹
    (Submodule.subset_span hmem)
  rwa [← algebraMap_smul K (d : 𝓞 K) (u j), ← hdK, inv_smul_smul₀ hd0] at h₃
end
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_coordinates_mem_span_eigenLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ j, u j ∈ Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)) := by
  atlas_forward_decl GlobalTheory.PtDeg.frameCoord_mem_span_eigLat
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LieSpan

theorem exists_isLieBasis_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib B.pol) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (n : SABMap G.t B.t (spMap ρV)), ∃ vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G), IsLieBasis vV ∧ ∀ k, ∃ (M : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A), IsLieComb M F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ ∧ (fun l => iK (M l)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) l => iK (v l)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
  intro E _ _ _ H K _ _ B F 𝔓 T iK hiK ρV hρV G n
  obtain ⟨N, r, M, hr, hM, -, hloc⟩ := GlobalTheory.T.lie_lattice_local_basis_description K B.pol F
  obtain ⟨i, hi⟩ : ∃ i, r i ∉ 𝔓.asIdeal := by
    by_contra h
    push_neg at h
    refine 𝔓.isPrime.ne_top ?_
    rw [eq_top_iff, ← hr]
    exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h j)
  have hv1 : ∀ m : ℕ, 𝔓.valuation K (algebraMap (𝓞 K) K (r i ^ m)) = 1 := fun m => by
    rw [HeightOneSpectrum.valuation_of_algebraMap, map_pow]
    rw [le_antisymm (𝔓.intValuation_le_one _) (not_lt.1 fun h => hi ((𝔓.intValuation_lt_one_iff_mem _).1 h)),
      one_pow]
  let R := Localization.subalgebra.ofField K (Submonoid.powers (r i))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (hM i).1)
  have e₁ : (algebraMap R K).comp (algebraMap (𝓞 K) R) = algebraMap (𝓞 K) K :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hval : ∀ z : R, iK (algebraMap R K z) ∈ Set.range (algebraMap T.V T.Fr) := fun z => by
    refine (hiK _).2 ?_
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (r i)) z
    have hz := congrArg (algebraMap R K) (IsLocalization.mk'_spec R x s)
    rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, e₁] at hz
    obtain ⟨m, hm⟩ := s.2
    have hs : 𝔓.valuation K (algebraMap (𝓞 K) K s) = 1 := by rw [← hm]; exact hv1 m
    have := congrArg (𝔓.valuation K) hz
    rw [map_mul, hs, _root_.mul_one] at this
    rw [this]
    exact 𝔓.valuation_le_one x
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.LamT.exists_restrict_ringHom (algebraMap R K) (algebraMap T.V T.Fr) hinj iK hval
  have hρ : ρV = ψ'.comp (algebraMap (𝓞 K) R) := by
    refine RingHom.ext fun x => hinj ?_
    have h₁ := RingHom.congr_fun hρV x
    have h₂ := RingHom.congr_fun hψ' (algebraMap (𝓞 K) R x)
    have h₃ := RingHom.congr_fun e₁ x
    simp only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  let GR := (Over.pullback (spMap (algebraMap (𝓞 K) R))).obj B.t.G
  have hp : IsGrpPullback GR B.t.G (spMap (algebraMap (𝓞 K) R)) (pullback.fst _ _) := isGrpPullback_pullback _ _
  have es₁ : spMap (algebraMap (𝓞 K) K) = spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [← spMap_comp, e₁]
  have hF : IsGrpPullback F.P₀.A B.t.G (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  have w₁ : F.φ ≫ B.t.G.hom = (F.P₀.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hF.1.w, es₁, Category.assoc]
  have hψ : IsGrpPullback F.P₀.A GR (spMap (algebraMap R K)) (hp.1.lift _ _ w₁) :=
    IsGrpPullback.cancel hp (hF.congr es₁ (hp.1.lift_fst _ _ w₁).symm) (hp.1.lift_snd _ _ w₁)
  obtain ⟨e, he, hx⟩ := hloc i R GR (pullback.fst _ _) (hp.1.lift _ _ w₁)
    (IsLocalization.map_units R (⟨r i, Submonoid.mem_powers _⟩ : Submonoid.powers (r i))) hp hψ
    (hp.1.lift_fst _ _ w₁)
  choose e₀ he₀ hM₀ using hx
  have hin := (GlobalTheory.T.lieLattice_localization_modelLieAlgebra K B.pol F R (Submonoid.powers (r i)) GR (pullback.fst _ _) (hp.1.lift _ _ w₁) e e₀ (M i)
    hp hψ (hp.1.lift_fst _ _ w₁) he fun k => ⟨he₀ k, hM₀ k⟩).1
  have es₂ : spMap ρV = spMap ψ' ≫ spMap (algebraMap (𝓞 K) R) := by rw [hρ]; exact spMap_comp _ _
  have hn : IsGrpPullback G.t.G B.t.G (spMap ρV) n.φ := n.cart
  have w₂ : n.φ ≫ B.t.G.hom = (G.t.G.hom ≫ spMap ψ') ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hn.1.w, es₂, Category.assoc]
  have hq : IsGrpPullback G.t.G GR (spMap ψ') (hp.1.lift _ _ w₂) :=
    IsGrpPullback.cancel hp (hn.congr es₂ (hp.1.lift_fst _ _ w₂).symm) (hp.1.lift_snd _ _ w₂)
  have hsm : Smooth GR.hom := by
    haveI := B.dim
    haveI : Smooth B.t.G.hom := SmoothOfRelativeDimension.smooth B.g _
    exact MorphismProperty.of_isPullback (P := @Smooth) hp.1 inferInstance
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange R T.V ψ' GR G.t.G _ hq hsm _ e he
  refine ⟨v', hb, fun k => ⟨M i k, e₀ k, hM₀ k, ?_, ?_⟩⟩
  · have ed : (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') =
        (Formalism.L2.Pj.dualMap iK).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) := by
      refine RingHom.ext fun x => ?_
      have h₁ := RingHom.congr_fun hψ' x.fst
      have h₂ := RingHom.congr_fun hψ' x.snd
      simp only [RingHom.comp_apply] at h₁ h₂
      refine TrivSqZeroExt.ext ?_ ?_
      · simpa [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR] using h₁
      · simp only [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
          zero_add]
        exact h₂
    have es : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') =
        spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) := by
      rw [← spMap_comp, ← spMap_comp, ed]
    have eL : (v' k).left ≫ n.φ =
        spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') ≫ (e k).left ≫ pullback.fst _ _ := by
      rw [← hp.1.lift_fst _ _ w₂, ← Category.assoc, hv' k, Category.assoc]
    have eR : (e₀ k).left ≫ F.φ =
        spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) ≫ (e k).left ≫ pullback.fst _ _ := by
      rw [← hp.1.lift_fst _ _ w₁, ← Category.assoc, he₀ k, Category.assoc]
    rw [eL, eR, ← Category.assoc, es, Category.assoc]
  · obtain ⟨_, ⟨m, rfl⟩, hs⟩ := hin k
    have hs0 : algebraMap (𝓞 K) K (r i ^ m) ≠ 0 := by
      intro h0
      have := hv1 m
      rw [h0, map_zero] at this
      exact zero_ne_one this
    obtain ⟨u, hu⟩ := (hiK (algebraMap (𝓞 K) K (r i ^ m))⁻¹).2 (by rw [map_inv₀, hv1 m, inv_one])
    have eq : (fun l => iK (M i k l)) = u • fun l => iK ((r i ^ m • M i k) l) := by
      funext l
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hu, map_inv₀]
      rw [← _root_.mul_assoc, inv_mul_cancel₀ ((map_ne_zero iK).2 hs0), _root_.one_mul]
    rw [eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hs, rfl⟩)

end GlobalTheory.LieSpan
end
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBasis_completion_in_span_lieLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib B.pol) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (n : SABMap G.t B.t (spMap ρV)), ∃ vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G), IsLieBasis vV ∧ ∀ k, ∃ (M : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A), IsLieComb M F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ ∧ (fun l => iK (M l)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) l => iK (v l)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
  atlas_forward_decl GlobalTheory.LieSpan.exists_isLieBasis_span
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

noncomputable section

open Limits

namespace GlobalTheory.LieLatGen

theorem exists_isLieBasis_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)), ∃ v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G), IsLieBasis v' ∧ ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ := by
  intro E _ _ _ H K _ _ B t₀ m2 F T iK t' n'
  have hF : IsGrpPullback F.P₀.A B.t.G (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  have hm : IsGrpPullback t₀.G B.t.G (spMap (algebraMap (𝓞 K) K)) m2.φ := m2.cart
  have hn : IsGrpPullback t'.G t₀.G (spMap iK) n'.φ := n'.cart
  have hc : IsGrpPullback t'.G B.t.G (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) (n'.φ ≫ m2.φ) := hn.comp hm
  have w : (n'.φ ≫ m2.φ) ≫ B.t.G.hom = (t'.G.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [hc.1.w, Category.assoc]
  have hq : IsGrpPullback t'.G F.P₀.A (spMap iK) (hF.1.lift _ _ w) :=
    IsGrpPullback.cancel hF (hc.congr rfl (hF.1.lift_fst _ _ w).symm) (hF.1.lift_snd _ _ w)
  have := F.P₀.isAb.comm
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange K T.Fr iK _ _ _ hq F.P₀.isAb.smooth _ F.v F.basis
  refine ⟨v', hb, fun k => ?_⟩
  rw [← hF.1.lift_fst _ _ w, ← Category.assoc, hv' k, Category.assoc]
  rfl

end GlobalTheory.LieLatGen
end
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBasis_fibre_over_completion_fraction_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)), ∃ v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G), IsLieBasis v' ∧ ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ := by
  atlas_forward_decl GlobalTheory.LieLatGen.exists_isLieBasis_fibre
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.CM GlobalTheory.LamT
namespace GlobalTheory.PtDeg.LieModel

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

theorem dualMap_id (R : Type) [CommRing R] : dualMap (RingHom.id R) = RingHom.id (DualNumber R) := by
  apply RingHom.ext
  intro x
  ext <;> simp [dualMap]

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [dualMap_id]; exact Spec.map_id _

theorem spMap_comp_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

theorem generic_coords_in_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G)) (M : Fin F.P₀.g → Fin F.P₀.g → K), IsLieBasis vV → (∀ k, ∃ w : epsR K ⟶ F.P₀.A, IsLieComb (M k) F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ) → ∀ (ub : epsOver T.V T.V ⟶ G.t.G) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), IsTan ub → u'' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ ub.left → ∃ (a : Fin F.P₀.g → T.V) (w'' : epsR T.Fr ⟶ t'.G), w''.left = u'' ∧ IsLieComb (∑ k, algebraMap T.V T.Fr (a k) • fun l => iK (M k l)) v' w'' := by
  intro E _ _ _ H K _ _ B t₀ m2 F T iK ρV hρV G t' n n' m2' h2 v' hv' hv'φ vV M hvV hM ub u'' hub hu''

  let ub' : epsR T.V ⟶ G.t.G := Over.homMk ub.left (Over.w ub)
  have hub' : IsTangent ub' := by
    unfold IsTangent
    refine hub.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ G.t.G) = toUnit _ ≫ η[G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  obtain ⟨a, ha, -⟩ := hvV.2 ub' hub'

  have hw'' : u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    apply spMap_frac_cancel (V := T.V)
    rw [Category.assoc, ← m2'.cart.1.w, ← Category.assoc, hu'', Category.assoc, Over.w ub]
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) = _
    exact (spMap_comp_two _ _).trans ((congrArg spMap (dualMap_alg _)).trans (spMap_comp_two _ _).symm)

  have hsq : ∀ k, (spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left) ≫ G.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := fun k => by
    rw [Category.assoc, Over.w (vV k)]
    exact (spMap_comp_two _ _).trans ((congrArg spMap (dualMap_alg _)).trans (spMap_comp_two _ _).symm)
  let g : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G) := fun k =>
    Over.homMk (m2'.cart.1.lift _ _ (hsq k)) (m2'.cart.1.lift_snd _ _ _)
  have hg1 : ∀ k, (g k).left ≫ m2'.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left :=
    fun k => m2'.cart.1.lift_fst _ _ _
  have hB : IsGrpPullback t'.G B.t.G (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) (n'.φ ≫ m2.φ) :=
    n'.cart.comp m2.cart
  have hT' := LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1
  have hgk : ∀ k, IsLieComb (fun l => iK (M k l)) v' (g k) := by
    intro k
    obtain ⟨wk, hwk, hwkeq⟩ := hM k
    obtain ⟨w₁, hw₁, -⟩ := hT'.1 (fun l => iK (M k l))
    have hf : spMap (RingHom.id T.Fr) ≫ (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) =
        spMap iK ≫ spMap (algebraMap (𝓞 K) K) := by rw [spMap_id', Category.id_comp]
    have hm := LetterInt.comb_match hB F.fib.2.1 (RingHom.id T.Fr) iK hf
      (fun i => by rw [spMap_dualMap_id, Category.id_comp]; exact hv'φ i) (fun _ => rfl) hw₁ hwk
    rw [spMap_dualMap_id, Category.id_comp] at hm
    have he : w₁ = g k := by
      refine Over.OverMorphism.ext (hB.1.hom_ext ?_ ((Over.w w₁).trans (Over.w (g k)).symm))
      rw [hm, ← hwkeq, ← h2, ← Category.assoc (g k).left, hg1, Category.assoc]
    exact he ▸ hw₁

  have hgt : ∀ k, IsTangent (g k) := fun k => hT'.2.1 _ _ (hgk k)
  obtain ⟨w, hw, -⟩ := (LieComb.lieComb_algebra T.Fr t'.G _ g hgt).1 (fun k => algebraMap T.V T.Fr (a k))
  have hcomb := hT'.2.2.1 _ (fun k l => iK (M k l)) g _ w hgk hw
  have hf2 : spMap (algebraMap T.V T.Fr) ≫ 𝟙 (Sp T.V) = spMap (RingHom.id T.Fr) ≫ spMap (algebraMap T.V T.Fr) := by
    rw [spMap_id', Category.id_comp, Category.comp_id]
  have hm2 := LetterInt.comb_match (isGrpPullback_self G.t.G) m2'.cart (algebraMap T.V T.Fr) (RingHom.id T.Fr) hf2
    (v₁ := vV) (v₂ := g) (fun i => by rw [spMap_dualMap_id, Category.id_comp, Category.comp_id, hg1])
    (c₁ := a) (c₂ := fun k => algebraMap T.V T.Fr (a k)) (fun _ => rfl) ha hw
  rw [spMap_dualMap_id, Category.id_comp, Category.comp_id] at hm2
  have hleft : w.left = u'' := by
    refine m2'.cart.1.hom_ext ?_ ((Over.w w).trans hw''.symm)
    rw [← hm2, hu'']
    rfl
  exact ⟨a, w, hleft, hcomb⟩

end GlobalTheory.PtDeg.LieModel
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_integral_tangent_in_span_lieBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G)) (M : Fin F.P₀.g → Fin F.P₀.g → K), IsLieBasis vV → (∀ k, ∃ w : epsR K ⟶ F.P₀.A, IsLieComb (M k) F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ) → ∀ (ub : epsOver T.V T.V ⟶ G.t.G) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), IsTan ub → u'' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ ub.left → ∃ (a : Fin F.P₀.g → T.V) (w'' : epsR T.Fr ⟶ t'.G), w''.left = u'' ∧ IsLieComb (∑ k, algebraMap T.V T.Fr (a k) • fun l => iK (M k l)) v' w'' := by
  atlas_forward_decl GlobalTheory.PtDeg.LieModel.generic_coords_in_span
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem over_of_fib {K : Type} [Field K] [NumberField K] {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)}
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol)
    (u₀ : Sp (DualNumber K) ⟶ t₀.G.left) (w : epsR K ⟶ F.P₀.A) (h : u₀ ≫ m2.φ = w.left ≫ F.φ) :
    u₀ ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  haveI : Mono (spMap (algebraMap (𝓞 K) K)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  rw [← cancel_mono (spMap (algebraMap (𝓞 K) K)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, h,
    Category.assoc]
  have := F.fib.2.1.1.w
  erw [this, ← Category.assoc, Over.w w]
  rfl

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

theorem spMap_dualMap_algebraMap {S R : Type} [CommRing S] [CommRing R] (f : S →+* R) :
    spMap (dualMap f) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap R (DualNumber R)) ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_dualMap_id {S : Type} [CommRing S] : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
  have : dualMap (RingHom.id S) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply TrivSqZeroExt.ext <;> simp [dualMap]
  simp only [spMap, this]
  exact Spec.map_id _

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lift_eps {K Tf : Type} [CommRing K] [CommRing Tf] {G' : Over (Sp Tf)} {G : Over (Sp K)}
    (f : K →+* Tf) {φ : G'.left ⟶ G.left} (hp : IsPullback φ G'.hom G.hom (spMap f))
    (u₀ : Sp (DualNumber K) ⟶ G.left) (hu : u₀ ≫ G.hom = spMap (algebraMap K (DualNumber K))) :
    ∃ g : epsR Tf ⟶ G', g.left ≫ φ = spMap (dualMap f) ≫ u₀ :=
  ⟨Over.homMk (hp.lift (spMap (dualMap f) ≫ u₀) (spMap (algebraMap Tf (DualNumber Tf)))
      (by rw [Category.assoc, hu, spMap_dualMap_algebraMap])) (hp.lift_snd _ _ _), hp.lift_fst _ _ _⟩

theorem isLieComb_of_match {K : Type} [Field K] [NumberField K] {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)}
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) {T : CDVR} (iK : K →+* T.Fr)
    {t' : SAB H (Sp T.Fr)} (n' : SABMap t' t₀ (spMap iK)) {v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)}
    (hv' : IsLieBasis v')
    (hv'φ : ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (dualMap iK) ≫ (F.v k).left ≫ F.φ)
    (c : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (hw : IsLieComb c F.v w) (g : epsR T.Fr ⟶ t'.G)
    (hg : g.left ≫ n'.φ ≫ m2.φ = spMap (dualMap iK) ≫ w.left ≫ F.φ) :
    IsLieComb (fun k => iK (c k)) v' g := by
  obtain ⟨w', hw'⟩ := ((GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1).1 (fun k => iK (c k))).exists
  have hpb := IsGrpPullback.comp n'.cart m2.cart
  have hid : spMap (RingHom.id T.Fr) = 𝟙 _ := by
    simp only [spMap, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have key := GlobalTheory.LamT.LetterInt.comb_match hpb F.fib.2.1 (RingHom.id T.Fr) iK
    (by rw [hid, Category.id_comp]) (v₁ := v') (v₂ := F.v)
    (fun k => by rw [spMap_dualMap_id, Category.id_comp]; exact hv'φ k) (c₁ := fun k => iK (c k)) (c₂ := c)
    (fun k => rfl) hw' hw
  rw [spMap_dualMap_id, Category.id_comp, ← hg] at key
  have : w' = g := Over.OverMorphism.ext (hpb.1.hom_ext key (by rw [Over.w w', Over.w g]))
  subst this
  exact hw'

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem comb_left_of_isCombAt {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Tf : Type} [CommRing Tf]
    {x : Sp Tf ⟶ Xo.X} {t' : SAB H (Sp Tf)} (m1' : SABMap t' Xo.univ.t x) {m : ℕ}
    (e : Fin m → (Sp (DualNumber Tf) ⟶ Xo.univ.t.G.left)) (cc : Fin m → Tf)
    (z : Sp (DualNumber Tf) ⟶ Xo.univ.t.G.left) (hz : IsCombAt x e cc z) (g : Fin m → (epsR Tf ⟶ t'.G))
    (hg : ∀ j, (g j).left ≫ m1'.φ = e j) (w'' : epsR Tf ⟶ t'.G) (hw : IsLieComb cc g w'') :
    w''.left ≫ m1'.φ = z := by
  obtain ⟨b, hb, rfl⟩ := hz
  obtain ⟨a, ha, rfl⟩ := hw
  have := GlobalTheory.LamT.LetterInt.prod_pull m1'.cart (epsR Tf) _ (𝟙 _) (by rw [Category.id_comp]; rfl) a b
    (fun j => by rw [hb j, Category.id_comp, ha j, Category.assoc, hg j]; rfl)
  rw [this, Category.id_comp]

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg

open GlobalTheory.PtDeg.FrameGen in
theorem frame_genFib_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (T : CDVR) (iK : K →+* T.Fr), letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x), m1'.φ = n'.φ ≫ m1.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → ∀ (i : Fin (Dw.mult ρ)) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) → u'' ≫ m1'.φ = y'.u ρ i → ∃ w'' : epsR T.Fr ⟶ t'.G, w''.left = u'' ∧ IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) v' w'' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ u hF T iK
  letI : Algebra c.F T.Fr := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hyT t' n' m1' h1 v' hv' hv'φ C a y' hchg i u'' hu''0 hu''1
  choose u₀ w hu₁ hu₂ hw using hF
  have hover : ∀ j, u₀ j ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) :=
    fun j => over_of_fib m2 F (u₀ j) (w j) (hu₂ j)
  choose g hg using fun j => exists_lift_eps iK n'.cart.1 (u₀ j) (hover j)
  have hg1 : ∀ j, (g j).left ≫ m1'.φ = yT.u ρ j := fun j => by
    rw [h1, ← Category.assoc, hg j, Category.assoc, hu₁ j]
    exact (hyT.2.1 ρ j).symm
  have hcomb : ∀ j, IsLieComb (fun k => iK (u j k)) v' (g j) := fun j =>
    isLieComb_of_match m2 F iK n' hv' hv'φ (u j) (w j) (hw j) (g j)
      (by rw [← Category.assoc, hg j, Category.assoc, hu₂ j])
  have hA := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1
  have htan : ∀ j, IsTangent (g j) := fun j => hA.2.1 _ _ (hcomb j)
  have hB := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ g htan
  obtain ⟨w'', hw''⟩ := (hB.1 (C ρ i)).exists
  have hleft : w''.left ≫ m1'.φ = y'.u ρ i :=
    comb_left_of_isCombAt m1' (yT.u ρ) (C ρ i) _ (hchg.2.1 ρ i) g hg1 w'' hw''
  refine ⟨w'', m1'.cart.1.hom_ext (by rw [hleft, hu''1]) (by rw [Over.w w'', hu''0]; rfl), ?_⟩
  exact hA.2.2.1 _ (fun j k => iK (u j k)) g (C ρ i) w'' hcomb hw''

end GlobalTheory.PtDeg
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_genericFibre_coordinates_eq_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (T : CDVR) (iK : K →+* T.Fr), letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x), m1'.φ = n'.φ ≫ m1.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → ∀ (i : Fin (Dw.mult ρ)) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) → u'' ≫ m1'.φ = y'.u ρ i → ∃ w'' : epsR T.Fr ⟶ t'.G, w''.left = u'' ∧ IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) v' w'' := by
  atlas_forward_decl GlobalTheory.PtDeg.frame_genFib_coords
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem GlobalTheory.PtDeg.intFrame_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hyT G t' n n' m1' m2' h1 h2 C a y' hchg hint i
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.T.exists_lieBasis_fibre_over_completion_fraction_field E H K B t₀ m2 F T iK t' n'
  obtain ⟨vV, hvV, hvVM⟩ := GlobalTheory.T.exists_lieBasis_completion_in_span_lieLattice E H K B F 𝔓 T iK hiK ρV hρV G n
  choose M w hMw hMn hMspan using hvVM
  obtain ⟨ub, hubT, -, -, hubu⟩ := hint
  obtain ⟨u', hu'1, hu'2⟩ := hubu ρ i
  obtain ⟨av, w₁, hw₁, hw₁c⟩ := GlobalTheory.T.genericFibre_integral_tangent_in_span_lieBasis E H K B t₀ m2 F T iK ρV hρV G t' n n' m2' h2 v' hv' hv'φ vV M hvV
    (fun k => ⟨w k, hMw k, hMn k⟩) (ub ρ i) u' (hubT ρ i) hu'2
  have hbase : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    rw [← hw₁]; exact Over.w w₁
  obtain ⟨w₂, hw₂, hw₂c⟩ := GlobalTheory.T.framedPoint_genericFibre_coordinates_eq_frame E H Dw l Xo c K y B t₀ m1 m2 F ρ u hu T iK yT hyT t' n' m1' h1 v' hv'
    hv'φ C a y' hchg i u' hbase hu'1
  obtain rfl : w₁ = w₂ := Over.OverMorphism.ext (hw₁.trans hw₂.symm)
  have htan : IsTangent w₁ :=
    (GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1).2.1 _ _ hw₁c
  have heq := (hv'.2 w₁ htan).unique hw₁c hw₂c
  have hWlie : (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V
      ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
    rw [← heq]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hMspan k)
  obtain ⟨r', -, hr'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K B.pol F (𝓞 E) B.t.act
  have hueig : ∀ j a, r' a (u j) = ((tt a : 𝓞 K) : K) • u j := by
    intro j a
    have := ((hr' tt (u j)).2).1 (GlobalTheory.T.framedPoint_coordinates_mem_span_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu j) a
    rw [this, ← algebraMap_smul K (tt a) (u j)]
  have hx := GlobalTheory.T.completed_span_eigen_vector_mem_eigen_sublattice K F.P₀.g F.lieLat (𝓞 E) (fun a => LinearMap.toMatrix' (r' a))
    (fun a => ((tt a : 𝓞 K) : K)) 𝔓 T iK hiK (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K B.pol F).1 _ hWlie (fun a => by
      rw [Matrix.mulVec_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, smul_comm]
      congr 1
      funext k
      rw [show (fun k => iK (u j k)) = iK ∘ u j from rfl, ← RingHom.map_mulVec, LinearMap.toMatrix'_mulVec, hueig j a]
      simp)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨c', ⟨hc1, hc2⟩, rfl⟩
  refine ⟨c', (hr' tt c').1.2 ⟨hc1, fun a => ?_⟩, rfl⟩
  have := hc2 a
  rw [LinearMap.toMatrix'_mulVec] at this
  rw [this, ← algebraMap_smul K (tt a) c']
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_point_integral_frame_mem_span_eigen_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) := by
  atlas_forward_decl GlobalTheory.PtDeg.intFrame_mem_span_eigLat
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem GlobalTheory.PtDeg.intFrame_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) ∧ ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV
  intro yT hyT G t' n n' m1' m2' h1 h2 C a y' hC hL
  exact ⟨GlobalTheory.T.cm_point_integral_frame_mem_span_eigen_lattice E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV yT hyT G t' n n' m1' m2' h1 h2 C a y' hC hL,
    GlobalTheory.T.completed_eigenLattice_le_span_integral_frame E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV yT hyT G t' n n' m1' m2' h1 h2 C a y' hC hL⟩
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrame_span_completed_eigenLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) ∧ ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  atlas_forward_decl GlobalTheory.PtDeg.intFrame_span_eigLat
end
