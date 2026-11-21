import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGeneric
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTraitNonlocalTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionUniformisationEqRestrictCharacters

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KummerConj

open GlobalTheory.TorusExt GlobalTheory.UnramTorsion GlobalTheory.BXOf

attribute [local instance] gtGroup

theorem valuation_val_eq {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (O : ValuationSubring F) (φ : R →+* O)
    (hφ : ∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r))
    {X : Scheme.{0}} {L : LB X} (J₀ : X → L.ι) (h₀ : ∀ x, x ∈ L.U (J₀ x)) {J : (Sp F ⟶ X) → L.ι}
    (hJ : Good L (closedPoint F) J) (eJ : ∀ ψ : Sp O ⟶ X, J (spMap O.subtype ≫ ψ) = J₀ (ψ (closedPoint O)))
    {K : Type} [Fintype K] {φs : K → ((TK R).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φs ε))
    (ht : t.IsGen) (p : K → (Spec (CommRingCat.of R) ⟶ X)) (hp : ∀ k, φs k = jK R ≫ p k) (j : K → L.ι)
    (hj : ∀ k, ⊤ ≤ p k ⁻¹ᵁ L.U (j k)) (h : ⊤ ≤ (LB.LinComb L φs ε).U j) :
    O.valuation (sig F (val t (jFK (R := R) F) (closedPoint F) J) : F) =
      O.valuation (algebraMap (FractionRing R) F (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h)) := by
  have hs : spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R := by
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ
  have hr : ∀ k, jFK (R := R) F ≫ φs k = spMap O.subtype ≫ (spMap φ ≫ p k) := fun k => by
    rw [hp k, ← Category.assoc, ← Category.assoc, hs]
  obtain ⟨w, hw⟩ : ∃ w : ((Sp F).presheaf.stalk (closedPoint F))ˣ →* O.ValueGroupˣ,
      ∀ u, (w u : O.ValueGroup) = O.valuation (sig F u : F) :=
    ⟨(Units.map O.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩
  have hunit : ∀ (ψ : Sp O ⟶ X) (U : X.Opens) (hU : ψ (closedPoint O) ∈ U) (a : Γ(X, U)ˣ),
      w (gm (spMap O.subtype ≫ ψ) (closedPoint F) U a) = 1 := fun ψ U hU a => by
    refine Units.ext ((hw _).trans ?_)
    rw [← sig_nat O.subtype ψ hU a]
    exact O.valuation_unit _
  have hz : jFK (R := R) F (closedPoint F) ∈ LB.wchart L φs j := h trivial
  have g := gen_trans ht (jFK (R := R) F) (closedPoint F) (hJ.mem φs (jFK (R := R) F)) hz
  have htr : w (trF φs ε (jFK (R := R) F) (closedPoint F) (fun k => J (jFK (R := R) F ≫ φs k)) j) = 1 := by
    show w (∏ k, gm (jFK (R := R) F ≫ φs k) (closedPoint F) (L.U (J (jFK (R := R) F ≫ φs k)) ⊓ L.U (j k))
      (L.g (J (jFK (R := R) F ≫ φs k)) (j k)) ^ ε k) = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_zpow]
    refine (congrArg (· ^ ε k) ?_).trans (one_zpow _)
    rw [hr k]
    apply hunit
    exact ⟨by rw [eJ]; exact h₀ _, hj k (show spMap φ (closedPoint O) ∈ ⊤ from trivial)⟩
  have hgv : (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R)) ((LB.LinComb L φs ε).U j)
      (t.s j)).val = ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ (closedPoint (FractionRing R))
        trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
          (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h).val) := by
    refine (gm_val (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R)) _ (h trivial) (t.s j)).trans ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, Units.coe_map, MonoidHom.coe_coe, res, RingHom.toMonoidHom_eq_coe]
    rw [Iso.hom_inv_id_apply]
    exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h)
      (closedPoint (FractionRing R)) trivial _).symm
  have hsg : sig (FractionRing R) (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R))
      (LB.wchart L φs j) (t.s j)) = GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h := by
    refine Units.ext ((congrArg (stalkClosedPointIso (CommRingCat.of (FractionRing R))).hom.hom hgv).trans ?_)
    rw [← CommRingCat.comp_apply, germ_stalkClosedPointIso_hom, Iso.inv_hom_id_apply]
  have n := sig_nat (algebraMap (FractionRing R) F) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (h trivial) (t.s j)
  rw [Category.comp_id] at n
  have n2 := (congrArg (Units.map (algebraMap (FractionRing R) F).toMonoidHom) hsg).symm.trans n
  have e : w (val t (jFK (R := R) F) (closedPoint F) J) =
      w (gm (jFK (R := R) F) (closedPoint F) ((LB.LinComb L φs ε).U j) (t.s j)) := by
    refine (congrArg w g).trans ?_
    rw [map_mul, htr, _root_.one_mul]
    rfl
  rw [← hw, e, hw]
  exact congrArg (fun u : Fˣ => O.valuation (u : F)) n2.symm

theorem conj_eq_add_tor : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ) (σ : F →ₐ[FractionRing R] F) (p p' : QkPt D F k), QkExt σ.toRingHom p p' →
    spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left →
    ∃ (τ : Multiplicative D.X →* Fˣ) (q : QkPt D F k), τ ^ k = 1 ∧ q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkAdd p q p' ∧
      ∀ (χ : D.X) (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D p.y χ x →
        ∃ s : F, s ≠ 0 ∧ O.valuation s ^ k = O.valuation (algebraMap (FractionRing R) F x) ∧
          σ s = (τ (Multiplicative.ofAdd χ) : F) * s := by
  intro R _ _ D hB F _ _ O φ hφ k σ p p' hext hfix
  have hσ' : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F :=
    RingHom.ext fun a => σ.commutes a
  obtain rfl : p' = qkExt hB σ.toRingHom hσ' p := (qkExt_iff hB _ hσ' _ _).1 hext
  have hb : extMap σ.toRingHom hσ' ≫ p.g.b = p.g.b := Over.OverMorphism.ext hfix
  set d : GtPtF D F := gtExt D σ.toRingHom hσ' p.g - p.g with hd
  have hdb : d.b = 1 := by
    rw [hd, sub_eq_add_neg, add_b, neg_b, gtExt_b, hb, mul_inv_cancel]
  have hgd : gtExt D σ.toRingHom hσ' p.g = p.g + d := by rw [hd, add_sub_cancel]
  obtain ⟨τ, hτ⟩ := exists_torusPt_eq hdb
  have hkd : k • d = 0 := by
    rw [hd, nsmul_sub, ← map_nsmul, qk_nsmul hB, gtExt_iota, sub_self]
  have hτk : τ ^ k = 1 := by
    have e : torusPt D F (Additive.ofMul (τ ^ k)) = torusPt D F (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, ← hτ, hkd, ofMul_one, map_zero]
    exact Additive.ofMul.injective (torusPt_injective e)
  let q : QkPt D F k := qkMk hB 0 d (by rw [hkd, map_zero])
  refine ⟨τ, q, hτk, rfl, (GlobalTheory.UT.isTor_iff _ _).2 ((isTorusPtF_iff_eq d τ).2 hτ), ?_, fun χ x hx => ?_⟩
  · refine (qkAdd_iff hB _ _ _).2 ?_
    have e : qkAdd hB p q = qkExt hB σ.toRingHom hσ' p := qk_ext (add_zero _) hgd.symm
    rw [e]
    exact qk_equiv_refl hB _

  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  choose J₀ h₀ using fun x : D.P.A.left => exists_chart D.P.isLB x
  obtain ⟨J, hJ, eJ⟩ := exists_good_ext D.P.isLB O.subtype Subtype.val_injective J₀ h₀
  let z : (TF (R := R) F).left := closedPoint F
  have hJ' : Good D.P.L z J := hJ
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ) := Over.homMk (spMap O.subtype) (by
    show spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  obtain ⟨w, hw⟩ : ∃ w : ((TF (R := R) F).left.presheaf.stalk z)ˣ →* O.ValueGroupˣ,
      ∀ u, (w u : O.ValueGroup) = O.valuation (sig F u : F) :=
    ⟨(Units.map O.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩
  have hint : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (ψ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L ψ ε)) (r : (Over.mk (spMap φ)).left ⟶ Y), w (val t (ρ.left ≫ r) z J) = 1 := by
    intro Y K _ ψ ε t r
    obtain ⟨u, hu⟩ := val_integral O.subtype h₀ eJ t r
    exact Units.ext ((hw _).trans ((congrArg O.valuation hu).trans (O.valuation_unit u)))
  obtain ⟨b, hb'⟩ := exists_extend O φ ρ rfl p.g.b
  have e₁ := w_nsmul ρ hJ' w hint p.g b hb' χ k
  rw [qk_nsmul hB, iota_val hB _ _ hJ'] at e₁
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ'
  refine ⟨(sig F (charVal p.g χ z J) : F), Units.ne_zero _, ?_, ?_⟩
  · have e₂ := congrArg Units.val e₁
    rw [Units.val_pow_eq_pow_val, hw, hw] at e₂
    rw [← e₂]
    obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
    have er : (𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F = jFK (R := R) F := by simp
    show O.valuation (sig F (val (D.tau p.y χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J) : F) = _
    rw [er]
    refine valuation_val_eq O φ hφ J₀ h₀ hJ eJ (D.tau p.y χ) (tau_isGen D _ _)
      (Sum.elim (Sum.elim (Sum.elim (fun _ => (D.c (p.y + χ)).left) (fun _ => (D.c p.y).left))
        (fun _ => (D.c χ).left)) (fun _ => (η[D.P.A] : _ ⟶ _).left)) ?_ j ?_ h
    · rintro (((_ | _) | _) | _)
      · rfl
      · rfl
      · rfl
      · show (toUnit (TK R)).left ≫ eSec D.P.A = jK R ≫ (η[D.P.A] : _ ⟶ _).left
        have e : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
        rw [e]
        rfl
    · rintro (((_ | _) | _) | _)
      exacts [i1, i2, i3, i4]
  · have key : σ (sig F (charVal p.g χ z J) : F) =
        (sig F (charVal (gtExt D σ.toRingHom hσ' p.g) χ z J) : F) := by
      have e := gtExt_val σ.toRingHom hσ' p.g χ hJ'
      have hφ' : ∀ i, (extMap σ.toRingHom hσ').left ≫ DegPre.gtφ D F p.g.b χ i =
          𝟙 _ ≫ DegPre.gtφ D F p.g.b χ i := by
        intro i
        rw [Category.id_comp]
        fin_cases i
        · show (extMap σ.toRingHom hσ' ≫ (cP D _ χ * p.g.b)).left = (cP D _ χ * p.g.b).left
          rw [MonObj.comp_mul, comp_cP, hb]
        · show (extMap σ.toRingHom hσ' ≫ cP D _ χ).left = (cP D _ χ).left
          rw [comp_cP]
        · show (extMap σ.toRingHom hσ' ≫ p.g.b).left = p.g.b.left
          rw [hb]
        · show (extMap σ.toRingHom hσ' ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
          rw [MonObj.comp_one]
      replace e := e.trans (val_of (p.g.s χ) _ _ J _ (fun i => congrArg J (hφ' i)))
      have n := sig_nat σ.toRingHom (𝟙 (Spec (CommRingCat.of F))) (hJ'.mem (DegPre.gtφ D F p.g.b χ) (𝟙 _))
        ((p.g.s χ).s fun i => J (𝟙 _ ≫ DegPre.gtφ D F p.g.b χ i))
      rw [Category.comp_id] at n
      exact (congrArg Units.val n).trans (congrArg (fun u => (sig F u : F)) e.symm)
    have hs : sig F (charVal d χ z J) = τ (Multiplicative.ofAdd χ) := by
      rw [hτ, torusPt_val τ χ hJ']
      refine Units.ext ?_
      show (stalkClosedPointIso (CommRingCat.of F)).hom.hom (((Sp F).presheaf.germ ⊤ (closedPoint F) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd χ) : F))) = _
      rw [← CommRingCat.comp_apply, germ_stalkClosedPointIso_hom, Iso.inv_hom_id_apply]
    have e := add_val p.g d χ hJ'
    rw [hdb, C.face₃, _root_.mul_one] at e
    rw [key, hgd, e, map_mul, Units.val_mul, hs, mul_comm]

end GlobalTheory.KummerConj
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_eq_add_kummer_torusTorsionPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ) (σ : F →ₐ[FractionRing R] F) (p p' : QkPt D F k), QkExt σ.toRingHom p p' →
    spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left →
    ∃ (τ : Multiplicative D.X →* Fˣ) (q : QkPt D F k), τ ^ k = 1 ∧ q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkAdd p q p' ∧
      ∀ (χ : D.X) (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D p.y χ x →
        ∃ s : F, s ≠ 0 ∧ O.valuation s ^ k = O.valuation (algebraMap (FractionRing R) F x) ∧
          σ s = (τ (Multiplicative.ofAdd χ) : F) * s := by
  first | exact @GlobalTheory.KummerConj.conj_eq_add_tor | exact GlobalTheory.KummerConj.conj_eq_add_tor | (intros; apply GlobalTheory.KummerConj.conj_eq_add_tor <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.DomValInt

theorem isIntegral_of_forall_valuationSubring (W : Type) [CommRing W] (F : Type) [Field F]
    [Algebra W F] (y : F)
    (hy : ∀ V : ValuationSubring F, (∀ w : W, algebraMap W F w ∈ V) → y ∈ V) :
    IsIntegral W y := by
  have hcl : IsIntegrallyClosedIn (integralClosure W F).toSubring F :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure W F) F)
  by_contra hn
  have hsn : y ∉ (integralClosure W F).toSubring := hn
  obtain ⟨V, hV, hyV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hsn
  exact hyV (hy V fun w => hV (Subalgebra.algebraMap_mem _ w))

theorem split_rel {F : Type} [Field F] (c : ℕ → F) (x : F) (n j : ℕ) (hjn : j ≤ n)
    (hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) :
    (∑ i ∈ Finset.range j, c i * x ^ i) +
      x ^ j * ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k = 0 := by
  rw [← hrel, show n + 1 = j + (n + 1 - j) by omega, Finset.sum_range_add, Finset.mul_sum,
    show j + (n + 1 - j) - j = n + 1 - j by omega]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_add]; ring

theorem tail_mem {F' : Type} [Field F'] (V : ValuationSubring F') (c : ℕ → F') (hc : ∀ i, c i ∈ V) (x : F')
    (n j : ℕ) (hjn : j ≤ n) (hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) :
    (∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k) ∈ V ∧
      (∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k) * x ∈ V := by
  have hsplit := split_rel c x n j hjn hrel
  set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs
  by_cases hxV : x ∈ V
  · have : s ∈ V := by
      rw [hs]
      exact sum_mem fun k _ => mul_mem (hc _) (pow_mem hxV k)
    exact ⟨this, mul_mem this hxV⟩
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
  have hxi : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  rcases j with _ | j'
  · simp at hsplit
    rw [hsplit]; simp
  · set A' := ∑ i ∈ Finset.range (j' + 1), c i * x⁻¹ ^ (j' - i) with hA'
    have hA'V : A' ∈ V := sum_mem fun i _ => mul_mem (hc _) (pow_mem hxi _)
    have hA'x : A' * x ^ j' = ∑ i ∈ Finset.range (j' + 1), c i * x ^ i := by
      rw [hA', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show x ^ j' = x ^ (j' - i) * x ^ i by rw [← pow_add]; congr 1; omega, inv_pow]
      field_simp
    have hsx : s * x = -A' := by
      have hpow : x ^ j' ≠ 0 := pow_ne_zero _ hx0
      apply mul_right_cancel₀ hpow
      rw [neg_mul, hA'x, _root_.mul_assoc, ← pow_succ']
      linear_combination hsplit
    have htV : s * x ∈ V := by rw [hsx]; exact neg_mem hA'V
    refine ⟨?_, htV⟩
    have : s = (s * x) * x⁻¹ := by field_simp
    rw [this]; exact mul_mem htV hxi

end GlobalTheory.DomValInt

namespace GlobalTheory.DomValInt

theorem exists_integral_quotient :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra.IsAlgebraic (FractionRing W) F] [Algebra W F]
    [IsScalarTower W (FractionRing W) F] (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ x ∈ O, ∃ s t : F, IsIntegral W s ∧ IsIntegral W t ∧ O.valuation s = 1 ∧ s * x = t := by
  intro W _ _ _ F _ _ _ _ _ O hW hmax x hxO

  have hK : ∀ a : FractionRing W, algebraMap (FractionRing W) F a ∈ O →
      ∃ w : W, algebraMap W F w = algebraMap (FractionRing W) F a := by
    intro a ha
    rcases ValuationRing.isInteger_or_isInteger W a with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact ⟨w, by rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, hw]⟩
    · by_cases ha0 : a = 0
      · exact ⟨0, by simp [ha0]⟩
      by_cases hu : IsUnit w
      · refine ⟨↑hu.unit⁻¹, ?_⟩
        have h1 : a⁻¹ * algebraMap W (FractionRing W) ↑hu.unit⁻¹ = 1 := by
          rw [← hw, ← map_mul, IsUnit.mul_val_inv, map_one]
        have h2 := (inv_mul_eq_one₀ ha0).mp h1
        rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, ← h2]
      · have hwm : w ∈ maximalIdeal W := (mem_maximalIdeal _).mpr hu
        have h2 := (O.mem_nonunits_iff).mp (hmax w hwm)
        have h3 := (O.valuation_le_one_iff _).mpr ha
        have h4 : algebraMap (FractionRing W) F a * algebraMap W F w = 1 := by
          rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, hw, ← map_mul,
            mul_inv_cancel₀ ha0, map_one]
        have h5 : O.valuation (algebraMap (FractionRing W) F a * algebraMap W F w) < 1 := by
          rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' h3) h2
        rw [h4, map_one] at h5
        exact absurd h5 (lt_irrefl _)

  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing W) x
  set n := p.natDegree with hn
  set b : ℕ → F := fun i => algebraMap (FractionRing W) F (p.coeff i) with hb
  set v := O.valuation with hv
  obtain ⟨i0, hi0, hi0max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun i => v (b i)) ⟨0, by simp⟩
  set M := v (b i0) with hM
  set S := (Finset.range (n + 1)).filter (fun i => v (b i) = M) with hS
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S id
    ⟨i0, Finset.mem_filter.mpr ⟨hi0, rfl⟩⟩
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hjS).1)
  have hjM : v (b j) = M := (Finset.mem_filter.mp hjS).2
  have hcoeff0 : ∀ i, n < i → b i = 0 := fun i hi => by
    simp [b, Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega)]
  have hle : ∀ i, v (b i) ≤ M := fun i => by
    by_cases hi : i ≤ n
    · exact hi0max i (Finset.mem_range.mpr (by omega))
    · rw [hcoeff0 i (by omega), map_zero]; exact zero_le'
  have hM0 : M ≠ 0 := by
    intro h
    have h1 : v (b n) = 0 := le_antisymm (h ▸ hle n) zero_le'
    rw [Valuation.zero_iff] at h1
    have h2 : p.leadingCoeff = 0 := (algebraMap (FractionRing W) F).injective (by rw [map_zero]; exact h1)
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h2)
  have hlt : ∀ i, j < i → v (b i) < M := by
    intro i hi
    rcases lt_or_eq_of_le (hle i) with h | h
    · exact h
    exfalso
    by_cases hin : i ≤ n
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
      have := hjmax i hiS
      simp only [id] at this
      omega
    · rw [hcoeff0 i (by omega), map_zero] at h
      exact hM0 h.symm
  have hbj : b j ≠ 0 := fun h => hM0 (by rw [← hjM, h, map_zero])
  have hMpos : 0 < M := zero_lt_iff.mpr hM0
  set c : ℕ → F := fun i => b i / b j with hc
  have hcle : ∀ i, v (c i) ≤ 1 := fun i => by
    simp only [c, map_div₀, hjM]
    exact (div_le_one₀ hMpos).mpr (hle i)
  have hclt : ∀ i, j < i → v (c i) < 1 := fun i hi => by
    simp only [c, map_div₀, hjM]
    exact (div_lt_one₀ hMpos).mpr (hlt i hi)
  have hcW : ∀ i, ∃ w : W, algebraMap W F w = c i := fun i => by
    have hci : c i = algebraMap (FractionRing W) F (p.coeff i / p.coeff j) := by
      simp [c, b, map_div₀]
    rw [hci]
    exact hK _ (by rw [← hci]; exact (O.valuation_le_one_iff _).mp (hcle i))
  have hcj : c j = 1 := div_self hbj
  have hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0 := by
    have h := hpx
    rw [Polynomial.aeval_eq_sum_range] at h
    simp only [c, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [div_eq_zero_iff]
    left
    simpa [Algebra.smul_def, b] using h
  set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs
  have hmemV : ∀ V : ValuationSubring F, (∀ w : W, algebraMap W F w ∈ V) → s ∈ V ∧ s * x ∈ V :=
    fun V hV => tail_mem V c (fun i => by obtain ⟨w, hw⟩ := hcW i; rw [← hw]; exact hV w)
      x n j hjn hrel
  refine ⟨s, s * x, isIntegral_of_forall_valuationSubring W F s fun V hV => (hmemV V hV).1,
    isIntegral_of_forall_valuationSubring W F _ fun V hV => (hmemV V hV).2, ?_, rfl⟩
  have hxle : v x ≤ 1 := (O.valuation_le_one_iff x).mpr hxO
  rw [hs, show n + 1 - j = (n - j) + 1 by omega, Finset.sum_range_succ', Nat.add_zero, pow_zero,
    _root_.mul_one, hcj, Valuation.map_add_eq_of_lt_right, map_one]
  rw [map_one]
  apply Valuation.map_sum_lt _ one_ne_zero
  intro k _
  rw [map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hxle _)) (hclt _ (by omega))

end GlobalTheory.DomValInt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_quotient_dominating_valuationSubring : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra.IsAlgebraic (FractionRing W) F] [Algebra W F]
    [IsScalarTower W (FractionRing W) F] (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ x ∈ O, ∃ s t : F, IsIntegral W s ∧ IsIntegral W t ∧ O.valuation s = 1 ∧ s * x = t := by
  atlas_forward_decl GlobalTheory.DomValInt.exists_integral_quotient
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

open Polynomial

namespace GlobalTheory.RootOfUniformiserDVR

theorem val_term_le_one' {F : Type} [Field F] {O : ValuationSubring F} {β : Type} (s : Finset β) (f : β → F)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → O.valuation (f i) = O.valuation (f j) → i = j)
    (hs : O.valuation (∑ i ∈ s, f i) ≤ 1) : ∀ i ∈ s, O.valuation (f i) ≤ 1 := by
  classical
  intro i hi
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => O.valuation (f i)) ⟨i, hi⟩
  by_cases h0 : f j = 0
  · refine (hmax i hi).trans ?_
    simp [h0]
  refine (hmax i hi).trans ?_
  rw [← Finset.add_sum_erase s f hj] at hs
  rwa [Valuation.map_add_eq_of_lt_left] at hs
  refine Valuation.map_sum_lt _ (by simpa using h0) fun k hk => ?_
  rw [Finset.mem_erase] at hk
  exact lt_of_le_of_ne (hmax k hk.2) fun he => hk.1 (hf j hj k hk.2 h0 he.symm).symm

theorem cong_on_adjoin : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra W F] [IsScalarTower W (FractionRing W) F]
    (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ (ϖ : W), Irreducible ϖ → ∀ (l : ℕ), l ≠ 0 → ∀ (x : F), x ^ l = algebraMap W F ϖ →
    ∀ (g : F ≃ₐ[FractionRing W] F) (b : F), b ∈ IntermediateField.adjoin (FractionRing W) {x} →
    O.valuation b ≤ 1 → O.valuation (g b - b) < 1 := by
  intro W _ _ _ F _ _ _ _ O hO hm ϖ hϖ l hl0 x hx g b hb hb1
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  set ϖK : FractionRing W := algebraMap W (FractionRing W) ϖ with hϖK
  have hx' : x ^ l = algebraMap (FractionRing W) F ϖK := by
    rw [hx, hϖK, ← IsScalarTower.algebraMap_apply]
  have hunit : ∀ u : Wˣ, O.valuation (algebraMap W F (u : W)) = 1 := by
    intro u
    have a1 := (O.valuation_le_one_iff _).2 (hO u)
    have a2 := (O.valuation_le_one_iff _).2 (hO ((u⁻¹ : Wˣ) : W))
    have e : O.valuation (algebraMap W F (u : W)) * O.valuation (algebraMap W F ((u⁻¹ : Wˣ) : W)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm a1 ?_
    by_contra hc
    push_neg at hc
    have := mul_lt_one_of_lt_of_le hc a2
    rw [e] at this
    exact lt_irrefl _ this
  have hϖlt : O.valuation (algebraMap W F ϖ) < 1 := by
    have := hm ϖ ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
    exact this
  have hWv : ∀ w : W, w ≠ 0 → ∃ n : ℕ,
      O.valuation (algebraMap W F w) = O.valuation (algebraMap W F ϖ) ^ n := by
    intro w hw
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
    exact ⟨n, by rw [map_mul, map_mul, hunit, _root_.one_mul, map_pow, map_pow]⟩

  have hvpos : ∀ w : W, w ≠ 0 → O.valuation (algebraMap W F w) ≠ 0 := by
    intro w hw
    rw [Valuation.ne_zero_iff]
    intro h0
    apply hw
    have : algebraMap W (FractionRing W) w = 0 := by
      rw [IsScalarTower.algebraMap_apply W (FractionRing W) F] at h0
      exact (map_eq_zero _).mp h0
    exact (IsFractionRing.injective W (FractionRing W)) (by rw [this, map_zero])
  have hK : ∀ a : FractionRing W, a ≠ 0 → ∃ m : ℤ,
      O.valuation (algebraMap (FractionRing W) F a) = O.valuation (algebraMap (FractionRing W) F ϖK) ^ m := by
    intro a ha
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := W) a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hp0 : p ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨n, hn⟩ := hWv p hp0
    obtain ⟨k, hk⟩ := hWv q hq0
    refine ⟨(n : ℤ) - k, ?_⟩
    rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hϖK,
      ← IsScalarTower.algebraMap_apply, hn, hk, zpow_sub₀ (hvpos ϖ hϖ0), zpow_natCast, zpow_natCast]
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0, eq_comm] at hx
    exact hvpos ϖ hϖ0 (by rw [hx, map_zero])
  set t := O.valuation x with ht
  have htl : O.valuation (algebraMap (FractionRing W) F ϖK) = t ^ l := by rw [← hx', map_pow]
  have ht0 : 0 < t := zero_lt_iff.mpr (by simpa [ht] using hx0)
  have ht1 : t < 1 := by
    have := hϖlt
    rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, ← hϖK, htl] at this
    exact (pow_lt_one_iff hl0).mp this
  have hinj : Function.Injective fun n : ℤ => t ^ n := zpow_right_injective₀ ht0 ht1.ne
  have hval : ∀ (a : FractionRing W) (i : ℕ), algebraMap (FractionRing W) F a * x ^ i ≠ 0 →
      ∃ m : ℤ, O.valuation (algebraMap (FractionRing W) F a * x ^ i) = t ^ ((i : ℤ) + l * m) := by
    intro a i ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨m, hm⟩ := hK a ha0
    refine ⟨m, ?_⟩
    rw [map_mul, hm, htl, map_pow, zpow_add₀ ht0.ne', zpow_mul, zpow_natCast, zpow_natCast, mul_comm]
  have hmod : ∀ (i j : ℕ) (m n : ℤ), i < l → j < l → t ^ ((i : ℤ) + l * m) = t ^ ((j : ℤ) + l * n) →
      i = j := by
    intro i j m n hi hj he
    have := congrArg (· % (l : ℤ)) (hinj he)
    simp only [Int.add_mul_emod_self_left] at this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  have hq : (X ^ l - C ϖK).Monic := monic_X_pow_sub_C _ hl0
  have hint : IsIntegral (FractionRing W) x := ⟨X ^ l - C ϖK, hq, by simp [hx']⟩
  have hb' : b ∈ Algebra.adjoin (FractionRing W) {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]; exact hb
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb'
  obtain ⟨p₀, rfl⟩ := hb'
  set p := p₀ %ₘ (X ^ l - C ϖK)
  have hp : aeval x p = aeval x p₀ := aeval_modByMonic_eq_self_of_root (by simp [hx'])
  have hdeg : p.natDegree < l := by
    have := natDegree_modByMonic_lt p₀ hq (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow_sub_C, natDegree_one] at this
      exact hl0 this)
    rwa [natDegree_X_pow_sub_C] at this
  change O.valuation (aeval x p₀) ≤ 1 at hb1
  change O.valuation (g (aeval x p₀) - aeval x p₀) < 1
  rw [← hp, aeval_eq_sum_range' hdeg] at hb1 ⊢
  simp only [Algebra.smul_def] at hb1 ⊢
  have hle := val_term_le_one' _ _ (fun i hi j hj h0 he => by
    obtain ⟨m, hm⟩ := hval _ i h0
    obtain ⟨n, hn⟩ := hval (p.coeff j) j (by
      intro h00
      rw [h00, map_zero] at he
      exact h0 (by simpa using he))
    exact hmod i j m n (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by rw [← hm, ← hn, he])) hb1
  have hgx : O.valuation (g x) = t := by
    refine pow_left_injective hl0 ?_
    show _ ^ l = t ^ l
    rw [← map_pow, ← map_pow, hx', g.commutes, htl]
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  have hlt : O.valuation (algebraMap (FractionRing W) F (p.coeff i) * x ^ i) < 1 := by
    refine lt_of_le_of_ne (hle i hi) fun he => ?_
    obtain ⟨m, hm⟩ := hval (p.coeff i) i (by intro h0; simp [h0] at he)
    have := hmod i 0 m 0 (Finset.mem_range.mp hi) (by omega) (by rw [← hm, he]; simp)
    omega
  refine Valuation.map_sub_lt _ ?_ hlt
  rw [map_mul g, g.commutes, map_pow g, map_mul, map_pow, hgx]
  rwa [map_mul, map_pow] at hlt

end GlobalTheory.RootOfUniformiserDVR
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphism_congr_one_on_adjoin_root_uniformiser : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra W F] [IsScalarTower W (FractionRing W) F]
    (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ (ϖ : W), Irreducible ϖ → ∀ (l : ℕ), l ≠ 0 → ∀ (x : F), x ^ l = algebraMap W F ϖ →
    ∀ (g : F ≃ₐ[FractionRing W] F) (b : F), b ∈ IntermediateField.adjoin (FractionRing W) {x} →
    O.valuation b ≤ 1 → O.valuation (g b - b) < 1 := by
  atlas_forward_decl GlobalTheory.RootOfUniformiserDVR.cong_on_adjoin
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaTameRoot

theorem exists_inertia_moves_root : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] [CharZero W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] [IsAlgClosure (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ k : ℕ, IsUnit (k : W) → ∃ (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F),
      IsLocalHom φ ∧ (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) ∧
      (∀ x ∈ O, O.valuation (σ x - x) < 1) ∧ π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ∧
      IsPrimitiveRoot (σ π / π) k := by
  intro W _ _ _ _ _ F _ _ _ ϖ hϖ k hk
  let K := FractionRing W
  letI : Algebra W F := ((algebraMap K F).comp (algebraMap W K)).toAlgebra
  haveI : IsScalarTower W K F := .of_algebraMap_eq fun _ => rfl
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := W) (by simpa using hk)
  let f : W →+* F := algebraMap W F
  have hf : Function.Injective f := (algebraMap K F).injective.comp (IsFractionRing.injective W K)
  obtain ⟨O, hO⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨h1, hloc⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff_isLocalHom f O).1 hO
  have h2 := ((GlobalTheory.localSubring_range_le_valuationSubring_iff f O).1 hO).2
  haveI : CharZero K := inferInstance
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : IsAlgClosed F := IsAlgClosure.isAlgClosed K
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (f ϖ) (Nat.pos_of_ne_zero hk0)
  haveI : NeZero (k : F) := ⟨by exact_mod_cast hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0, eq_comm, map_eq_zero_iff f hf] at hπ
    exact hϖ.ne_zero hπ
  have hmin := GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := π) hπ
  have hmin' := GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := ζ * π)
    (by rw [mul_pow, hζ.pow_eq_one, _root_.one_mul]; exact hπ)
  haveI : IsGalois K F := {}
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) F (x := ζ * π) (y := π)).1
    (hmin'.trans hmin.symm)
  change g π = ζ * π at hg

  let S := integralClosure W F
  have hc : SMulCommClass (F ≃ₐ[K] F) W F := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    simp only [AlgEquiv.smul_def, Algebra.smul_def, _root_.map_mul, AlgEquiv.commutes]⟩
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  haveI : ContinuousSMul (F ≃ₐ[K] F) S := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : F)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  let H := MulAction.stabilizer (F ≃ₐ[K] F) π
  have hH : IsClosed (H : Set (F ≃ₐ[K] F)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := K) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let φ : W →+* O := f.codRestrict O h1
  letI : Algebra W O := φ.toAlgebra
  haveI : IsScalarTower W O F := .of_algebraMap_eq fun _ => rfl
  have hSO : ∀ b : F, IsIntegral W b → b ∈ O := by
    intro b hb
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := F)).mp hb.tower_top
    rw [← hy]
    exact y.2
  let incl : S →+* O := (S.val.toRingHom).codRestrict O (fun b => hSO b b.2)
  let Q : Ideal S := (maximalIdeal O).comap incl
  have hQ : ∀ b : S, b ∈ Q ↔ O.valuation (b : F) < 1 := fun b =>
    ValuationSubring.valuation_lt_one_iff O (incl b)
  obtain ⟨a₁, ha₁, a₂, ha₂, hcong⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := W) H Q g
    (fun b hb => by
      rw [hQ]
      refine GlobalTheory.T.automorphism_congr_one_on_adjoin_root_uniformiser W F O h1 h2 ϖ hϖ k hk0 π hπ g b ?_ ((O.valuation_le_one_iff _).mpr (hSO b b.2))
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin K {π}),
        IntermediateField.mem_fixedField_iff]
      intro e he
      exact congrArg Subtype.val (hb e (he ⟨π, IntermediateField.mem_adjoin_simple_self K π⟩)))
  let σ := a₂ * g * a₁
  have hσπ : σ π = a₂ ζ * π := by
    have e1 : a₁ π = π := ha₁
    have e2 : a₂ π = π := ha₂
    simp only [σ, AlgEquiv.mul_apply, e1, hg, map_mul, e2]
  have hσS : ∀ b : F, IsIntegral W b → O.valuation (σ b - b) < 1 := fun b hb =>
    (hQ (σ • ⟨b, hb⟩ - ⟨b, hb⟩)).1 (hcong ⟨b, hb⟩)
  refine ⟨O, φ, σ.toAlgHom, π, hloc, fun w => rfl, fun x hx => ?_, hπ, ?_⟩
  · obtain ⟨s, t, hs, ht, hs1, e⟩ := GlobalTheory.T.exists_integral_quotient_dominating_valuationSubring W F O h1 h2 x hx
    change O.valuation (σ x - x) < 1
    have hs' := hσS s hs
    have ht' := hσS t ht
    have htv : O.valuation t ≤ 1 := (O.valuation_le_one_iff _).mpr (hSO t ht)
    have hσs : O.valuation (σ s) = 1 := by
      have : σ s = s + (σ s - s) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hs1]; exact hs'), hs1]
    have key : s * σ s * (σ x - x) = s * (σ t - t) - t * (σ s - s) := by
      rw [← e, map_mul]; ring
    have hv : O.valuation (s * σ s * (σ x - x)) < 1 := by
      rw [key]
      refine Valuation.map_sub_lt _ ?_ ?_
      · rw [map_mul, hs1, _root_.one_mul]; exact ht'
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' htv) hs'
    rwa [map_mul, map_mul, hs1, hσs, _root_.one_mul, _root_.one_mul] at hv
  · change IsPrimitiveRoot (σ π / π) k
    rw [hσπ, mul_div_cancel_right₀ _ hπ0]
    exact hζ.map_of_injective a₂.injective

end GlobalTheory.InertiaTameRoot
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_moves_tame_root : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] [CharZero W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] [IsAlgClosure (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ k : ℕ, IsUnit (k : W) → ∃ (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F),
      IsLocalHom φ ∧ (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) ∧
      (∀ x ∈ O, O.valuation (σ x - x) < 1) ∧ π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ∧
      IsPrimitiveRoot (σ π / π) k := by
  first | exact @GlobalTheory.InertiaTameRoot.exists_inertia_moves_root | exact GlobalTheory.InertiaTameRoot.exists_inertia_moves_root | (intros; apply GlobalTheory.InertiaTameRoot.exists_inertia_moves_root <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Member.TameDivOrd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
private lemma ord_vw_unit_mul_uniformiser_pow {W : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {ϖ : W} (hϖ : Irreducible ϖ) (h0 : ϖ ≠ 0) (u : Wˣ) (m : ℕ) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun
      (Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u *
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m) = m := by
  induction m with
  | zero =>
    rw [pow_zero, _root_.mul_one, Nat.cast_zero]
    exact (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).map_unit u
  | succ m ih =>
    rw [pow_succ, ← _root_.mul_assoc, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul, ih,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw_uniformiser h0
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
    push_cast
    ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
private lemma eq_one_of_pow_eq_one_of_ne_zero {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ}
    {k : ℕ} (hk : k ≠ 0) (h : a ^ k = 1) : a = 1 := by
  rcases lt_trichotomy a 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le' h1 hk).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hk).ne'

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
private lemma one_le_valuation_root_of_unity_sub_one {F : Type} [Field F] (O : ValuationSubring F) {k : ℕ}
    (hk : IsUnit (k : O)) {w : F} (hw : w ^ k = 1) (hw1 : w ≠ 1) : 1 ≤ O.valuation (w - 1) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have hsum : ∑ i ∈ Finset.range k, w ^ i = 0 := by
    rw [geom_sum_eq hw1, hw, sub_self, zero_div]
  have hkF : (k : F) = (w - 1) * -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j := by
    rw [mul_neg, Finset.mul_sum]
    simp_rw [mul_comm (w - 1), geom_sum_mul]
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have hvw : O.valuation w = 1 :=
    eq_one_of_pow_eq_one_of_ne_zero hk0 (by rw [← map_pow, hw, map_one])
  have hwO : w ∈ O := (O.valuation_le_one_iff w).1 hvw.le
  have hcO : -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j ∈ O :=
    neg_mem (sum_mem fun i _ => sum_mem fun j _ => pow_mem hwO j)
  have hvk : O.valuation (k : F) = 1 := by
    simpa using O.valuation_unit hk.unit
  rw [← hvk, hkF, map_mul]
  exact mul_le_of_le_one_right' ((O.valuation_le_one_iff _).2 hcO)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in

theorem _root_.GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ (k : ℕ) (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F), IsUnit (k : O) →
      IsLocalHom φ → (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ x ∈ O, O.valuation (σ x - x) < 1) → π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) →
      IsPrimitiveRoot (σ π / π) k →
      ∀ (d : F) (z : (FractionRing W)ˣ), σ d = d → O.valuation d ^ k = O.valuation (algebraMap (FractionRing W) F z) →
        (k : ℤ) ∣ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z := by
  intro W _ _ _ F _ _ ϖ hϖ k O φ σ π hk _ hφ hσ hπ hζ d z hd hdz
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have h0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖF : algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).2 h0)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0] at hπ
    exact hϖF hπ.symm
  set ζ := σ π / π with hζdef
  have hσπ : σ π = ζ * π := by rw [hζdef, div_mul_cancel₀ _ hπ0]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective W (z : FractionRing W)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap W (FractionRing W) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : (z : FractionRing W) * algebraMap W _ b = algebraMap W _ a := by
    rw [← hab, div_mul_cancel₀ _ hbF]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at key
    exact z.ne_zero (by simpa [hbF] using key)
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ

  have hU : z * (Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u' *
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m') =
      Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u *
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m := by
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [show ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 : (FractionRing W)ˣ) : FractionRing W) =
      algebraMap W _ ϖ from rfl, ← map_pow, ← map_mul, ← map_pow, ← map_mul, key]
  have hord : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z + m' = m := by
    have := congrArg (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun hU
    rwa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul,
      ord_vw_unit_mul_uniformiser_pow hϖ, ord_vw_unit_mul_uniformiser_pow hϖ] at this

  have hφu : ∀ x : Wˣ, O.valuation (φ x : F) = 1 := fun x => by
    simpa using O.valuation_unit (Units.map (φ : W →* O) x)
  have keyF : algebraMap _ F (z : FractionRing W) * ((φ u' : F) * (φ ϖ : F) ^ m') =
      (φ u : F) * (φ ϖ : F) ^ m := by
    have := congrArg (algebraMap (FractionRing W) F) key
    simpa only [hφ, map_mul, map_pow] using this
  have hP : O.valuation (φ ϖ : F) = O.valuation π ^ k := by rw [hφ, ← hπ, map_pow]
  have hV : O.valuation d ^ k * O.valuation π ^ (k * m') = O.valuation π ^ (k * m) := by
    have := congrArg O.valuation keyF
    simp only [map_mul, map_pow, hφu, _root_.one_mul, hP] at this
    rw [hdz, pow_mul, pow_mul]
    exact this
  have hvπ : O.valuation π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ0
  set y := d * π ^ m' / π ^ m with hydef
  have hvy : O.valuation y = 1 := by
    apply eq_one_of_pow_eq_one_of_ne_zero hk0
    rw [hydef, map_div₀, map_mul, map_pow, map_pow, div_pow, mul_pow, ← pow_mul, ← pow_mul,
      mul_comm m' k, mul_comm m k, hV, div_self (pow_ne_zero _ hvπ)]
  set w := ζ ^ m' / ζ ^ m with hwdef
  have hσy : σ y = w * y := by
    rw [hydef, hwdef, map_div₀, map_mul, map_pow, map_pow, hd, hσπ]
    ring
  have hyO : y ∈ O := (O.valuation_le_one_iff y).1 hvy.le
  have hwk : w ^ k = 1 := by
    rw [hwdef, div_pow, ← pow_mul, ← pow_mul, mul_comm m' k, mul_comm m k, pow_mul, pow_mul,
      hζ.pow_eq_one, one_pow, one_pow, div_one]
  have hw : w = 1 := by
    by_contra hw1
    have h1 := one_le_valuation_root_of_unity_sub_one O hk hwk hw1
    have hlt := hσ y hyO
    rw [hσy, show w * y - y = (w - 1) * y by ring, map_mul, hvy, _root_.mul_one] at hlt
    exact absurd hlt (not_lt.2 h1)
  have hdvd : (k : ℤ) ∣ (m' : ℤ) - m := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hk0), zpow_natCast, zpow_natCast]
    exact hw
  have hn : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z = m - m' := by omega
  rw [hn, ← dvd_neg, neg_sub]
  exact hdvd

end GlobalTheory.Member.TameDivOrd
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameInertia_fixed_dvd_valuation_order : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ (k : ℕ) (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F), IsUnit (k : O) →
      IsLocalHom φ → (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ x ∈ O, O.valuation (σ x - x) < 1) → π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) →
      IsPrimitiveRoot (σ π / π) k →
      ∀ (d : F) (z : (FractionRing W)ˣ), σ d = d → O.valuation d ^ k = O.valuation (algebraMap (FractionRing W) F z) →
        (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z := by
  first | exact @GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord | exact GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord | (intros; apply GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_tauCoordinate_add_nsmul_first_variable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.TauBimult →
    ∀ (a z b : D.X) (k : ℕ) (x x' x'' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x →
      GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D z b x' → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (a + k • z) b x'' →
      ∃ u : Rˣ, x'' = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (x * x' ^ k) := by
  first | exact @GlobalTheory.TauShift.main | exact GlobalTheory.TauShift.main | (intros; apply GlobalTheory.TauShift.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InertiaFix

open GlobalTheory.TorusExt GlobalTheory.UnramTorsion ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] gtGroup

theorem sigma_fixes_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ), IsUnit (k : O) → ∀ (σ : F →ₐ[FractionRing R] F), (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    ∀ p : QkPt D F k, spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left := by
  intro R _ _ D hB F _ _ O φ hφ k hk σ hσ p
  have memO : ∀ x : O, σ (x : F) ∈ O := fun x => by
    have h1 : σ (x : F) - x ∈ O := (O.valuation_le_one_iff _).1 (hσ x x.2).le
    have := O.add_mem _ _ h1 x.2
    simpa using this
  let σO : O →+* O := (σ.toRingHom.comp O.subtype).codRestrict O.toSubring memO
  have hσO : ∀ x : O, ((σO x : O) : F) = σ x := fun _ => rfl
  have hσφ : σO.comp φ = φ := RingHom.ext fun r => Subtype.ext (by
    show σ ((φ r : O) : F) = (φ r : F)
    rw [hφ]; exact σ.commutes _)
  have hres : (IsLocalRing.residue O).comp σO = IsLocalRing.residue O := RingHom.ext fun x => by
    show IsLocalRing.residue O (σO x) = IsLocalRing.residue O x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply (ValuationSubring.valuation_lt_one_iff O _).2
    have : ((σO x - x : O) : F) = σ (x : F) - x := by push_cast; rfl
    rw [this]; exact hσ x x.2
  have hsub : σ.toRingHom.comp O.subtype = O.subtype.comp σO := rfl
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ) := Over.homMk (spMap O.subtype) (by
    show spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  obtain ⟨b', hb'⟩ := exists_extend O φ ρ rfl p.g.b
  let σ' : Over.mk (spMap φ) ⟶ Over.mk (spMap φ) := Over.homMk (spMap σO) (by
    show spMap σO ≫ spMap φ = spMap φ
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσφ])
  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  haveI := D.P.isAb.comm
  have hd : IsDominant (spMap O.subtype) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical O.subtype).2
      (by rw [(RingHom.injective_iff_ker_eq_bot O.subtype).1 Subtype.val_injective]; exact bot_le)
  have hpk : p.g.b ^ k = cP D _ p.y := by
    rw [← nsmul_b, qk_nsmul hB, iota_b]
  have hpow : b' ^ k = cP D _ p.y := by
    have e : ρ ≫ b' ^ k = ρ ≫ cP D _ p.y := by
      rw [comp_cP, ← hpk, ← hb']; exact map_pow (preHom ρ) _ _
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk (spMap φ)).left := (inferInstance : IsReduced (Sp O))
    exact ext_of_isDominant (spMap O.subtype) (congrArg CommaMorphism.left e)
  have hpow' : b' ^ k = (σ' ≫ b') ^ k := by
    have e2 : σ' ≫ b' ^ k = (σ' ≫ b') ^ k := map_pow (preHom σ') b' k
    rw [← e2, hpow, comp_cP]
  have hcl : spMap (IsLocalRing.residue O) ≫ b'.left = spMap (IsLocalRing.residue O) ≫ (σ' ≫ b').left := by
    rw [Over.comp_left, ← Category.assoc]
    congr 1
    show _ = spMap (IsLocalRing.residue O) ≫ spMap σO
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hres]
  have heq : b' = σ' ≫ b' := GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) D.P.A D.P.isAb.smooth O (spMap φ) k hk b' (σ' ≫ b') hpow'
    (IsLocalRing.ResidueField O) (IsLocalRing.residue O) inferInstance hcl
  rw [← hb', Over.comp_left]
  show spMap σ.toRingHom ≫ spMap O.subtype ≫ b'.left = spMap O.subtype ≫ b'.left
  conv_rhs => rw [heq]
  rw [← Category.assoc, Over.comp_left, ← Category.assoc]
  congr 1
  show spMap σ.toRingHom ≫ spMap O.subtype = spMap O.subtype ≫ spMap σO
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.InertiaFix
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixes_abelianPart_of_torsionPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ), IsUnit (k : O) → ∀ (σ : F →ₐ[FractionRing R] F), (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    ∀ p : QkPt D F k, spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left := by
  first | exact @GlobalTheory.InertiaFix.sigma_fixes_abelianPart | exact GlobalTheory.InertiaFix.sigma_fixes_abelianPart | (intros; apply GlobalTheory.InertiaFix.sigma_fixes_abelianPart <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory

theorem restrict_torus_smul_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (a : 𝓞 E) (x : P.D.toPre.X), ρ (a • x) = a • ρ x := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ
    hα hj _ h₀j
  letI := H.starRing
  have key : ∀ a : 𝓞 E, j ≫ tV.act.act a =
      SplitTorus.torusMap _ (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a)) ≫ j := by
    intro a
    have : IsSchemeTheoreticallyDominant (spMap α) :=
      ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hα
    have : IsSeparated tV.G.hom := tV.semi.separated
    have : Flat (splitTorusAff ZU P'.D.toPre.X).hom :=
      (ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
    have : Flat (splitTorus (Sp V) P'.D.toPre.X).hom := inferInstanceAs (Flat (pullback.snd _ _))
    refine ExtUnique.over_hom_ext_of_isPullback (SplitTorus.isPullback_bcMap (spMap α) _) ?_
    have e1 := TorusPart.pullTorus_comp n.cart n.cart (tV.act.act a) (tΩ.act.act a) (n.act a) j
    have e2 := TorusPart.pullTorus_torusMap_comp n.cart j
      (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a))
    have e3 := TorusPart.PELUnif.torus_comp_act P' hβ n' a
    rw [hj, e3] at e1
    rw [hj] at e2
    rw [← TorusPart.pullTorus_left n.cart, ← TorusPart.pullTorus_left n.cart, e1, e2]
  have hmono := (GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P (ResidueField V) ((residue V).comp ψ) 0
    (TorusPart.map_pow_one_eq_zero h₀) t₀.G m₀'.φ m₀'.cart).1
  have key2 : ∀ a : 𝓞 E, ρ.comp (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) =
      (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a)).comp ρ := by
    intro a
    have e := congrArg (TorusPart.pullTorus m₀.cart) (key a)
    rw [TorusPart.pullTorus_comp m₀.cart m₀.cart (tV.act.act a) (t₀.act.act a) (m₀.act a) j,
      TorusPart.pullTorus_torusMap_comp m₀.cart j, h₀j, Category.assoc,
      TorusPart.PELUnif.torus_comp_act P h₀ m₀' a, ← Category.assoc, ← Category.assoc,
      ← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_comp] at e
    haveI : Mono (TorusPart.PELUnif.torus P h₀ m₀') := hmono
    have : Nonempty (Sp (ResidueField V)) := inferInstance
    exact SplitTorus.torusMap_injective ((cancel_mono _).1 e)
  intro a x
  have k := DFunLike.congr_fun (key2 (H.bar a)) x
  rw [show H.bar (H.bar a) = a from star_star a] at k
  exact k

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCharacterRestriction_commutes_ringAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (a : 𝓞 E) (x : P.D.toPre.X), ρ (a • x) = a • ρ x := by
  atlas_forward_decl GlobalTheory.restrict_torus_smul_comm
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCharacterRestriction_trait_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    Function.Surjective ρ := by
  first | exact @GlobalTheory.TorusOnto.restrict_surjective | exact GlobalTheory.TorusOnto.restrict_surjective | (intros; apply GlobalTheory.TorusOnto.restrict_surjective <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsion_uniformisation_eq_restrictCharacters : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') [CharZero R] [CharZero W], AdmBase R (maximalIdeal R) → AdmBase W (maximalIdeal W) →
    ∀ (g : R →+* W) (m : SABMap t' t (spMap g))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    α.comp ψ = β.comp g → n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F]
      (O : ValuationSubring F) (φ : W →+* O), IsLocalHom φ →
      (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing W) F (algebraMap W (FractionRing W) (g r))) →
    ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative P.D.toPre.X →* Fˣ) (τ' : Multiplicative P'.D.toPre.X →* Fˣ)
      (q : QkPt P.D.toPre F k) (q' : QkPt P'.D.toPre F k) (v : Sp F ⟶ t.G.left) (v' : Sp F ⟶ t'.G.left),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) →
      q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g →
      GlobalTheory.FlatTors.IsImage P F k q v → GlobalTheory.FlatTors.IsImage P' F k q' v' → v = v' ≫ m.φ := by
  first | exact @GlobalTheory.ToricTorsionCompare.toric_torsion_eq_restrict | exact GlobalTheory.ToricTorsionCompare.toric_torsion_eq_restrict | (intros; apply GlobalTheory.ToricTorsionCompare.toric_torsion_eq_restrict <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TauForm

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

theorem exists_eq_add_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {F : Type} [Field F]
    {k : ℕ} {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ k) {u v : X}
    (h : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd u) = τ (Multiplicative.ofAdd v)) :
    ∃ z : X, v = u + k • z := by
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, ∃ c : ℤ, b.repr (v - u) i = k * c := fun i => by
    let τ : Multiplicative X →* Fˣ := (zpowersHom Fˣ ζ).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
    have e : ζ ^ (b.repr u i) = ζ ^ (b.repr v i) := h τ (MonoidHom.ext fun x => by
      show (ζ ^ (b.coord i x.toAdd)) ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow])
    refine (hζ.zpow_eq_one_iff_dvd _).1 ?_
    rw [map_sub, Finsupp.sub_apply, zpow_sub, e, mul_inv_cancel]
  choose c hc using key
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (v - u), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul, natCast_zsmul]

section Ord

variable {W : Type} [CommRing W] [IsDomain W] {Γ : Type} [AddCommGroup Γ] (v : LatticeVal W Γ)

theorem val_one : v.toFun 1 = 0 := by
  have := v.map_mul 1 1
  rw [_root_.mul_one] at this
  exact left_eq_add.1 this

theorem val_pow (x : (FractionRing W)ˣ) (k : ℕ) : v.toFun (x ^ k) = k • v.toFun x := by
  induction k with
  | zero => rw [pow_zero, val_one, zero_nsmul]
  | succ k ih => rw [pow_succ, v.map_mul, ih, succ_nsmul]

theorem val_div (x y : (FractionRing W)ˣ) : v.toFun (x / y) = v.toFun x - v.toFun y := by
  rw [eq_sub_iff_add_eq, ← v.map_mul, div_mul_cancel]

theorem exists_unit_of_ord_eq [IsDiscreteValuationRing W] {x y : (FractionRing W)ˣ}
    (h : (ord_vw W).toFun x = (ord_vw W).toFun y) :
    ∃ u : Wˣ, (x : FractionRing W) = algebraMap W (FractionRing W) (u : W) * (y : FractionRing W) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ (x / y).ne_zero
  have h1 := ord_vw_uniformiser hϖ.ne_zero hϖ.maximalIdeal_eq
  have e : x / y = Units.map (algebraMap W (FractionRing W)).toMonoidHom u * toUnitK ϖ hϖ.ne_zero ^ n :=
    Units.ext (by rw [hu, Units.smul_def, Algebra.smul_def, Units.val_mul, Units.val_zpow_eq_zpow_val]; rfl)
  have hz : (ord_vw W).toFun (toUnitK ϖ hϖ.ne_zero ^ n) = n := by
    obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
    · rw [zpow_natCast, val_pow, h1]; simp
    · rw [zpow_neg, zpow_natCast, ← one_div, val_div, val_one, val_pow, h1]; simp
  have h0 : n = 0 := by
    have := congrArg (ord_vw W).toFun e
    rw [val_div, h, sub_self, (ord_vw W).map_mul, (ord_vw W).map_unit, hz, zero_add] at this
    exact this.symm
  rw [h0, zpow_zero, _root_.mul_one, div_eq_iff_eq_mul] at e
  exact ⟨u, congrArg Units.val e⟩

end Ord

theorem cubWeil_push {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t : SAB H S}
    {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : ℕ} (T : Over S') (s : T.left ⟶ S) (hs : s = T.hom ≫ f)
    {x y : T ⟶ t'.G} {x₁ y₁ : Over.mk s ⟶ t.G} (hx : x₁.left = x.left ≫ m.φ) (hy : y₁.left = y.left ≫ m.φ)
    {z : Γ(T.left, ⊤)ˣ} (h : GlobalTheory.UU.CubWeil t'.cub k x y z) : GlobalTheory.UU.CubWeil t.cub k x₁ y₁ z := by
  subst hs
  obtain rfl : x₁ = toBase m.cart.1.w x := Over.OverMorphism.ext hx
  obtain rfl : y₁ = toBase m.cart.1.w y := Over.OverMorphism.ext hy
  exact GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f t.G t'.G m.cm m.cart.1.w
    (fun T a b => Over.OverMorphism.ext (m.cart.2 T a b _ _ rfl rfl).symm) _ _ _ _ m.lin k T x y z h

theorem dvd_ord_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [CharZero R] {t : SAB H (Sp R)} (P : PELUnif (maximalIdeal R) t) (hR : AdmBase R (maximalIdeal R))
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W] {t' : SAB H (Sp W)}
    (P' : PELUnif (maximalIdeal W) t') (hW : AdmBase W (maximalIdeal W)) {g : R →+* W} (m : SABMap t' t (spMap g))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X) (gK : FractionRing R →+* FractionRing W)
    (hgK : ∀ r, gK (algebraMap R _ r) = algebraMap W _ (g r))
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F]
    (hF : ∀ x, algebraMap (FractionRing R) F x = algebraMap (FractionRing W) F (gK x))
    {k : ℕ} (hk : IsUnit (k : R)) {ϖ : W} (hϖ : Irreducible ϖ) (O : ValuationSubring F) (φ : W →+* O)
    (σ : F →ₐ[FractionRing W] F) (π : F) (hφ : IsLocalHom φ)
    (eφ : ∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w))
    (hσ : ∀ x ∈ O, O.valuation (σ x - x) < 1)
    (hπ : π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ)) (hζ : IsPrimitiveRoot (σ π / π) k)
    (hT : ∀ (τ : Multiplicative P.D.toPre.X →* Fˣ) (τ' : Multiplicative P'.D.toPre.X →* Fˣ)
      (q : QkPt P.D.toPre F k) (q' : QkPt P'.D.toPre F k) (v : Sp F ⟶ t.G.left) (v' : Sp F ⟶ t'.G.left),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) →
      q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g →
      GlobalTheory.FlatTors.IsImage P F k q v → GlobalTheory.FlatTors.IsImage P' F k q' v' → v = v' ≫ m.φ)
    {a b : P.D.toPre.X} {x : (FractionRing R)ˣ} {x' : (FractionRing W)ˣ} (hx : IsTauCoord P.D.toPre a b x)
    (hx' : IsTauCoord P'.D.toPre (ρ a) (ρ b) x') :
    (k : ℤ) ∣ (ord_vw W).toFun (Units.map gK.toMonoidHom x) - (ord_vw W).toFun x' := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hB := P.D.tau_bimult
  have hB' := P'.D.tau_bimult
  obtain ⟨f, i₁, p₁, s₁, a₁, w₁, c₁⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H R t P hR F k hk1
  obtain ⟨f', i₂, p₂, s₂, a₂, w₂, c₂⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H W t' P' hW F k hk1
  have hs : jFK (R := R) F ≫ jK R = (TF (R := W) F).hom ≫ spMap g := by
    show spMap _ ≫ spMap _ = (spMap _ ≫ spMap _) ≫ spMap g
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun r => (hF _).trans (congrArg _ (hgK r))))
  obtain ⟨e, he⟩ : ∃ e : (TF (R := W) F ⟶ t'.G) ≃* (TF (R := R) F ⟶ t.G), ∀ u, (e u).left = u.left ≫ m.φ :=
    GlobalTheory.LiePull.exists_pushEquiv m.cart (TF (R := W) F) _ hs

  have tor : ∀ (τ' : Multiplicative P'.D.toPre.X →* Fˣ) (q' : QkPt P'.D.toPre F k), τ' ^ k = 1 → q'.y = 0 →
      GlobalTheory.UT.IsTor τ' q'.g → ∀ p : QkPt P.D.toPre F k,
      GlobalTheory.UU.CubWeil t.cub k (e (f' q')) (f p) (unitOn (τ' (Multiplicative.ofAdd (ρ p.y)))) := by
    intro τ' q' h₁ h₂ h₃ p
    obtain ⟨q, h₄, h₅⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (τ'.comp (AddMonoidHom.toMultiplicative ρ))
      (MonoidHom.ext fun χ => DFunLike.congr_fun h₁ _)
    have : f q = e (f' q') := Over.OverMorphism.ext
      ((hT _ τ' q q' _ _ h₁ (fun _ => rfl) h₄ h₅ h₂ h₃ ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)).trans (he _).symm)
    exact this ▸ w₁ q p _ h₄ h₅
  obtain ⟨p, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 a
  obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
  obtain ⟨p', hp'⟩ := s₂ (e.symm (f p)) (by rw [← map_pow, p₁, map_one])
  have hp : f p = e (f' p') := by rw [hp', e.apply_symm_apply]
  have π0 : π ≠ 0 := fun h => by
    rw [h, zero_pow hk0, eq_comm, map_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective W _)] at hπ
    exact hϖ.ne_zero hπ
  obtain ⟨z, hz⟩ : ∃ z, p'.y = ρ p.y + k • z := by
    refine exists_eq_add_nsmul (ζ := (hζ.isUnit hk0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ) fun τ' h₁ => ?_
    obtain ⟨q', h₂, h₃⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB' (k := k) τ' h₁
    exact GlobalTheory.ZH.TorusPerp.unitOn_injective ((tor τ' q' h₁ h₂ h₃ p).unique
      (cubWeil_push m (TF (R := W) F) _ hs (he _) (by rw [hp, he]) (w₂ q' p' τ' h₂ h₃)))

  let σR : F →ₐ[FractionRing R] F := { σ.toRingHom with commutes' := fun y => by rw [hF]; exact σ.commutes _ }
  have eφR : ∀ r, ((φ.comp g) r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) := fun r => by
    rw [hF, hgK]; exact eφ _
  obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σR.toRingHom (RingHom.ext σR.commutes) p
  obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
  obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.T.conj_eq_add_kummer_torusTorsionPoint R _ hB F O (φ.comp g) eφR k σR p r hr
    (GlobalTheory.T.inertia_fixes_abelianPart_of_torsionPoint R _ hB F O (φ.comp g) eφR k hkO σR hσ p)
  obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.T.conj_eq_add_kummer_torusTorsionPoint W _ hB' F O φ eφ k σ p' r' hr'
    (GlobalTheory.T.inertia_fixes_abelianPart_of_torsionPoint W _ hB' F O φ eφ k hkO σ hσ p')
  have hq : f q₁ = e (f' q₂) := by
    have h₁ : f r = e (f' r') := Over.OverMorphism.ext (by
      rw [c₁ σR p r hr, he, c₂ σ p' r' hr', hp, he, Category.assoc])
    rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, ← hp] at h₁
    exact mul_left_cancel h₁
  have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) :=
    GlobalTheory.ZH.TorusPerp.unitOn_injective ((w₁ q₁ pb τ₁ y₁ t₁).unique (hq ▸ tor τ₂ q₂ k₂ y₂ t₂ pb))
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord W P'.D.toPre p'.y (ρ pb.y)
  obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord W P'.D.toPre z (ρ pb.y)
  obtain ⟨s, s0, sv, sσ⟩ := v₁ _ x hx
  obtain ⟨s', s0', sv', sσ'⟩ := v₂ _ x'' hx''
  have sσ : σ s = _ := sσ
  have dv := GlobalTheory.T.tameInertia_fixed_dvd_valuation_order W F ϖ hϖ k O φ σ π hkO hφ eφ hσ hπ hζ (s / s') (Units.map gK.toMonoidHom x / x'')
    (by rw [map_div₀, sσ, sσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
    (by rw [map_div₀, div_pow, sv, sv', Units.val_div_eq_div_val, map_div₀, map_div₀, hF]; rfl)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_tauCoordinate_add_nsmul_first_variable W _ hB' _ z _ k x' xz x'' hx' hxz (hz ▸ hx'')
  rw [val_div, hu, (ord_vw W).map_mul, (ord_vw W).map_unit, (ord_vw W).map_mul, val_pow, zero_add, nsmul_eq_mul,
    ← sub_sub] at dv
  exact (dvd_sub_left (dvd_mul_right _ _)).1 dv

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), GlobalTheory.TorRef.IsCN R → P.TorsionIso →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.UU.CDVR W → ∀ (g : R →+* W) (hg : Function.Injective g), ¬ IsLocalHom g →
    ∀ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap g)) (P' : PELUnif (maximalIdeal W) t'),
      ∃ ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X, Function.Surjective ρ ∧
        ∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W) := by
  intro E _ _ _ H R _ _ _ t P hR _ W _ _ _ hW g hg hnl t' m P'
  obtain ⟨hn, hi, hc, hz⟩ := hR
  obtain ⟨hd, hc', hz'⟩ := hW
  have hR : AdmBase R (maximalIdeal R) := ⟨hn, inferInstance, hi, hc⟩
  have hW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hc'⟩
  have sc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (u : A →+* B) (v : B →+* C),
      spMap v ≫ spMap u = spMap (v.comp u) := fun u v => (Spec.map_comp _ _).symm
  have pull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (u : SAB H S), ∃ u' : SAB H S', Nonempty (SABMap u' u f) := fun f u => by
    obtain ⟨_, _, _, _, _, n, -⟩ := sabPull proved_CubePullSt f u
    exact ⟨_, ⟨n⟩⟩
  have comp : ∀ {S S' S'' : Scheme.{0}} {u : SAB H S} {u' : SAB H S'} {u'' : SAB H S''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
      {f'' : S'' ⟶ S} (n : SABMap u' u f) (n' : SABMap u'' u' f'), f' ≫ f = f'' →
      ∃ n'' : SABMap u'' u f'', n''.φ = n'.φ ≫ n.φ := by
    rintro _ _ _ _ _ _ _ _ _ n n' rfl
    exact GlobalTheory.ObjMaps.exists_sab_comp n n'
  have cancel : ∀ {S S' S'' : Scheme.{0}} {u : SAB H S} {u' : SAB H S'} {u'' : SAB H S''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
      {f'' : S'' ⟶ S} (n : SABMap u' u f) (n'' : SABMap u'' u f''), f' ≫ f = f'' →
      ∃ n' : SABMap u'' u' f', n''.φ = n'.φ ≫ n.φ := by
    rintro _ _ _ _ _ _ _ _ _ n n' rfl
    exact GlobalTheory.ObjMaps.exists_sab_cancel n n'
  obtain ⟨V, _, _, _, ψ, Ω, _, α, β, hψ, hβ, eα, hT⟩ := GlobalTheory.T.exists_trait_nonlocal_torusExtension' R t.G t.semi W g hnl
  obtain ⟨tV, ⟨mV⟩⟩ := pull (spMap ψ) t
  obtain ⟨_, _, _, _, _, mL, -⟩ := sabPull proved_CubePullSt (spMap ((algebraMap V (FractionRing V)).comp ψ)) t
  obtain ⟨mL', -⟩ := cancel mV mL (sc ψ (algebraMap V (FractionRing V)))
  obtain ⟨tΩ, ⟨n'⟩⟩ := pull (spMap β) t'
  obtain ⟨n'', en⟩ := comp m n' ((sc g β).trans (congrArg spMap eα.symm))
  obtain ⟨n, en'⟩ := cancel mV n'' (sc ψ (α.comp (algebraMap V (FractionRing V))))
  obtain ⟨j, hj, ej⟩ := GlobalTheory.T.extend_splitTorus_hom_over_dvr V tV.G tV.semi _ _ mL'.cart hT Ω α tΩ.G n.φ n.cart _
    (GlobalTheory.TorusPart.PELUnif.torus P' hβ n') inferInstance
  obtain ⟨t₀, ⟨m₀⟩⟩ := pull (spMap (residue V)) tV
  obtain ⟨m₀', e₀⟩ := comp mV m₀ (sc ψ (residue V))
  have h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0 := GlobalTheory.TorusPart.map_eq_zero_of_isLocalHom _
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.T.uniformisationTorus_mono_and_factor E H R _ t P (ResidueField V) _ 0 (GlobalTheory.TorusPart.map_pow_one_eq_zero h₀) t₀.G _
    m₀'.cart).2 _ (GlobalTheory.TorusPart.pullTorus m₀.cart j) inferInstance
  have hα : Function.Injective (α.comp (algebraMap V (FractionRing V))) :=
    α.injective.comp (IsFractionRing.injective V _)
  refine ⟨{ ρ with map_smul' := GlobalTheory.T.torusCharacterRestriction_commutes_ringAction E H R t P W t' P' V ψ tV mV Ω _ β hβ tΩ n n' j t₀ m₀ h₀ m₀' ρ hα ej e₀ hρ },
    GlobalTheory.T.torusCharacterRestriction_trait_surjective E H R t P W t' P' V ψ tV mV Ω _ β hβ tΩ n n' j t₀ m₀ h₀ m₀' ρ hα ej e₀ hρ, fun a b x x' hx hx' => ?_⟩
  let gK : FractionRing R →+* FractionRing W := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap W _ (g r) := IsFractionRing.lift_algebraMap _
  refine exists_unit_of_ord_eq (x := Units.map gK.toMonoidHom x) ?_
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  let F := AlgebraicClosure (FractionRing W)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing W) F).comp gK).toAlgebra
  have key : ∀ k : ℕ, IsUnit (k : R) →
      (k : ℤ) ∣ (ord_vw W).toFun (Units.map gK.toMonoidHom x) - (ord_vw W).toFun x' := fun k hk => by
    obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_inertia_moves_tame_root W F ϖ hϖ k (by simpa using hk.map g)
    exact dvd_ord_sub P hR P' hW m ρ gK hgK (fun _ => rfl) hk hϖ O φ σ π h₁ h₂ h₃ h₄ h₅
      (GlobalTheory.T.toricTorsion_uniformisation_eq_restrictCharacters E H R t P W t' P' hR hW g m V ψ tV mV Ω _ β hβ tΩ n n' j t₀ m₀ h₀ m₀' ρ hα ej e₀ hρ eα
        (en'.symm.trans en) F O φ h₁ h₂ (fun r => congrArg (algebraMap (FractionRing W) F) (hgK r)) k hk) hx hx'
  rw [← sub_eq_zero]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
    ((ord_vw W).toFun (Units.map gK.toMonoidHom x) - (ord_vw W).toFun x')) (by simpa using hl.pow _)) ?_
  rw [Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

end GlobalTheory.TauForm
end
