import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.Test

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Scheme.{0}}

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_epsMul_one (R : Type) [CommRing R] : spMap (epsMul (1 : R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [epsMul]

theorem latDR_subset_latHT {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (t : SAB H X) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X) : latDR t x ⊆ latHT t p x := by
  rintro v ⟨xO, hx, vO, hv, e⟩
  refine ⟨xO, hx, 0, vO, hv, by rw [pow_zero, sp_epsMul_one, Category.id_comp, e], fun n c g _ => ?_⟩
  simp

abbrev torus (X : Scheme.{0}) : SAB H X :=
  GlobalTheory.Models.Inhab.trivTriple H (splitTorus X (𝓞 E)) (GlobalTheory.Diag.isSemiAbelian _ _) (GlobalTheory.Diag.diagAct _ _ _)

def charUnit {A : Type} [CommRing A] {g : Sp A ⟶ X} (w : Over.mk g ⟶ splitTorus X (𝓞 E)) (a : 𝓞 E) : Aˣ :=
  ⟨GlobalTheory.Diag.charVal w a, GlobalTheory.Diag.charVal w (-a), by rw [← GlobalTheory.Diag.charVal_add, add_neg_cancel, GlobalTheory.Diag.charVal_zero],
    by rw [← GlobalTheory.Diag.charVal_add, neg_add_cancel, GlobalTheory.Diag.charVal_zero]⟩

def torusChar {O : Type} [CommRing O] (x : Sp O ⟶ X) (q : ℕ) (a : 𝓞 E) : TorsChar (torus H X) x q where
  χ _ _ _ _ g := charUnit g a
  mul _ _ _ _ g g' _ _ := Units.ext (GlobalTheory.Diag.charVal_mul g g' a)
  nat B B' _ _ _ _ _ _ φ g g' _ h :=
    (GlobalTheory.Diag.left_eq_iff φ.toRingHom (by rw [← Category.assoc, sp_comp]; congr 2; exact φ.comp_algebraMap.symm) g' g).1 h a


theorem dual_base {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) = spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [sp_comp, sp_comp]
  congr 1
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]


end Lat

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_flagPt {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (Ω : Type) [Field Ω]
    (y : Sp Ω ⟶ gen Z) : ∃ z : FlagPt Z Ω, z.y = y := by
  have h : y ≫ genStr Z = spMap (Spec.preimage (y ≫ genStr Z)).hom := (Spec.map_preimage _).symm
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z Ω _ y h
  exact ⟨⟨_, y, h, f.v, f.tan, f.eig, f.basis⟩, rfl⟩

instance intO_valRing (C : Type) [NormedField C] [IsUltrametricDist C] : ValuationRing (intO C) := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  by_cases h : ‖(a : C)‖ ≤ ‖(b : C)‖
  · by_cases hb : (b : C) = 0
    · refine ⟨1, Or.inr (Subtype.ext ?_)⟩
      rw [hb, norm_zero, norm_le_zero_iff] at h
      simp [h, hb]
    · refine ⟨⟨a / b, show ‖(a / b : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩,
        Or.inr (Subtype.ext ?_)⟩
      simp [mul_div_cancel₀ _ hb]
  · have ha : (a : C) ≠ 0 := fun h0 => h (by simp [h0])
    refine ⟨⟨b / a, show ‖(b / a : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ (le_of_not_ge h) (norm_nonneg _)⟩,
      Or.inl (Subtype.ext ?_)⟩
    simp [mul_div_cancel₀ _ ha]

instance intO_frac (C : Type) [NormedField C] [IsUltrametricDist C] : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖z‖ ≤ 1
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · exact ⟨1, ⟨z⁻¹, show ‖z⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_not_ge h)⟩,
      by rw [map_one, one_div]; exact (inv_inv z).symm⟩

theorem latDR_nonempty (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] (x : Sp C ⟶ Z.X) : (latDR Z.t x).Nonempty := by
  have := isProper_toroidalModel_structureMap Z
  let φ : 𝓞 c.F →+* C := (Spec.preimage (x ≫ Z.s)).hom
  have hφ : ∀ a, φ a ∈ intO C := fun a => by
    have h1 : IsIntegral (intO C) (φ a) := (RingOfIntegers.isIntegral a).map_of_comp_eq (Int.castRingHom _) φ
      (RingHom.ext_int _ _)
    classical
    let _ : GCDMonoid (intO C) := IsBezout.toGCDDomain _
    have : IsIntegrallyClosed (intO C) := GCDMonoid.toIsIntegrallyClosed
    obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := intO C) (K := C)).1 h1
    exact hb ▸ b.2
  have hv : ValuativeCriterion.Existence Z.s := by
    have h := (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Z.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) Z.s)
    exact h.1
  let S : ValuativeCommSq Z.s :=
    { R := intO C, K := C, i₁ := x, i₂ := spMap (φ.codRestrict _ hφ)
      commSq := ⟨by
        rw [← Spec.map_preimage (x ≫ Z.s)]
        exact Spec.map_comp (CommRingCat.ofHom (φ.codRestrict _ hφ)) (CommRingCat.ofHom (intO C).subtype)⟩ }
  obtain ⟨⟨xO, h1, -⟩⟩ := (hv S).exists_lift
  let p : tEpsG xO ⟶ Over.mk xO := Over.homMk (spMap (algebraMap _ (DualNumber _))) rfl
  refine ⟨_, xO, h1, (1 : tEpsG xO ⟶ Z.t.G).left, ⟨Over.w _, ?_⟩, rfl⟩
  rw [← MonObj.comp_one p, Over.comp_left, ← Category.assoc]
  change (_ ≫ spMap _) ≫ _ = _
  rw [GlobalTheory.Diag.fstHom_base, Category.id_comp]

end Pts

theorem polar_sq (a b : ℝ) : polar (fun x : ℝ => x ^ 2) {a, b} = a * b := by
  have h : ({a, b} : Multiset ℝ) = a ::ₘ b ::ₘ 0 := rfl
  simp only [h, polar, Multiset.powerset_cons, Multiset.powerset_zero]
  simp
  ring


def arReal (Tau : Type) (N g : ℕ) : ArIn Tau N g Unit where
  A _ := ℝ
  num _ M := M.prod
  root a R _ _ := if a 2 then R else 1
  whole _ _ _ _ := 1



section Stages

variable {D : D7} {N j : ℕ} {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (P : PadPkg D N j Comp jC ng)

def locOf : LocSt D N j ng := ⟨P.loc, P.ex, P.locB, P.pbKF⟩

def globOf : GlobSt fun p => (P.loc p).Mdl :=
  ⟨P.Xg, P.bc, P.DivG, P.effD, P.noVertD, P.posBdD, P.ampleOnAbelianBase, P.Met, P.nefFibM, P.ampleGen, P.limRA⟩

open PadPkg in

def admissibleStageOfPackage : AdmSt D N j jC :=
  ⟨fun p _ la => P.Mp p la, fun p _ la z => md P p la z, fun p _ la z => P.CurveM p la z,
    fun p _ la z => P.degM p la z, fun p _ la => P.htMdl p la⟩

end Stages


section Sign

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem grNorm_le_of_smul {X : Scheme.{0}} {t : SAB H X} {C : Type} [NontriviallyNormedField C] {x : Sp C ⟶ X}
    {Λ Λ' : Set (Sp (DualNumber C) ⟶ t.G.left)} {m : ℕ} {u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    (hu : ∀ k, IsTanAtG t x (u k)) {a : C} (ha : a ≠ 0) (h : ∀ w ∈ Λ, spMap (epsMul a) ≫ w ∈ Λ') (i : Fin m)
    (hne : (Guard.grSet t x Λ u i).Nonempty) : ‖a‖ * grNorm t x Λ' u i ≤ grNorm t x Λ u i := by
  refine le_csInf hne ?_
  rintro _ ⟨cf, h0, h1, ⟨w, hw, hc⟩, rfl⟩
  have hb : BddBelow (Guard.grSet t x Λ' u i) := ⟨0, by rintro _ ⟨cf, -, -, -, rfl⟩; positivity⟩
  have := csInf_le hb ⟨fun k => a * cf k, mul_ne_zero ha h0, fun k hk => by simp [h1 k hk],
    ⟨_, h w hw, Guard.comb_smul hu hc a⟩, rfl⟩
  have hp : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [Guard.grNorm_eq]
  refine (mul_le_mul_of_nonneg_left this hp.le).trans_eq ?_
  rw [norm_mul]
  field_simp

theorem lnLie_sub (hB : HTBoundSt) {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {Ω : Type} [Field Ω] (y : FlagPt Z Ω)
    (p : ℕ) [hp : Fact p.Prime] (io : Ω →+* ℂ_[p]) (τ : E →+* ℂ) (k : ℕ) :
    0 ≤ y.lnLie io p false τ k - y.lnLie io p true τ k ∧
      y.lnLie io p false τ k - y.lnLie io p true τ k ≤ 1 / ((p : ℝ) - 1) * Real.log p := by
  have h1 : (1 : ℝ) < p := Nat.one_lt_cast.2 hp.out.one_lt
  have hlog : 0 < Real.log p := Real.log_pos h1
  by_cases hk : k < Dw.mult τ
  swap
  · simp only [FlagPt.lnLie, dif_neg hk, sub_self]
    exact ⟨le_rfl, mul_nonneg (by rw [one_div, inv_nonneg]; linarith) hlog.le⟩
  simp only [FlagPt.lnLie, dif_pos hk]
  have hu := fun k => GlobalTheory.FactorDepth.isTanAtG_map _ io (y.tan τ k)
  have hi := (Guard.indep_u y τ).map io (y.tan τ)
  obtain ⟨n1, p1⟩ := Guard.grNorm_latDR_pos Z _ hu hi ⟨k, hk⟩
  obtain ⟨n2, p2⟩ := Guard.grNorm_latHT_pos Z hB p _ hu hi ⟨k, hk⟩
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by simpa using PadicComplex.norm_extends' p (p : ℚ_[p])
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) hp1
  have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hp1.ne'] at ha
    exact hp.out.ne_zero (Nat.cast_eq_zero.1 ha.symm)
  have hla : Real.log ‖a‖ = -(1 / ((p : ℝ) - 1)) * Real.log p := by
    have : ((p : ℝ) - 1) * Real.log ‖a‖ = - Real.log p := by
      rw [← hc, ← Real.log_pow, ← norm_pow, ha, hn, Real.log_inv]
    have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    linarith
  have hna : ‖a‖ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    rw [Real.rpow_def_of_pos (by linarith), mul_comm, ← hla, Real.exp_log (norm_pos_iff.2 ha0)]
  have e1 := grNorm_le_of_smul hu (a := 1) one_ne_zero (Λ' := latHT Z.t p _) (fun w hw => by
    rw [sp_epsMul_one, Category.id_comp]; exact latDR_subset_latHT _ p _ hw) _ n1
  obtain ⟨xO, hx, hx'⟩ := Guard.existsUnique_ext Z (spMap io ≫ y.y ≫ genι Z)
  have e2 := grNorm_le_of_smul hu ha0 (Λ' := latDR Z.t _) (fun w hw => by
    have := hB E H _ Z.t p ℂ_[p] hn xO (fun b hb => hx' b (hb.trans hx)) w (hx ▸ hw) a hna.le
    exact hx ▸ this) _ n2
  rw [norm_one, _root_.one_mul] at e1
  have l1 := Real.log_le_log p2 e1
  have l2 := Real.log_le_log (mul_pos (norm_pos_iff.2 ha0) p1) e2
  rw [Real.log_mul (norm_ne_zero_iff.2 ha0) p1.ne', hla] at l2
  simp only [lat]
  constructor <;> linarith

end Sign

section Phi

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

theorem phi_bounds (hB : HTBoundSt) (p : ℕ) [Fact p.Prime] (y : Pt s) (x : DV.Rt D.what₂.Tau N) :
    ((x.2 : ℕ) < j → vDiff D.host.E p * Real.log p ≤ phi s p y x ∧
      phi s p y x ≤ (vDiff D.host.E p + 1 / ((p : ℝ) - 1)) * Real.log p) ∧
    (j ≤ (x.2 : ℕ) → -(1 / ((p : ℝ) - 1) * Real.log p) ≤ phi s p y x ∧ phi s p y x ≤ 0) := by
  rw [phi, Guard.lnAt_eq, Guard.lnAt_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : (x.2 : ℕ) < S.Dw.p := by rw [S.p_eq]; exact h
    have := lnLie_sub hB y p (iotaP p) (DV.tauEmb D x.1) x.2
    simp only [FlagPt.lnRoot, if_pos h', if_true, Bool.false_eq_true, if_false]
    constructor <;> linarith [this.1, this.2]
  · have h' : ¬ (x.2 : ℕ) < S.Dw.p := by rw [S.p_eq]; exact h.not_gt
    have := lnLie_sub hB y p (iotaP p) (conjEmb (DV.tauEmb D x.1)) (S.Dw.p + S.Dw.q - 1 - x.2)
    simp only [FlagPt.lnRoot, if_neg h']
    constructor <;> linarith [this.1, this.2]


def admissibleTrivialStage (D : D7) {N j : ℕ} (hj : j ≤ N) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : AdmSt D N j jC where
  admitted _ _ _ := Unit
  mdl p _ la _ := GlobalTheory.trivialAdmissibleModel D p (jC p la) N j hj
  Crv _ _ _ _ := DV.Rt D.what₂.Tau N → ℝ
  deg _ _ _ _ c := c
  ht _ _ _ := ()

end Phi

end GlobalTheory.ShFam.Pad.Test
