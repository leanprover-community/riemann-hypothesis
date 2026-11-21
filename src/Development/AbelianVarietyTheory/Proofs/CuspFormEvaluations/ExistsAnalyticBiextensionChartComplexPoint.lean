import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameAdjointnessSeriesTrivial
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase
import BuildAid.ForwardExisting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJets
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetRdMulInvPow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CorrOfJetsOfAnalyticFrameProducts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppLESpMapJetPt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrame
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameFirstPartialLawTrivial
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CubicalReadingOneAnalyticFrame
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrameStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CorrOfJetsOfAnalyticFrameProductsStatement

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal

attribute [local instance] Over.cartesianMonoidalCategory

theorem chart_isHolFam_comp_clm {Y : Scheme.{0}} {g N : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (A : (Fin N → ℂ) →L[ℂ] (Fin g → ℂ)) : IsHolFam fun v => e (A v) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage A.continuous, h2.comp A.differentiable.differentiableOn fun _ hv => hv⟩

theorem chart_holTo_of_isHolFam {Y : Scheme.{0}} {N : ℕ} {e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolFam e) :
    IsHolTo Set.univ e := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  simp only [Set.mem_univ, true_and]
  exact ⟨h1, h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem AnPt.chart_jx_left (m : ℕ) : (Φ.jx m).left = jetPt (fun z => (Φ.e z).left) Φ.hol m := rfl

theorem AnPt.chart_e_zero : Φ.e 0 = 1 := by
  have h := Φ.e_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem AnPt.chart_trunc (m : ℕ) :
    homAt y.x (jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) ≫ Φ.jx (m + 1) =
      Φ.jx m := by
  ext1
  rw [Over.comp_left, Φ.chart_jx_left, Φ.chart_jx_left]
  exact jetPt_trunc _ _ m

theorem AnPt.chart_zero (m : ℕ) :
    homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) ≫ Φ.jx m = 1 := by
  ext1
  rw [Over.comp_left, Φ.chart_jx_left, one_left'']
  have h1 := jetPt_aug (fun z => (Φ.e z).left) Φ.hol m
  refine h1.trans ?_
  show (Φ.e 0).left = _
  rw [Φ.chart_e_zero, one_left'']
  show y.x ≫ _ = (spMap (algebraMap ℂ ℂ) ≫ y.x) ≫ _
  rw [Algebra.algebraMap_self, spMap]
  simp

theorem AnPt.chart_act (m : ℕ) (a : 𝓞 E) :
    Φ.jx m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) ≫ Φ.jx m := by
  ext1
  rw [Over.comp_left, Over.comp_left, Φ.chart_jx_left]
  have hlin : ∀ z, (Φ.e z).left ≫ (Xo.univ.t.act.act a).left = (Φ.e (fun k => ty k (a : E) * z k)).left := by
    intro z
    rw [← Over.comp_left, ← Φ.lin a z]
    rfl
  have hol' := isHolFam_comp (fun z => (Φ.e z).left) Φ.hol (Xo.univ.t.act.act a).left
  rw [jetPt_comp (fun z => (Φ.e z).left) Φ.hol _ _ hol' (fun z => rfl)]
  haveI : IsLocalHom ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
        Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) :=
    isLocalHom_jetMap (m := m)
      (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) -
        MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2))))
      (fun _ => sub_const_mem_orig _)
  symm
  refine jetPt_precomp (fun z => (Φ.e z).left) _ Φ.hol hol' ?_ m _ ?_
  · show (Φ.e 0).left ≫ _ = (Φ.e 0).left
    rw [hlin]; congr 2; funext k; simp
  · intro U hU f
    change jetSubstP m _ (jetOf m _) = _
    rw [jetSubstP_anAct, ← jetOf_scale m _ (contDiffAt_val _ Φ.hol hU f)]
    congr 1
    funext z
    show valAt' (Φ.e _).left U f = valAt' ((Φ.e z).left ≫ _) U f
    rw [hlin]

theorem AnPt.chart_tan (j0 : Fin g) (vt : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)
    (hd : IsDerivAt0 (fun z => (Φ.e z).left) (Pi.single j0 1) vt) :
    IsCombAt y.x (m := g)
      (fun j => (homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫
        Φ.jx (0 + 1)).left) (fun j => if j = j0 then 1 else 0) vt := by
  classical
  let v : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j =>
    homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫ Φ.jx (0 + 1)
  let u : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j => epsHom y.x (if j = j0 then 1 else 0) ≫ v j
  refine ⟨u, fun j => by simp [u, v, epsHom], ?_⟩
  have hone : ∀ j, j ≠ j0 → u j = 1 := by
    intro j hj
    ext1
    simp only [u, v, if_neg hj, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left]
    rw [← Category.assoc, spMap_epsMul_zero_jetTan, Category.assoc, jetPt_aug, one_left'']
    show spMap _ ≫ (Φ.e 0).left = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y.x) ≫ _
    rw [Φ.chart_e_zero, one_left'', Category.assoc]
    rfl
  have hprod : (List.ofFn u).prod = u j0 := by
    rw [List.prod_ofFn, Finset.prod_eq_single j0 (fun j _ hj => hone j hj) (by simp)]
  rw [hprod]
  simp only [u, v, if_pos rfl, ite_true, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left,
    epsMul_one]
  rw [show spMap (RingHom.id (DualNumber ℂ)) = 𝟙 _ from by simp [spMap]]
  exact (Category.id_comp _).trans (jetPt_tan (fun z => (Φ.e z).left) Φ.hol ((0 : Fin 1), j0) vt hd)

theorem AnPt.chart_pair : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (Φ.e (anPr 0 v)).left (Φ.e (anPr 1 v)).left
        ((Over.w (Φ.e (anPr 0 v))).trans (Over.w (Φ.e (anPr 1 v))).symm) :=
  chart_holTo_of_isHolFam (isHolFam_pullback_lift _ _ _ Xo.univ.t.G.hom Xo.univ.t.G.hom (2 * g)
    (fun v => (Φ.e (anPr 0 v)).left) (fun v => (Φ.e (anPr 1 v)).left) y.x
    (fun v => Over.w (Φ.e (anPr 0 v))) (fun v => Over.w (Φ.e (anPr 1 v)))
    (chart_isHolFam_comp_clm _ Φ.hol (anPr 0)) (chart_isHolFam_comp_clm _ Φ.hol (anPr 1)))

theorem AnPt.chart_law (m : ℕ) :
    homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) ≫ Φ.jx m =
      jpt y g Φ.jx m (0 : Fin 2) * jpt y g Φ.jx m (1 : Fin 2) :=
  jets_law y.x Φ.e Φ.hol Φ.jx (fun _ => rfl) Φ.e_add Φ.chart_pair m

theorem anPt_isChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el),
    IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec el) Φ.jx :=
  fun _ _ _ _ _ _ _ _ _ _ _ y _ _ el Φ =>
    { zero := fun m => Φ.chart_zero m
      trunc := fun m => Φ.chart_trunc m
      law := fun m => Φ.chart_law m
      act := fun m a => Φ.chart_act m a
      tan := fun ℓ => Φ.chart_tan (el.symm ℓ) (y.u ℓ.1 ℓ.2) (Φ.der ℓ)
      basis := fun v => basis_single el v }

end GlobalTheory.AnVal
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFrame_exponential_jets_isChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec el) Φ.jx := by
  atlas_forward_decl GlobalTheory.AnVal.anPt_isChart
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValJetEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

theorem jet_point_eq {K : Type} [Field K] {I : Type} {m : ℕ} (p : PrimeSpectrum (Jet K I m)) :
    p = IsLocalRing.closedPoint (Jet K I m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_jetAug _ (by rwa [jetAug_mk]))
    have := jet_nilpotent_of_orig K I m (sub_const_mem_orig (R := K) q)
    rwa [h0, map_zero, sub_zero] at this
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_id' {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (h' : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (b : Γ(Y, ⊤)ˣ) (hb : (f.appLE U ⊤ h').hom a.val = b.val) :
    res h (pullU f U a) = res (le_top : W ≤ ⊤) b := by
  have : b = res h' (pullU f U a) := Units.ext hb.symm
  rw [this, res_res']

theorem exists_gen_of_units {X Y : Scheme.{0}} (L : LB X) (hY : ∀ p q : Y, p = q) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : K → L.ι → Γ(Y, ⊤)ˣ)
    (hu : ∀ k j j' (h : ⊤ ≤ φ k ⁻¹ᵁ (L.U j ⊓ L.U j')),
      (u k j).val = ((φ k).appLE _ ⊤ h).hom (L.g j j').val * (u k j').val) :
    ∃ τ : LB.Gen (LB.LinComb L φ ε), τ.IsGen ∧ ∀ (j : K → L.ι) (h : ⊤ ≤ LB.wchart L φ j),
      (Y.presheaf.map (homOfLE h).op).hom (τ.s j).val = (∏ k, u k (j k) ^ ε k).val := by
  refine ⟨⟨fun j => res le_top (∏ k, u k (j k) ^ ε k)⟩, fun (i : K → L.ι) (j : K → L.ι) => ?_, fun j h => ?_⟩
  · by_cases hne : ∃ p, p ∈ LB.wchart L φ i ⊓ LB.wchart L φ j
    · obtain ⟨p, hp⟩ := hne
      have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) := fun k q _ => by
        rw [hY q p]
        exact ⟨LB.wchart_le L φ i k hp.1, LB.wchart_le L φ j k hp.2⟩
      have hle : ∀ k, LB.wchart L φ i ⊓ LB.wchart L φ j ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) := fun k =>
        le_top.trans (hk k)
      show res (inf_le_left : LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ i) (res le_top (∏ k, u k (i k) ^ ε k)) =
        (∏ k, (res (hle k) (pullU (φ k) _ (L.g (i k) (j k)))) ^ (ε k)) *
          res (inf_le_right : LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ j) (res le_top (∏ k, u k (j k) ^ ε k))
      rw [res_res', res_res', map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [res_pullU (φ k) _ _ (hk k) (L.g (i k) (j k)) (u k (i k) * (u k (j k))⁻¹)
        (by rw [Units.val_mul, hu k _ _ (hk k), Units.mul_inv_cancel_right]), map_zpow, map_zpow, ← mul_zpow,
        ← map_mul, inv_mul_cancel_right]
    · have hb : LB.wchart L φ i ⊓ LB.wchart L φ j = ⊥ :=
        le_bot_iff.1 fun p hp => (hne ⟨p, hp⟩).elim
      have : Subsingleton Γ(Y, LB.wchart L φ i ⊓ LB.wchart L φ j) := by
        rw [hb]; infer_instance
      exact Units.ext (this.elim _ _)
  · exact congrArg Units.val ((res_res' le_top h _).trans (res_id' _ _))

theorem jetOf_one {d : ℕ} (m : ℕ) : jetOf m (fun _ : Fin d → ℂ => (1 : ℂ)) = 1 := by
  rw [jetOf_const, map_one]

theorem jetOf_pow {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (k : ℕ) :
    jetOf m (fun z => f z ^ k) = jetOf m f ^ k := by
  induction k with
  | zero => simpa using jetOf_one m
  | succ k ih =>
    rw [pow_succ, ← ih, ← jetOf_mul m (hf.pow k) hf]
    congr 1

theorem contDiffAt_zpow' {d : ℕ} {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (h0 : f 0 ≠ 0) (k : ℤ) :
    ContDiffAt ℂ ω (fun z => f z ^ k) 0 := by
  cases k with
  | ofNat k => simpa using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)

theorem jetOf_zpow {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (h0 : f 0 ≠ 0)
    (u : (Jet ℂ (Fin 1 × Fin d) m)ˣ) (hu : u.val = jetOf m f) (k : ℤ) :
    jetOf m (fun z => f z ^ k) = (u ^ k).val := by
  cases k with
  | ofNat k => simpa [hu] using jetOf_pow m hf k
  | negSucc k =>
    rw [zpow_negSucc]
    refine Units.eq_inv_of_mul_eq_one_left ?_
    rw [Units.val_pow_eq_pow_val, hu, ← jetOf_pow m hf,
      ← jetOf_mul m (hf.pow (k + 1)) (contDiffAt_zpow' hf h0 _), ← jetOf_one m]
    refine jetOf_congr m ((hf.continuousAt.eventually_ne h0).mono fun z hz => ?_)
    show f z ^ (k + 1) * f z ^ (Int.negSucc k) = 1
    rw [zpow_negSucc, mul_inv_cancel₀ (pow_ne_zero _ hz)]

theorem jetOf_prod {d : ℕ} (m : ℕ) {K : Type} (s : Finset K) {f : K → (Fin d → ℂ) → ℂ}
    (hf : ∀ k, ContDiffAt ℂ ω (f k) 0) :
    jetOf m (fun z => ∏ k ∈ s, f k z) = ∏ k ∈ s, jetOf m (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetOf_one m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← jetOf_mul m (hf a) (contDiffAt_prod fun k _ => hf k)]
    congr 1
    funext z
    simp [Finset.prod_insert ha]

theorem appLE_spMap_jetPt {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {R : Type} [CommRing R] (r : Jet ℂ (Fin 1 × Fin d) m →+* R) (U : Y.Opens) (hU : e 0 cpt ∈ U)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) (a : Γ(Y, U)) :
    ((spMap r ≫ jetPt e hol m).appLE U ⊤ h).hom a = toΓ R (r (jetOf m fun z => valAt' (e z) U a)) := by
  have h1 : ⊤ ≤ jetPt e hol m ⁻¹ᵁ U := fun p _ => by
    rw [jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) p]
    show jetPt e hol m (IsLocalRing.closedPoint _) ∈ U
    rwa [jetPt_closedPoint]
  have e1 : (spMap r ≫ jetPt e hol m).appLE U ⊤ h = (jetPt e hol m).appLE U ⊤ h1 ≫ (spMap r).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap r) (jetPt e hol m) U ⊤ ⊤ h1 le_rfl).symm
  rw [e1, jetPt_appLE e hol m U hU h1, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem mem_of_spMap_jetPt {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {I : Type} (r : Jet ℂ (Fin 1 × Fin d) m →+* Jet ℂ I m) (U : Y.Opens)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) : e 0 cpt ∈ U := by
  let p : Sp (Jet ℂ I m) := IsLocalRing.closedPoint (Jet ℂ I m)
  have h2 : (spMap r ≫ jetPt e hol m) p ∈ U := h (show p ∈ (⊤ : (Sp (Jet ℂ I m)).Opens) from trivial)
  rw [Scheme.Hom.comp_apply] at h2
  rw [← jetPt_closedPoint e hol m, ← jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) (spMap r p)]
  exact h2

theorem contDiffAt_fr {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n : ℕ} (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (j : L.L.ι)
    (h : (Φ.e (Λ (colsOf n g 0))).left cpt ∈ L.L.U j) :
    ContDiffAt ℂ ω (fun v => Φ.fr j (Λ (colsOf n g v))) 0 := by
  have h1 : ContDiffAt ℂ ω (Φ.fr j) (Λ (colsOf n g 0)) :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} (Φ.fr j) (Φ.hol (L.L.U j) 0).1 (Φ.fr_hol j) _
      (top_le_of_mem h)).contDiffAt
  have h2 : ContDiff ℂ ω (colsOf n g) :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_apply ℂ ℂ (finProdFinEquiv (i, j))
  have h3 : ContDiff ℂ ω (fun v => Λ (colsOf n g v)) :=
    (LinearMap.toContinuousLinearMap Λ).contDiff.comp h2
  exact h1.comp 0 h3.contDiffAt

theorem exists_gen_jetRd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ k, Φ.JetMap m (φ k) (Λ k)) → ∃ τ : LB.Gen (LB.LinComb L.L φ ε), τ.IsGen ∧ Φ.JetRd m φ ε τ Λ := by
  intro S A _ _ L x0 g Φ n m K _ φ ε Λ hφ
  classical
  have hφ' := hφ
  choose hol hφe using hφ'
  let r : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m := renN n g m
  let F : K → L.L.ι → (Fin (n * g) → ℂ) → ℂ := fun k j v => Φ.fr j (Λ k (colsOf n g v))
  let u0 : K → L.L.ι → (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ := fun k j =>
    if h : IsUnit (jetOf m (F k j)) then h.unit else 1
  have hmem : ∀ k (U : A.left.Opens), ⊤ ≤ φ k ⁻¹ᵁ U → (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ U := fun k U h =>
    mem_of_spMap_jetPt _ (hol k) m r U (by rw [hφe k] at h; exact h)
  have hF0 : ∀ k j, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U j → F k j 0 ≠ 0 := fun k j h =>
    Φ.fr_ne j _ (top_le_of_mem h)
  have hu0 : ∀ k j, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U j → (u0 k j).val = jetOf m (F k j) := fun k j h => by
    have hu : IsUnit (jetOf m (F k j)) := isUnit_of_jetAug _ (by rw [jetAug_jetOf]; exact hF0 k j h)
    simp only [u0, dif_pos hu, IsUnit.unit_spec]
  let ρ : (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ →* Γ(Sp (Jet ℂ (Fin n × Fin g) m), ⊤)ˣ :=
    Units.map ((toΓ (Jet ℂ (Fin n × Fin g) m)).comp r).toMonoidHom
  have hρ : ∀ a, (ρ a).val = toΓ _ (r a.val) := fun _ => rfl
  obtain ⟨τ, h1, h2⟩ := exists_gen_of_units L.L (Y := Sp (Jet ℂ (Fin n × Fin g) m))
    (fun p q => (jet_point_eq (K := ℂ) (I := Fin n × Fin g) (m := m) p).trans
      (jet_point_eq (K := ℂ) (I := Fin n × Fin g) (m := m) q).symm) φ ε (fun k j => ρ (u0 k j)) (fun k j j' h => by
      have hm := hmem k _ h
      have key : ∀ (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (h : ⊤ ≤ ψ ⁻¹ᵁ (L.L.U j ⊓ L.L.U j')),
          ψ = spMap r ≫ jetPt _ (hol k) m → (ψ.appLE _ ⊤ h).hom (L.L.g j j').val = toΓ _ (r (jetOf m fun z =>
            valAt' (Φ.e (Λ k (colsOf n g z))).left (L.L.U j ⊓ L.L.U j') (L.L.g j j').val)) := by
        rintro _ h rfl
        exact appLE_spMap_jetPt _ (hol k) m r _ hm h _
      rw [key _ h (hφe k), hρ, hρ, ← map_mul, ← map_mul, hu0 k j hm.1, hu0 k j' hm.2,
        ← jetOf_mul m (contDiffAt_val _ (hol k) hm _) (contDiffAt_fr Φ (Λ k) j' hm.2)]
      exact congrArg (fun x => toΓ _ (r x))
        (jetOf_congr m ((eventually_mem _ (hol k) hm).mono fun z hz => Φ.fr_g j j' _ hz)))
  refine ⟨τ, h1, hφ, fun j h => ?_⟩
  have hm : ∀ k, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U (j k) := fun k =>
    hmem k _ (h.trans (LB.wchart_le L.L φ j k))
  rw [h2 j h]
  have e1 : (∏ k, ρ (u0 k (j k)) ^ ε k) = ρ (∏ k, u0 k (j k) ^ ε k) := by
    simp only [map_prod, map_zpow]
  rw [e1, hρ]
  show toΓ _ (r _) = toΓ _ (r (jetOf m fun v => ∏ k, F k (j k) v ^ ε k))
  refine congrArg (fun x => toΓ _ (r x)) ?_
  rw [jetOf_prod m Finset.univ (f := fun k v => F k (j k) v ^ ε k)
    (fun k => contDiffAt_zpow' (contDiffAt_fr Φ (Λ k) _ (hm k)) (hF0 k _ (hm k)) _), Units.coe_prod]
  exact Finset.prod_congr rfl fun k _ =>
    (jetOf_zpow m (contDiffAt_fr Φ (Λ k) _ (hm k)) (hF0 k _ (hm k)) _ (hu0 k _ (hm k)) _).symm

end GlobalTheory.AnValJetEx
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_jet_reading : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ k, Φ.JetMap m (φ k) (Λ k)) → ∃ τ : LB.Gen (LB.LinComb L.L φ ε), τ.IsGen ∧ Φ.JetRd m φ ε τ Λ := by
  atlas_forward_decl GlobalTheory.AnValJetEx.exists_gen_jetRd
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (n m : ℕ), (∀ i : Fin n, Φ.toAnFr.JetMap m (jpt y g Φ.jx m i).left (LinearMap.proj i)) ∧ Φ.toAnFr.JetMap m (1 : jO y g m n ⟶ Xo.univ.t.G).left 0 ∧ (∀ (a b : jO y g m n ⟶ Xo.univ.t.G) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m b.left Λ' → Φ.toAnFr.JetMap m (a * b).left (Λ + Λ') ∧ ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left), (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m) ∧ (∀ (a : jO y g m n ⟶ Xo.univ.t.G) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (α : 𝓞 E), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m (a ≫ Xo.univ.t.act.act α).left (tyAct ty α ∘ₗ Λ)) ∧ Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) := by
  first | exact @GlobalTheory.AnVal.jetPts_jetMap | exact GlobalTheory.AnVal.jetPts_jetMap | (intros; apply GlobalTheory.AnVal.jetPts_jetMap <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem jetMap_psum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el) (n m : ℕ) (xs : Fin n → (jO y g m n ⟶ Xo.univ.t.G))
    (Λ : Fin n → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hx : ∀ i, Φ.toAnFr.JetMap m (xs i).left (Λ i))
    (I : Finset (Fin n)) :
    Φ.toAnFr.JetMap m (psum Xo.univ.t.G xs I).left (∑ i ∈ I, Λ i) := by
  obtain ⟨-, h1, hmul, -⟩ := GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ n m
  have key : ∀ L : List (Fin n), Φ.toAnFr.JetMap m
      (L.foldr (fun k acc => padd Xo.univ.t.G (xs k) acc) (pzero Xo.univ.t.G (jO y g m n))).left
      (L.map Λ).sum := by
    intro L
    induction L with
    | nil => exact h1
    | cons k L ih => exact (hmul _ _ _ _ (hx k) ih).1
  have hs : (((List.finRange n).filter (fun x => decide (x ∈ I))).map Λ).sum = ∑ i ∈ I, Λ i := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    congr 1
    ext i
    simp
  rw [← hs]
  exact key _

theorem exists_isAnE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∃ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ
  have h : ∀ m, ∃ τ : FrTy y g Φ.jx m, τ.IsGen ∧ Φ.toAnFr.JetRd m
      (cφ ![jpt y g Φ.jx m (0 : Fin 2), jpt y g Φ.jx m (1 : Fin 2)]) (cε 2) τ (psumL 2 g) := by
    intro m
    refine GlobalTheory.T.exists_generator_jet_reading _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 m _
      (cφ ![jpt y g Φ.jx m (0 : Fin 2), jpt y g Φ.jx m (1 : Fin 2)]) (cε 2) (psumL 2 g) ?_
    intro I
    refine jetMap_psum Φ 2 m _ (fun i => LinearMap.proj i) ?_ I.down
    have h0 := (GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ 2 m).1
    intro i
    fin_cases i
    · exact h0 0
    · exact h0 1
  choose e he using h
  exact ⟨e, he⟩

end GlobalTheory.AnVal
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticFrame_jetPair_isAnE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∃ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e := by
  atlas_forward_decl GlobalTheory.AnVal.exists_isAnE
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValEL

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

theorem tay_coord {N : ℕ} (k : Fin N) :
    tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 := (contDiff_apply ℂ ℂ k).contDiffAt
  refine TCPf.eq_of_cc _ _ fun l => ?_
  rcases l.eq_nil_or_concat with rfl | ⟨l', ⟨a, j⟩, rfl⟩
  · simp only [List.foldr_nil, constantCoeff_tay, TM.mD_zero, MvPowerSeries.constantCoeff_X, Pi.zero_apply]
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    have hd : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j (1 : ℂ) : Fin N → ℂ) k := by
      funext y
      exact congrArg (fun T : (Fin N → ℂ) →L[ℂ] ℂ => T (Pi.single j 1))
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv
    rw [List.concat_eq_append, List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hθ, hd, TM.tay_const, MvPowerSeries.pderiv_X]
    congr 2
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h, Pi.single_apply]

theorem jetN_coord {n g : ℕ} (m : ℕ) (a : ℂ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => a * w i j) =
      Ideal.Quotient.mk _ (MvPolynomial.C a * MvPolynomial.X (i, j)) := by
  have h1 : jetOf m (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, j))) := by
    rw [jetOf, tay_coord, psJet, FBIdJet.psTrunc_eq, ← MvPolynomial.coe_X, FBIdJet.mk_trunc_coe]
  have h2 := jetOf_mul m (f := fun _ : Fin (n * g) → ℂ => a) (h := fun v => v (finProdFinEquiv (i, j)))
    contDiffAt_const (contDiff_apply ℂ ℂ _).contDiffAt
  rw [jetOf_const, h1] at h2
  have h3 : jetN m (fun w : Fin n → Fin g → ℂ => a * w i j) = renN n g m (jetOf m
    ((fun _ : Fin (n * g) → ℂ => a) * fun v => v (finProdFinEquiv (i, j)))) := rfl
  have h4 : renN n g m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, j)))) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
    show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
    rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]
  rw [h3, h2, map_mul, AlgHom.commutes, map_mul, h4, ← MvPolynomial.algebraMap_eq]
  rfl

theorem jetSubstP_X {κ κ' : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (sb : κ → MvPolynomial κ' ℂ) (p : κ) :
    (jetSubstP m sb : Jet ℂ κ m →ₐ[ℂ] Jet ℂ κ' m) (psJet m (MvPowerSeries.X p)) =
      Ideal.Quotient.mk _ (sb p - MvPolynomial.C (MvPolynomial.constantCoeff (sb p))) := by
  rw [psJet, FBIdJet.psTrunc_eq, ← MvPolynomial.coe_X, FBIdJet.mk_trunc_coe]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  rw [MvPolynomial.aeval_X]

theorem jetAug_jetN {n g : ℕ} (m : ℕ) (f : (Fin n → Fin g → ℂ) → ℂ) :
    (jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) (jetN m f) = f 0 := by
  rw [jetN, renN, jetAug_jetMap, jetAug_jetOf]
  rfl

theorem valAt'_id_inj {W : (Sp ℂ).Opens} (hW : ⊤ ≤ W) {a b : Γ(Sp ℂ, W)}
    (h : valAt' (𝟙 (Sp ℂ)) W a = valAt' (𝟙 (Sp ℂ)) W b) : a = b := by
  obtain rfl : W = ⊤ := top_le_iff.mp hW
  rw [valAt'_of _ _ le_rfl, valAt'_of _ _ le_rfl] at h
  unfold valAt at h
  have := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h
  simpa [Scheme.Hom.appLE] using this

theorem valAt'_spMap_toΓ {R : Type} [CommRing R] (f : R →+* ℂ) (a : R) :
    valAt' (spMap f) ⊤ (toΓ R a) = f a := by
  rw [valAt'_of _ _ le_rfl]
  have := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)) (toΓ R a)
  have h1 : (spMap f).appLE ⊤ ⊤ le_rfl = (spMap f).appTop := (Scheme.Hom.app_eq_appLE _).symm
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom (toΓ R a) = a := by simp [toΓ]
  unfold valAt
  rw [h1]
  exact this.trans (congrArg f h2)

theorem sameSum_cancel {X Y : Scheme.{0}} {P : Type} [Fintype P] (x x' : Y ⟶ X) (hx : x = x') (k : ℤ)
    (φ : Fin 1 ⊕ P → (Y ⟶ X)) (φ' : P → (Y ⟶ X)) (ε : P → ℤ) (h1 : ∀ i, φ (Sum.inl i) = x')
    (h2 : ∀ I, φ (Sum.inr I) = φ' I) :
    LB.SameSum (fun _ : Fin 1 => x) (fun _ => k) (Sum.elim φ φ')
      (fun i => k * Sum.elim (Sum.elim (fun _ => 1) fun I => -ε I) ε i) := by
  subst hx
  obtain rfl : φ = Sum.elim (fun _ => x) φ' := by
    funext i
    rcases i with i | I
    exacts [h1 i, h2 I]
  intro ψ
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc, ← Finset.sum_add_distrib,
    Finset.sum_eq_zero (s := (Finset.univ : Finset P)), add_zero]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x = ψ <;> simp [h]
  · intro I _
    by_cases h : φ' I = ψ <;> simp [h]

theorem prod_zpow_sum {K : Type} {a : ℂ} (ha : a ≠ 0) (s : Finset K) (ε : K → ℤ) :
    ∏ k ∈ s, a ^ ε k = a ^ ∑ k ∈ s, ε k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.prod_insert hk, Finset.sum_insert hk, ih, zpow_add₀ ha]

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem jetMap_uniq {n m : ℕ} {ψ ψ' : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) (h' : Φ.JetMap m ψ' Λ') (e : Λ = Λ') :
    ψ = ψ' := by
  subst e
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := h'
  rfl

theorem e_zero_left : (Φ.e 0).left = x0 ≫ eSec A := by
  rw [(Φ.e_ker 0).2 Φ.lat.zero_mem, Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem jetMap_aug {n m : ℕ} {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) :
    spMap ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ) ≫ ψ = (Φ.e 0).left := by
  obtain ⟨hol, rfl⟩ := h
  have hr : ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ).comp
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) =
      ((jetAug : Jet ℂ (Fin 1 × Fin (n * g)) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin (n * g)) m →+* ℂ) :=
    RingHom.ext fun a => jetAug_jetMap _ (fun _ => X_mem_orig _) a
  rw [← Category.assoc, ← anSpMap_comp, hr, jetPt_aug]
  exact congrArg (fun z => (Φ.e z).left) (map_zero Λ)

theorem corr_rig {n m : ℕ} {K : Type} [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ)
    (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : Φ.JetRd m φ ε τ Λ)
    (hε : ∑ k, ε k = 1) :
    LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L φ ε τ (homAt x0 (jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ)).left)
      (rigT A L.L L.rig (overAt x0 ℂ) 1) := by
  have hid : spMap (algebraMap ℂ ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have h0 : (overAt x0 ℂ).hom = x0 := by
    show spMap (algebraMap ℂ ℂ) ≫ x0 = x0
    rw [hid, Category.id_comp]
  intro j j' _ _ hjj
  have hj : ∀ k, j k = j' 0 := fun k => hjj k 0 (by
    rw [h0, ← e_zero_left Φ]; exact jetMap_aug Φ (h.1 k))
  apply Units.ext
  set W := LB.wchart L.L (fun k => (homAt x0 (jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ)).left ≫ φ k) j ⊓
    LB.wchart L.L (fun _ : Fin 1 => (overAt x0 ℂ).hom ≫ eSec A) j' with hWdef
  by_cases hc : cpt ∈ W
  · have hW : (⊤ : (Sp ℂ).Opens) ≤ W := top_le_of_mem (x := 𝟙 (Sp ℂ)) hc
    have hW1 := hW.trans inf_le_left
    have hW2 := hW.trans inf_le_right
    haveI : IsLocalHom ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ) :=
      ⟨fun a ha => isUnit_of_jetAug a ha.ne_zero⟩
    have hp : spMap ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ) cpt =
        IsLocalRing.closedPoint _ := Spec_closedPoint
    have hT : ⊤ ≤ LB.wchart L.L φ j := by
      refine (Scheme.preimage_eq_top_of_closedPoint_mem
        (𝟙 (Spec (CommRingCat.of (Jet ℂ (Fin n × Fin g) m)))) (U := LB.wchart L.L φ j) ?_).ge
      have : spMap ((jetAug : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin n × Fin g) m →+* ℂ) cpt ∈
          LB.wchart L.L φ j := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hc.1 k
      rwa [hp] at this
    have hU : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U (j' 0) := by
      rw [e_zero_left Φ, ← h0]
      exact hW2.trans (LB.wchart_le _ _ _ 0)
    refine valAt'_id_inj hW ?_
    refine (TB.ValAt.valAt'_res (𝟙 (Sp ℂ)) inf_le_left hW _).trans (Eq.trans ?_ (TB.ValAt.valAt'_res (𝟙 (Sp ℂ)) inf_le_right hW _).symm)
    refine (TB.ValAt.valAt'_res (𝟙 (Sp ℂ)) (V := LB.wchart L.L _ j) _ hW1 _).trans ((valAt'_comp (𝟙 (Sp ℂ)) _ _ _).trans ?_)
    have hR : valAt' (𝟙 (Sp ℂ)) _ ((rigT A L.L L.rig (overAt x0 ℂ) 1).s j').val = Φ.fr (j' 0) 0 := by
      rw [Φ.fr_0 _ hU]
      simp only [rigT, zpow_one]
      refine (TB.ValAt.valAt'_res (𝟙 (Sp ℂ)) (V := LB.wchart L.L _ j') _ hW2 _).trans ((valAt'_comp (𝟙 (Sp ℂ)) _ _ _).trans ?_)
      rw [Category.id_comp, h0]
      rfl
    refine Eq.trans ?_ hR.symm
    rw [Category.id_comp]
    refine (TB.ValAt.valAt'_res _ hT le_rfl _).symm.trans ?_
    refine (congrArg (valAt' _ ⊤) (h.2 j hT)).trans ((valAt'_spMap_toΓ _ _).trans ?_)
    refine (jetAug_jetN m _).trans ?_
    have hne := Φ.fr_ne _ _ hU
    simp only [map_zero, hj]
    rw [prod_zpow_sum hne, hε, zpow_one]
  · have hb : W = ⊥ := by
      refine le_bot_iff.1 fun p hp => hc ?_
      rwa [Subsingleton.elim cpt p]
    haveI : Subsingleton Γ(Sp ℂ, W) := by rw [hb]; infer_instance
    exact Subsingleton.elim (α := Γ(Sp ℂ, W)) _ _

end General

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] [StarRing (𝓞 E)] {y : FrPt Xo c ℂ} {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

def graphL (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : (Fin 1 → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ) :=
  LinearMap.pi ![LinearMap.proj 0, tyAct ty a ∘ₗ LinearMap.proj 0]

omit [IsCMField E] [StarRing (𝓞 E)] in
theorem graphL_apply (a : 𝓞 E) (w : Fin 1 → Fin g → ℂ) : graphL ty a w = ![w 0, tyAct ty a (w 0)] := by
  funext i
  fin_cases i <;> rfl

theorem jetRd_prim (wP : PrimTy H Xo) (hP : IsPrim wP) (m : ℕ) :
    Φ.toAnFr.JetRd (n := 1) m _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wP (Φ.jx m).left)
      (Sum.elim (fun _ => LinearMap.proj 0) fun I => psumL 2 g I ∘ₗ graphL ty H.w0) := by
  obtain ⟨hq, hx⟩ := (GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ 1 m).2.2.2.2
  rw [hx]
  refine GlobalTheory.AnValJetGlob.jetRd_pullGen _ _ _ _ _ Φ.toAnFr 1 m _ _ _ _ wP _ _ hq fun v => ?_
  have := (GlobalTheory.AnVal.PrimRd.prim_reading E H Dw l Xo c y g ty el Φ).2 wP hP (colsOf 1 g v 0)
  convert this using 1
  · rfl
  funext k
  rcases k with k | I
  · rfl
  · show psumL 2 g I (graphL ty H.w0 _) = _
    rw [graphL_apply]
    rfl

theorem jetRd_pe (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) :
    Φ.toAnFr.JetRd (n := 1) m _ _
      (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn g m ![0] ((anFB ty).A.act H.w0 j)])
      (fun I => psumL 2 g I ∘ₗ graphL ty H.w0) := by
  refine GlobalTheory.JetLinSub.jetRd_linSubst _ _ _ _ _ Φ.toAnFr 2 1 m (graphL ty H.w0) _ (fun p => ?_) _ _ _ (e m) _ (he m).2
  obtain ⟨i, j⟩ := p
  rw [jetSubstP_X]
  fin_cases i
  · have := jetN_coord (n := 1) m 1 0 j
    simp only [_root_.one_mul, map_one] at this
    refine Eq.trans ?_ this.symm
    simp
  · refine Eq.trans ?_ (jetN_coord (n := 1) m (ty j (H.w0 : E)) 0 j).symm
    have hr : psIn g m ![0] ((anFB ty).A.act H.w0 j) = psTrunc m (linAct ty H.w0 j) := by
      have : (fun p : Fin 1 × Fin g => ((![0] : Fin 1 → Fin 1) p.1, p.2)) = id := by
        funext p
        exact Prod.ext (Subsingleton.elim _ _) rfl
      rw [psIn, this, MvPolynomial.rename_id]
      rfl
    have hc := constantCoeff_of_mem_orig (FBIdJet.psTrunc_mem_orig m _ (cc_linAct ty H.w0 j))
    show Ideal.Quotient.mk _ (psIn g m ![0] ((anFB ty).A.act H.w0 j) -
      MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m ![0] ((anFB ty).A.act H.w0 j)))) = _
    rw [hr, hc, map_zero, sub_zero, FBIdJet.psTrunc_eq, ← FBIdJet.mk_trunc_coe m (MvPolynomial.C _ * _)]
    simp [linAct]

end Pt

theorem eL_appellHumbert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ (e : ∀ m, FrTy y g Φ.jx m) (wP : PrimTy H Xo), Φ.IsAnE e → IsPrim wP → (∀ (m k : ℕ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y g Φ.jx (anFB ty).A.act e wP m) k)) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (eL y g Φ.jx (anFB ty).A.act e wP 0) (homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) 0 →ₐ[ℂ] ℂ)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x ℂ) 1) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e wP he hP
  have key := fun m => GlobalTheory.AnVal.jetRd_mul_inv_pow _ _ _ _ _ Φ.toAnFr 1 m _ _ _ _ _ _ _ _ _ _
    (jetRd_prim Φ wP hP m) (jetRd_pe Φ e he m)
  refine ⟨fun m k τ hτ => ?_, corr_rig Φ.toAnFr _ _ _ _ (key 0).1 ?_⟩
  · have h2 := (GlobalTheory.AnVal.jetRd_mul_inv_pow _ _ _ _ _ Φ.toAnFr 1 m _ _ _ _ _ _ _ _ _ _ (key m).1 hτ).2.2 k
    refine GlobalTheory.AnVal.JetCorr.corr_of_jetRd _ _ _ _ _ Φ.toAnFr hI 1 m _ _ _ _ _ _ _ _ _ _ hτ h2 ?_
    exact sameSum_cancel _ _ rfl _ _ _ _ (fun _ => Category.comp_id _) fun I =>
      jetMap_uniq Φ.toAnFr ((jetRd_prim Φ wP hP m).1 (Sum.inr I)) ((jetRd_pe Φ e he m).1 I) rfl
  · simp [Fintype.sum_sum_type]

end GlobalTheory.AnValEL
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ (e : ∀ m, FrTy y g Φ.jx m) (wP : PrimTy H Xo), Φ.IsAnE e → IsPrim wP → (∀ (m k : ℕ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y g Φ.jx (anFB ty).A.act e wP m) k)) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (eL y g Φ.jx (anFB ty).A.act e wP 0) (homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) 0 →ₐ[ℂ] ℂ)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x ℂ) 1) := by
  atlas_forward_decl GlobalTheory.AnValEL.eL_appellHumbert
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameImm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section Group

variable {g : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}

theorem deriv_one (h0 : e 0 = (1 : Over.mk y ⟶ G).left) : IsDerivAt0 e 0 (1 : epsPt y ⟶ G).left := by
  let φ : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have h1 : (1 : epsPt y ⟶ G).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 := by
    rw [h0, ← MonObj.comp_one φ]
    rfl
  have h2 : spMap GlobalTheory.TangentOrigin.fstC ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 = e 0 := by
    rw [← Category.assoc, GlobalTheory.FrameTangent.spMap_comp']
    have : GlobalTheory.TangentOrigin.fstC.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
      RingHom.ext fun r => by simp
    rw [this]
    simp [spMap]
  rw [h1, GlobalTheory.PointUnif.isDerivAt0_iff]
  refine ⟨h2, fun U hU f => ?_⟩
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h2 ▸ (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp _ _ U hU0 hU, map_zero]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem deriv_list (h0 : e 0 = (1 : Over.mk y ⟶ G).left) :
    ∀ (m : ℕ) (w : Fin m → Fin g → ℂ) (v : Fin m → (epsPt y ⟶ G)), (∀ i, IsDerivAt0 e (w i) (v i).left) →
      IsDerivAt0 e (∑ i, w i) (List.ofFn v).prod.left
  | 0, w, v, _ => by simpa using deriv_one h0
  | m + 1, w, v, h => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
    exact GlobalTheory.PointUnif.deriv_mul h0 (h 0) (deriv_list h0 m _ _ fun i => h i.succ)

end Group

theorem anPt_imm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm := by
  classical
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ w hw
  by_contra hcon
  push Not at hcon
  apply hw
  have he0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  have h0 : (fun z => (Φ.e z).left) 0 = (1 : Over.mk y.x ⟶ Xo.univ.t.G).left := congrArg (·.left) he0
  have d0 := deriv_one (e := fun z => (Φ.e z).left) h0
  have dw : IsDerivAt0 (fun z => (Φ.e z).left) w (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    refine ⟨d0.1, fun U hU f => (d0.2 U hU f).trans ?_⟩
    rw [map_zero]
    refine (hcon U f ?_).symm
    have h3 := (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
    exact (congrArg (fun p : Sp ℂ ⟶ Xo.univ.t.G.left => ⊤ ≤ p ⁻¹ᵁ U) d0.1).mp h3
  let q := (Fintype.equivFin (Lt1 Dw)).symm
  have key : ∀ w' : Fin g → ℂ, IsDerivAt0 (fun z => (Φ.e z).left) w' (1 : epsPt y.x ⟶ Xo.univ.t.G).left →
      IsCombAt y.x (m := Fintype.card (Lt1 Dw)) (fun i => y.u (q i).1 (q i).2) (fun i => w' (el.symm (q i)))
        (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    intro w' hw'
    let v : Fin (Fintype.card (Lt1 Dw)) → (epsPt y.x ⟶ Xo.univ.t.G) := fun i =>
      GlobalTheory.FrameTangent.smT y.x (w' (el.symm (q i)))
        (GlobalTheory.FrameTangent.ovT (t := Xo.univ.t) (y.tan (q i).1 (q i).2))
    refine ⟨v, fun i => rfl, GlobalTheory.PointUnif.deriv_unique ?_ hw'⟩
    have hs : w' = ∑ i, w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ) := by
      exact (pi_eq_sum_univ' w').trans
        (Equiv.sum_comp (q.trans el.symm) (fun j => w' j • (Pi.single j 1 : Fin g → ℂ))).symm
    have := deriv_list (e := fun z => (Φ.e z).left) h0 _
      (fun i => w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ)) v
      fun i => GlobalTheory.PointUnif.deriv_smul (Φ.der (q i)) _
    rwa [← hs] at this
  have ht : IsTanAt y.x (1 : epsPt y.x ⟶ Xo.univ.t.G).left := ⟨Over.w _, d0.1.trans h0⟩
  have hu := (GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c ℂ y _ ht).unique
    (y₁ := fun ℓ => w (el.symm ℓ)) (y₂ := fun ℓ => (0 : Fin g → ℂ) (el.symm ℓ)) (key w dw) (key 0 d0)
  funext j
  simpa using congrFun hu (el j)

end GlobalTheory.FrameImm
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFrame_exponential_immersion_at_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm := by
  atlas_forward_decl GlobalTheory.FrameImm.anPt_imm
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetVal

open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

section Pt

variable {K : Type} [Field K] {σ : Type} {m : ℕ}

theorem jet_pt_eq (p : PrimeSpectrum (Jet K σ m)) : p = IsLocalRing.closedPoint (Jet K σ m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_jetAug _ (by rwa [jetAug_mk]))
    have := jet_nilpotent_of_orig K σ m (sub_const_mem_orig (R := K) q)
    rwa [h0, map_zero, sub_zero] at this
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

end Pt

theorem gs_appLE_top {Y X : Scheme.{0}} (φ : Y ⟶ X) (y : Y) (U : X.Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs φ y U a = gs (𝟙 Y) y ⊤ ((φ.appLE U ⊤ h).hom a) := by
  have hy : φ y ∈ U := h trivial
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, gs_res (𝟙 Y) y h trivial, gs_pull (𝟙 Y) φ y U hy, Category.id_comp]

section PullSec

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A)
  (hh : h ≫ snd T A = snd T' A)

def pullSecF (s : LB.Sec (LPow A L a T)) (j : Fin 1 → L.ι) : Γ((T' ⊗ A).left, (LPow A L a T').U j) :=
  ((T' ⊗ A).left.presheaf.map (homOfLE (chart_le_res A L h hh a j)).op).hom ((h.left.app _).hom (s.f j))

def pullSecLP (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') where
  f := pullSecF A L a h hh s
  compat i j := fn_ext fun y hy => by
    have hi : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) i := chart_le_res A L h hh a i hy.1
    have hj : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) j := chart_le_res A L h hh a j hy.2
    have v : ∀ j', y ∈ (LPow A L a T').U j' → gs (𝟙 _) y _ (pullSecF A L a h hh s j') =
        gs (𝟙 _ ≫ h.left) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j') (s.f j') := fun j' hj' =>
      (gs_res _ y _ hj' _).trans (gs_pull _ h.left y _ (chart_le_res A L h hh a j' hj') _)
    refine ((gs_res (𝟙 _) y _ hy _).trans ((v i hy.1).trans (sec_trans s (𝟙 _ ≫ h.left) y hi hj))).trans ?_
    refine Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm
    refine congrArg₂ (· * ·) ?_ ((v j hy.2).symm.trans (gs_res (𝟙 _) y _ hy _).symm)
    refine Eq.trans ?_ (gs_unit (𝟙 _) y _ hy _).symm
    refine congrArg Units.val (Eq.trans ?_
      (gm_linComb L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) (𝟙 _) y i j hy.1 hy.2).symm)
    simp only [trF, Category.assoc, ← Over.comp_left, hh]

theorem isPullSec_pullSecLP (s : LB.Sec (LPow A L a T)) : IsPullSec A L a h hh s (pullSecLP A L a h hh s) :=
  fun _ => rfl

end PullSec

section Fam

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (L : LB G.left) {x0 : Sp ℂ ⟶ X} {g : ℕ}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (hol : IsHolFam e) (he : ∀ z, e z ≫ G.hom = x0)

def jB (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 :=
  Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m))) rfl

def xJ (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ G :=
  Over.homMk (jetPt e hol m) (jetPt_over e hol G.hom x0 he m)

def ePt (z : Fin g → ℂ) : Over.mk x0 ⟶ G := Over.homMk (e z) (he z)

def lftJ (z : Fin g → ℂ) : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left := (ptSecT G (ePt e he z)).left

theorem lftJ_snd (z : Fin g → ℂ) : lftJ e he z ≫ (snd (Over.mk x0) G).left = e z := by
  rw [lftJ, ← Over.comp_left, ptSecT, lift_snd]
  rfl

theorem lftJ_fst (z : Fin g → ℂ) : lftJ e he z ≫ (fst (Over.mk x0) G).left = 𝟙 _ := by
  rw [lftJ, ← Over.comp_left, ptSecT, lift_fst]
  rfl

theorem lftJ_eq (holP : IsHolFam (lftJ e he)) (m : ℕ) :
    (ptSecT G (xJ e hol he m)).left ≫ (jB (x0 := x0) (g := g) m ▷ G).left = jetPt (lftJ e he) holP m := by
  have h1 : jetPt (lftJ e he) holP m ≫ (Over.mk x0 ⊗ G).hom =
      spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ x0 :=
    jetPt_over (lftJ e he) holP _ x0 (fun z => Over.w (ptSecT G (ePt e he z))) m
  let φ : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 ⊗ G := Over.homMk (jetPt (lftJ e he) holP m) h1
  suffices hs : ptSecT G (xJ e hol he m) ≫ jB m ▷ G = φ by
    rw [← Over.comp_left, hs]
    rfl
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, whiskerRight_fst, ptSecT, lift_fst_assoc, Category.id_comp]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    show spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) = jetPt (lftJ e he) holP m ≫ (fst (Over.mk x0) G).left
    rw [jetPt_comp (lftJ e he) holP _ (fun _ => 𝟙 (Sp ℂ)) (isHolFam_const _) (lftJ_fst e he) m, ← jetPt_const,
      Category.comp_id]
  · rw [Category.assoc, whiskerRight_snd, ptSecT, lift_snd]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    show jetPt e hol m = jetPt (lftJ e he) holP m ≫ (snd (Over.mk x0) G).left
    rw [jetPt_comp (lftJ e he) holP _ e hol (lftJ_snd e he) m]

theorem isValueAt_jet (holP : IsHolFam (lftJ e he)) (m k : ℕ)
    (F : LB.Sec (LPow G L (k : ℤ) (Over.mk x0)))
    (F' : LB.Sec (LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))))
    (hF' : IsPullSec G L (k : ℤ) (jB m ▷ G) (whiskerRight_snd _ _) F F')
    (θF : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ)
    (hfr : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j})
    (hfr0 : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (hrd : ∀ j z (pt : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left), pt ≫ (snd (Over.mk x0) G).left = e z →
      pt ≫ (fst (Over.mk x0) G).left = 𝟙 (Sp ℂ) → ⊤ ≤ e z ⁻¹ᵁ L.U j →
      valAt' pt ((LPow G L (k : ℤ) (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θF z * fr j z ^ (k : ℤ))
    (τ : LB.Gen (LB.LinComb L (Y := (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) (K := Fin 1)
      (fun _ => (xJ e hol he m).left) (fun _ => (k : ℤ))))
    (hτ : ∀ (j : Fin 1 → L.ι) (h : ⊤ ≤ LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) j),
      ((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left.presheaf.map (homOfLE h).op).hom (τ.s j).val =
        toΓ _ (jetOf m (fun z => fr (j 0) z ^ k))) :
    IsValueAt G L (k : ℤ) F' (xJ e hol he m) τ (toΓ _ (jetOf m θF)) := by
  intro j
  obtain ⟨j0, rfl⟩ : ∃ j0, j = fun _ => j0 := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine fn_ext fun x hx => ?_
  let Φ := (ptSecT G (xJ e hol he m)).left
  let Ψ := (jB (x0 := x0) (g := g) m ▷ G).left
  let U := (LPow G L (k : ℤ) (Over.mk x0)).U (fun _ => j0)
  have key : Φ ≫ Ψ = jetPt (lftJ e he) holP m := lftJ_eq e hol he holP m
  have hW : ⊤ ≤ LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) (fun _ => j0) := fun p _ => by
    have e1 := jet_pt_eq (K := ℂ) (σ := Fin 1 × Fin g) (m := m) p
    have e2 := jet_pt_eq (K := ℂ) (σ := Fin 1 × Fin g) (m := m) x
    rw [e1, ← e2]
    exact hx
  have hmem1 : ∀ p, Φ p ∈ (LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))).U (fun _ => j0) := fun p =>
    val_le G L (xJ e hol he m) (fun _ => j0) (hW (show p ∈ (⊤ : (Sp (Jet ℂ (Fin 1 × Fin g) m)).Opens) from trivial))
  have hmem : ∀ p, Ψ (Φ p) ∈ U := fun p =>
    chart_le_res G L (T := Over.mk x0) (T' := overAt x0 (Jet ℂ (Fin 1 × Fin g) m)) (jB (x0 := x0) (g := g) m ▷ G)
      (whiskerRight_snd _ _) (k : ℤ) (fun _ => j0) (hmem1 p)
  have hU' : ⊤ ≤ jetPt (lftJ e he) holP m ⁻¹ᵁ U := fun p _ => by
    have h2 := hmem p
    rw [← Scheme.Hom.comp_apply, key] at h2
    exact h2
  have hU : lftJ e he 0 cpt ∈ U := by
    have h3 : jetPt (lftJ e he) holP m (IsLocalRing.closedPoint _) ∈ U := hU' trivial
    rwa [jetPt_closedPoint] at h3
  have hU0 : e 0 cpt ∈ L.U j0 := by
    have h4 : (snd (Over.mk x0) G).left (lftJ e he 0 cpt) ∈ L.U j0 := Set.mem_iInter.1 hU 0
    rwa [← Scheme.Hom.comp_apply, lftJ_snd] at h4

  have heq : ∀ᶠ z in nhds 0, valAt' (lftJ e he z) U (F.f (fun _ => j0)) = θF z * fr j0 z ^ k :=
    (eventually_mem e hol hU0).mono fun z hz => by
      rw [hrd j0 z (lftJ e he z) (lftJ_snd e he z) (lftJ_fst e he z) hz, zpow_natCast]
  have hval : ContDiffAt ℂ ω (fun z => valAt' (lftJ e he z) U (F.f (fun _ => j0))) 0 :=
    contDiffAt_val (lftJ e he) holP hU _
  have hfrA : ContDiffAt ℂ ω (fr j0) 0 :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ e z ⁻¹ᵁ L.U j0} (fr j0) (hol (L.U j0) 0).1 (hfr j0) 0
      (top_le_of_mem hU0)).contDiffAt
  have hfrk : ContDiffAt ℂ ω (fun z => fr j0 z ^ k) 0 := hfrA.pow k
  have hθ : ContDiffAt ℂ ω θF 0 := by
    refine (hval.div hfrk (pow_ne_zero _ (hfr0 j0 0 (top_le_of_mem hU0)))).congr_of_eventuallyEq ?_
    filter_upwards [heq, eventually_mem e hol hU0] with z hz hz'
    exact eq_div_of_mul_eq (pow_ne_zero _ (hfr0 j0 z hz')) hz.symm
  have hjet : jetOf m (fun z => valAt' (lftJ e he z) U (F.f (fun _ => j0))) =
      jetOf m θF * jetOf m (fun z => fr j0 z ^ k) := by
    rw [jetOf_congr m heq]
    exact jetOf_mul m hθ hfrk

  have s1 : gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x
      (LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) (fun _ => j0))
      ((((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left).presheaf.map
        (homOfLE (val_le G L (xJ e hol he m) (fun _ => j0))).op).hom
          (((ptSecT G (xJ e hol he m)).left.app _).hom (F'.f (fun _ => j0)))) =
      gs Φ x ((LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))).U (fun _ => j0)) (F'.f (fun _ => j0)) :=
    (gs_res (𝟙 _) x (val_le G L (xJ e hol he m) (fun _ => j0)) hx _).trans
      ((gs_pull (𝟙 _) Φ x _ (hmem1 x) _).trans (by rw [Category.id_comp]))
  have s2 : gs Φ x ((LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))).U (fun _ => j0)) (F'.f (fun _ => j0)) =
      gs (Φ ≫ Ψ) x U (F.f (fun _ => j0)) := by
    rw [hF' (fun _ => j0)]
    exact (gs_res Φ x (chart_le_res G L (T := Over.mk x0) (T' := overAt x0 (Jet ℂ (Fin 1 × Fin g) m))
        (jB (x0 := x0) (g := g) m ▷ G) (whiskerRight_snd _ _) (k : ℤ) (fun _ => j0)) (hmem1 x) _).trans
      (gs_pull Φ Ψ x U (hmem x) _)
  have s3 : gs (Φ ≫ Ψ) x U (F.f (fun _ => j0)) = gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x ⊤
      (toΓ _ (jetOf m θF * jetOf m (fun z => fr j0 z ^ k))) := by
    rw [key, gs_appLE_top _ x U hU', jetPt_appLE (lftJ e he) holP m U hU hU', CommRingCat.comp_apply, jetψ_apply,
      ← hjet]
    rfl

  have r1 : gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x
      (LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) (fun _ => j0))
      ((((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left).presheaf.map (homOfLE le_top).op).hom
          (toΓ _ (jetOf m θF)) * (τ.s (fun _ => j0)).val) =
      gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x ⊤
        (toΓ _ (jetOf m θF * jetOf m (fun z => fr j0 z ^ k))) := by
    refine (gs_mul (𝟙 _) x _ hx _ _).trans ?_
    refine (congrArg₂ (· * ·) (gs_res (𝟙 _) x le_top hx _)
      ((gs_res (𝟙 _) x hW trivial (τ.s (fun _ => j0)).val).symm.trans
        (congrArg (gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x ⊤) (hτ _ hW)))).trans ?_
    rw [← gs_mul (𝟙 _) x ⊤ trivial, ← map_mul]
  exact (s1.trans (s2.trans s3)).trans r1.symm

theorem isHolFam_lftJ (hol : IsHolFam e) : IsHolFam (lftJ e he) := by
  have hl : lftJ e he = fun z => Limits.pullback.lift (f := x0) (g := G.hom) (𝟙 (Sp ℂ)) (e z)
      ((Category.id_comp x0).trans (he z).symm) := by
    funext z
    rw [lftJ, ptSecT, Over.lift_left]
    rfl
  rw [hl]
  exact GlobalTheory.AnVal.isHolFam_pullback_lift X (Sp ℂ) G.left x0 G.hom g (fun _ => 𝟙 (Sp ℂ)) e x0 (fun _ => Category.id_comp x0) he
    (isHolFam_const _) hol

end Fam

def onePr (g : ℕ) : (Fin (1 * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (1 * g) => ℂ)
    (finProdFinEquiv ((0 : Fin 1), j))

theorem onePr_apply {g : ℕ} (v : Fin (1 * g) → ℂ) (j : Fin g) : onePr g v j = v (finProdFinEquiv ((0 : Fin 1), j)) :=
  rfl

theorem anLin_onePr {g : ℕ} (p : Fin 1 × Fin g) :
    anLin (onePr g) p = MvPolynomial.X ((0 : Fin 1), finProdFinEquiv ((0 : Fin 1), p.2)) := by
  rw [anLin, Finset.sum_eq_single (finProdFinEquiv ((0 : Fin 1), p.2))]
  · rw [onePr_apply, Pi.single_eq_same, map_one]
    exact _root_.one_mul _
  · intro k _ hk
    rw [onePr_apply, Pi.single_eq_of_ne (Ne.symm hk), map_zero, zero_mul]
  · simp

theorem jetN_one {g : ℕ} (m : ℕ) {f : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) :
    jetN (n := 1) m (fun w => f (w 0)) = jetOf m f := by
  have h1 : (fun v => (fun w : Fin 1 → Fin g → ℂ => f (w 0)) (colsOf 1 g v)) = f ∘ onePr g := rfl
  rw [jetN, h1, jetOf_comp_anLin m hf, renN,
    anJetMap_comp _ _ _ _ (fun p => MvPolynomial.X p) (fun _ => X_mem_orig _) (fun p => by
      obtain ⟨a, j⟩ := p
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      simp only [anLin_onePr, MvPolynomial.aeval_X, Equiv.symm_apply_apply])]
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (jetOf m f)
  rw [← hp]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval MvPolynomial.X p) = _
  rw [MvPolynomial.aeval_X_left_apply]

theorem isValueAt_jetPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (m k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.Rd k F θ → Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → ∃ F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y g m 1)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y g m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧ IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (Φ.jx m) τ (toΓ _ (jetOf m θ)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ m k F θ τ hF hτ
  have he : ∀ z, (Φ.e z).left ≫ Xo.univ.t.G.hom = y.x := fun z => Over.w (Φ.e z)
  refine ⟨pullSecLP _ _ _ _ (whiskerRight_snd _ _) F, isPullSec_pullSecLP _ _ _ _ _ F, ?_⟩
  refine isValueAt_jet Xo.univ.t.PP.L (fun z => (Φ.e z).left) Φ.hol he (isHolFam_lftJ _ he Φ.hol) m k F _
    (isPullSec_pullSecLP _ _ _ _ _ F) θ Φ.fr Φ.fr_hol Φ.fr_ne hF τ fun j h => ?_
  have hmem : jetPt (fun z => (Φ.e z).left) Φ.hol m (IsLocalRing.closedPoint _) ∈ Xo.univ.t.PP.L.U (j 0) :=
    Set.mem_iInter.1 (h trivial) 0
  rw [jetPt_closedPoint] at hmem
  have hA : ContDiffAt ℂ ω (Φ.fr (j 0)) 0 :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j 0)} (Φ.fr (j 0))
      (Φ.hol (Xo.univ.t.PP.L.U (j 0)) 0).1 (Φ.fr_hol (j 0)) 0 (top_le_of_mem hmem)).contDiffAt
  refine (hτ.2 j h).trans (congrArg _ ?_)
  rw [← jetN_one m (hA.pow k)]
  congr 1
  funext w
  simp

end GlobalTheory.JetVal
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isValueAt_jetPoint_cmFrame_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (m k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.Rd k F θ → Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → ∃ F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y g m 1)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y g m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧ IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (Φ.jx m) τ (toΓ _ (jetOf m θ)) := by
  atlas_forward_decl GlobalTheory.JetVal.isValueAt_jetPt
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValSecondLaw

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff

theorem tay_coord {N : ℕ} (k : Fin N) :
    tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 := (contDiff_apply ℂ ℂ k).contDiffAt
  refine TCPf.eq_of_cc _ _ fun l => ?_
  induction l using List.reverseRecOn with
  | nil =>
    simp only [List.foldr_nil]
    rw [constantCoeff_tay, TM.mD_zero]
    simp
  | append_singleton l q _ =>
    obtain ⟨a, j⟩ := q
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    rw [List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hθ]
    have hd : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j 1 : Fin N → ℂ) k := by
      funext y
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv (x := y)
      exact congrArg (fun L : (Fin N → ℂ) →L[ℂ] ℂ => L (Pi.single j 1)) this
    rw [hd, TM.tay_const, MvPowerSeries.pderiv_X]
    congr 2
    by_cases h : k = j
    · subst h; simp
    · simp [Pi.single_apply, h, Prod.ext_iff]

theorem psJet_X' {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (p : κ) :
    psJet m (MvPowerSeries.X p : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X p) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem jetN_coord {n g : ℕ} (m : ℕ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j) = Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  have h : jetOf m (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, j))) := by
    rw [jetOf, tay_coord, psJet_X']
  show renN n g m (jetOf m (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j)))) = _
  rw [h]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  simp only [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

theorem jetN_coord_add {n g : ℕ} (m : ℕ) (i i' : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j + w i' j) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j) + MvPolynomial.X (i', j)) := by
  rw [map_add, ← jetN_coord, ← jetN_coord, jetN, jetN, jetN, ← map_add]
  exact congrArg _ (jetOf_add m (contDiff_apply ℂ ℂ (finProdFinEquiv (i, j))).contDiffAt
      (contDiff_apply ℂ ℂ (finProdFinEquiv (i', j))).contDiffAt)

theorem subst_X {κ κ' : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (sb : κ → MvPolynomial κ' ℂ) (p : κ) :
    (jetSubstP m sb : Jet ℂ κ m →ₐ[ℂ] Jet ℂ κ' m) (psJet m (MvPowerSeries.X p)) =
      Ideal.Quotient.mk _ (sb p - MvPolynomial.C (MvPolynomial.constantCoeff (sb p))) := by
  rw [psJet_X']
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  simp

theorem psIn_add {g n' : ℕ} (m : ℕ) (r : Fin 2 → Fin n') (j : Fin g) :
    (Ideal.Quotient.mk _ (psIn g m r (addF ℂ g j) - MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m r (addF ℂ g j)))) :
      Jet ℂ (Fin n' × Fin g) m) =
      Ideal.Quotient.mk _ (MvPolynomial.X (r 0, j) + MvPolynomial.X (r 1, j)) := by
  have hc : MvPolynomial.constantCoeff (psTrunc m (addF ℂ g j)) = 0 := by
    rw [FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_truncTotal _ (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [addF]
  have ha : (addF ℂ g j : MvPowerSeries (Fin 2 × Fin g) ℂ) =
      ((MvPolynomial.X ((0 : Fin 2), j) + MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin g) ℂ) :
        MvPowerSeries (Fin 2 × Fin g) ℂ) := by simp [addF]
  rw [psIn, MvPolynomial.constantCoeff_rename, hc, map_zero, sub_zero]
  have key : ∀ P : MvPolynomial (Fin 2 × Fin g) ℂ,
      (Ideal.Quotient.mk _ (MvPolynomial.rename (fun p : Fin 2 × Fin g => (r p.1, p.2)) P) : Jet ℂ (Fin n' × Fin g) m) =
      jetMap (m := m) (fun p : Fin 2 × Fin g => MvPolynomial.X (r p.1, p.2)) (fun _ => X_mem_orig _)
        (Ideal.Quotient.mk _ P) := by
    intro P
    show _ = Ideal.Quotient.mk _ (MvPolynomial.aeval _ _)
    rw [MvPolynomial.rename_eq_aeval]
    rfl
  rw [key, ha, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, ← key]
  simp

theorem sameSum_of_jetMap {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n m : ℕ} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)} {ε : K → ℤ}
    {Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    {φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)} {ε' : K' → ℤ}
    {Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (h : ∀ k, Φ.JetMap m (φ k) (Λ k)) (h' : ∀ k, Φ.JetMap m (φ' k) (Λ' k))
    (hs : ∀ f : ((Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) → ℤ, ∑ k, ε k * f (Λ k) = ∑ k, ε' k * f (Λ' k)) :
    LB.SameSum φ ε φ' ε' := by
  classical
  intro ψ
  have key : ∀ (χ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) M, Φ.JetMap m χ M → (χ = ψ ↔ Φ.JetMap m ψ M) := by
    rintro χ M ⟨h1, h2⟩
    exact ⟨fun e => ⟨h1, e ▸ h2⟩, fun ⟨_, h4⟩ => h2.trans h4.symm⟩
  have := hs fun M => if Φ.JetMap m ψ M then 1 else 0
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (this.trans (Finset.sum_congr rfl fun k _ => ?_))
  · rw [key _ _ (h k)]
    split_ifs <;> simp
  · rw [key _ _ (h' k)]
    split_ifs <;> simp

theorem sum_two {M : Type} [AddCommMonoid M] (F : ULift.{0} (Finset (Fin 2)) → M) :
    ∑ I, F I = F ⟨∅⟩ + F ⟨{0}⟩ + F ⟨{1}⟩ + F ⟨{0, 1}⟩ := by
  rw [← Equiv.ulift.symm.sum_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]
  rfl

theorem sum_three {M : Type} [AddCommMonoid M] (F : thK.{0} → M) :
    ∑ I, F I = F ⟨∅⟩ + F ⟨{0}⟩ + F ⟨{1}⟩ + F ⟨{2}⟩ + F ⟨{0, 1}⟩ + F ⟨{0, 2}⟩ + F ⟨{1, 2}⟩ + F ⟨{0, 1, 2}⟩ := by
  have h := Equiv.sum_comp (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) F
  refine h.symm.trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]
  rfl

theorem psumL_pi {n n' g : ℕ} (I : ULift.{0} (Finset (Fin n))) (B : Fin n → (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    psumL n g I ∘ₗ LinearMap.pi B = ∑ i ∈ I.down, B i := by
  refine LinearMap.ext fun w => ?_
  simp [psumL, LinearMap.sum_apply]

theorem count {g : ℕ} (P Q R : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (f : ((Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) → ℤ) :
    ∑ I : thK.{0}, thε I * f (psumL 3 g I ∘ₗ LinearMap.pi ![Q, R, P]) =
      ∑ k : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)),
        Sum.elim (cε 2) (Sum.elim (fun k => - cε 2 k) (fun k => - cε 2 k)) k *
        f (Sum.elim (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![P, Q + R])
          (Sum.elim (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![P, Q]) (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![P, R])) k) := by
  rw [sum_three, Fintype.sum_sum_type, Fintype.sum_sum_type, sum_two, sum_two, sum_two]
  simp only [Sum.elim_inl, Sum.elim_inr, psumL_pi]
  simp [thε, cε, Finset.sum_insert, add_comm P, add_assoc]
  ring

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem jetRd_scale_one {n m : ℕ} {K : Type} [Fintype K]
    {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ Xo.univ.t.G.left)} {ε : K → ℤ}
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) :
    scaleGen φ ε (unitΓ (1 : (Jet ℂ (Fin n × Fin g) m)ˣ)) τ = τ := by
  simp only [scaleGen, unitΓ, map_one, _root_.one_mul]

theorem jetRd_pe (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) {n' : ℕ}
    (φ : Fin 2 → Fin g → MvPolynomial (Fin n' × Fin g) ℂ)
    (B : Fin 2 → (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ i j, (Ideal.Quotient.mk _ (φ i j - MvPolynomial.C (MvPolynomial.constantCoeff (φ i j))) :
      Jet ℂ (Fin n' × Fin g) m) = jetN m (fun w => B i w j)) :
    Φ.toAnFr.JetRd m _ _ (pe y g Φ.jx e m φ) (fun k => psumL 2 g k ∘ₗ LinearMap.pi B) :=
  GlobalTheory.JetLinSub.jetRd_linSubst _ _ _ _ g Φ.toAnFr 2 n' m (LinearMap.pi B) (fun p => φ p.1 p.2)
    (fun p => (subst_X m _ p).trans (h p.1 p.2)) _ _ _ _ _ (he m).2

theorem jetRd_pe_two (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) {n' : ℕ}
    (φ φ' : Fin g → MvPolynomial (Fin n' × Fin g) ℂ)
    (B B' : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ j, (Ideal.Quotient.mk _ (φ j - MvPolynomial.C (MvPolynomial.constantCoeff (φ j))) :
      Jet ℂ (Fin n' × Fin g) m) = jetN m (fun w => B w j))
    (h' : ∀ j, (Ideal.Quotient.mk _ (φ' j - MvPolynomial.C (MvPolynomial.constantCoeff (φ' j))) :
      Jet ℂ (Fin n' × Fin g) m) = jetN m (fun w => B' w j)) :
    Φ.toAnFr.JetRd m _ _ (pe y g Φ.jx e m ![φ, φ']) (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![B, B']) :=
  jetRd_pe Φ e he m ![φ, φ'] ![B, B'] (Fin.forall_fin_two.2 ⟨h, h'⟩)

set_option backward.isDefEq.respectTransparency false in
theorem jetRd_cube {n : ℕ} (m : ℕ) (a b d : jO y g m n ⟶ Xo.univ.t.G)
    (P Q R : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.toAnFr.JetMap m a.left P)
    (hb : Φ.toAnFr.JetMap m b.left Q) (hd : Φ.toAnFr.JetMap m d.left R) :
    Φ.toAnFr.JetRd m _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
      (lift a (lift b d)).left) (fun I => psumL 3 g I ∘ₗ LinearMap.pi ![P, Q, R]) := by
  obtain ⟨-, hq2, e2⟩ := (GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ n m).2.2.1 b d Q R hb hd
  obtain ⟨hq1, e1⟩ := ha
  have hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (P (colsOf n g v)))
      (lift (Φ.e (Q (colsOf n g v))) (Φ.e (R (colsOf n g v))))).left) :=
    isHolFam_pullback_lift _ _ _ Xo.univ.t.G.hom (Xo.univ.t.G ⊗ Xo.univ.t.G).hom _ _ _ y.x
      (fun v => Over.w (Φ.e (P (colsOf n g v))))
      (fun v => Over.w (lift (Φ.e (Q (colsOf n g v))) (Φ.e (R (colsOf n g v))))) hq1 hq2
  have e3 : (lift a (lift b d)).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
      jetPt _ hq m := by
    apply pullback.hom_ext
    · rw [Category.assoc, jetPt_comp _ hq (pullback.fst _ _) _ hq1 (fun v => congrArg Over.Hom.left (lift_fst _ _)), ← e1]
      exact congrArg Over.Hom.left (lift_fst a (lift b d))
    · rw [Category.assoc, jetPt_comp _ hq (pullback.snd _ _) _ hq2 (fun v => congrArg Over.Hom.left (lift_snd _ _)), ← e2]
      exact congrArg Over.Hom.left (lift_snd a (lift b d))
  rw [e3]
  refine GlobalTheory.AnValJetGlob.jetRd_pullGen _ _ _ _ g Φ.toAnFr n m _ _ _ _ _ _ _ hq fun v => ?_
  have := GlobalTheory.cubical_reading_one E H Dw l Xo c y g ty el Φ (P (colsOf n g v)) (Q (colsOf n g v)) (R (colsOf n g v))
  have hv : LinearMap.pi ![P, Q, R] (colsOf n g v) = ![P (colsOf n g v), Q (colsOf n g v), R (colsOf n g v)] := by
    funext i
    fin_cases i <;> rfl
  simpa only [LinearMap.comp_apply, hv] using this

end Main

theorem second_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 3 × Fin g) m)ˣ, (u : Jet ℂ (Fin 3 × Fin g) m) = psJet m (anFB ty).ph2 ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift (jpt y g Φ.jx m (1 : Fin 3)) (lift (jpt y g Φ.jx m (2 : Fin 3)) (jpt y g Φ.jx m (0 : Fin 3)))).left) (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn g m ![1, 2] ((anFB ty).G.F j)]) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)])) (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ himm e he m
  refine ⟨1, by rw [show (anFB ty).ph2 = 1 from rfl, FBIdJet.psJet_one, Units.val_one], ?_⟩
  rw [jetRd_scale_one]
  have hp := (GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ 3 m).1
  have hL := jetRd_cube Φ m _ _ _ _ _ _ (hp 1) (hp 2) (hp 0)
  have hX : ∀ (i : Fin 3) (j : Fin g), (Ideal.Quotient.mk _ (MvPolynomial.X (i, j) -
      MvPolynomial.C (MvPolynomial.constantCoeff (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin g) ℂ))) :
      Jet ℂ (Fin 3 × Fin g) m) = jetN m (fun w => (LinearMap.proj i : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) w j) := by
    intro i j
    simp only [LinearMap.proj_apply]
    rw [jetN_coord]
    simp
  have hF : ∀ j, (Ideal.Quotient.mk _ (psIn g m ![(1 : Fin 3), 2] ((anFB ty).G.F j) -
      MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m ![(1 : Fin 3), 2] ((anFB ty).G.F j)))) :
      Jet ℂ (Fin 3 × Fin g) m) =
      jetN m (fun w => ((LinearMap.proj 1 : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) +
        (LinearMap.proj 2 : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) w j) := by
    intro j
    simp only [LinearMap.proj_apply, LinearMap.add_apply, Pi.add_apply]
    rw [show (anFB ty).G.F j = addF ℂ g j from rfl, psIn_add, jetN_coord_add]
    rfl
  have h1 := jetRd_pe_two Φ e he m (fun j => MvPolynomial.X ((0 : Fin 3), j))
    (fun j => psIn g m ![1, 2] ((anFB ty).G.F j)) (LinearMap.proj 0) (LinearMap.proj 1 + LinearMap.proj 2) (hX 0) hF
  have h2 := jetRd_pe_two Φ e he m (fun j => MvPolynomial.X ((0 : Fin 3), j))
    (fun j => MvPolynomial.X ((1 : Fin 3), j)) (LinearMap.proj 0) (LinearMap.proj 1) (hX 0) (hX 1)
  have h3 := jetRd_pe_two Φ e he m (fun j => MvPolynomial.X ((0 : Fin 3), j))
    (fun j => MvPolynomial.X ((2 : Fin 3), j)) (LinearMap.proj 0) (LinearMap.proj 2) (hX 0) (hX 2)
  have h2' := (jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ _ _ _ h2 h2).2.1
  have h3' := (jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ _ _ _ h3 h3).2.1
  have h23 := (jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ _ _ _ h2' h3').1
  have hR := (jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ _ _ _ h1 h23).1
  have hS := sameSum_of_jetMap Φ.toAnFr hL.1 hR.1 (count (LinearMap.proj 0) (LinearMap.proj 1) (LinearMap.proj 2))
  have hC := GlobalTheory.AnVal.JetCorr.corr_of_jetRd _ _ _ _ g Φ.toAnFr himm 3 m _ _ _ _ _ _ _ _ _ _ hL hR hS
  exact hC

end GlobalTheory.AnValSecondLaw
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFrame_second_partial_law_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 3 × Fin g) m)ˣ, (u : Jet ℂ (Fin 3 × Fin g) m) = psJet m (anFB ty).ph2 ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift (jpt y g Φ.jx m (1 : Fin 3)) (lift (jpt y g Φ.jx m (2 : Fin 3)) (jpt y g Φ.jx m (0 : Fin 3)))).left) (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn g m ![1, 2] ((anFB ty).G.F j)]) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)])) (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  atlas_forward_decl GlobalTheory.AnValSecondLaw.second_law
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetReading_linearSubstitution_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n n' m : ℕ) (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (sb : Fin n × Fin g → MvPolynomial (Fin n' × Fin g) ℂ), (∀ p, (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m) (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2)) → ∀ (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m (fun k => spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε (LB.pullGen L.L φ ε τ (spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m))) (fun k => Λ k ∘ₗ B) := by
  first | exact @GlobalTheory.JetLinSub.jetRd_linSubst | exact GlobalTheory.JetLinSub.jetRd_linSubst | (intros; apply GlobalTheory.JetLinSub.jetRd_linSubst <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal.Sym

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem tay_coord {g : ℕ} (k : Fin g) :
    tay (fun v : Fin g → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  have hc : ContDiffAt ℂ ω (fun v : Fin g → ℂ => v k) 0 := (contDiff_apply ℂ ℂ k).contDiffAt
  refine TCPf.eq_of_cc _ _ fun l => ?_
  rcases List.eq_nil_or_concat l with rfl | ⟨l', q, rfl⟩
  · simp only [List.foldr_nil, constantCoeff_tay, MvPowerSeries.constantCoeff_X]
    show lD _ 0 (Multiset.toList 0) = 0
    rw [Multiset.toList_zero]
    exact iteratedFDeriv_zero_apply _
  · rw [List.concat_eq_append, List.foldr_append, List.foldr_append]
    congr 2
    obtain ⟨a, j⟩ := q
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hc]
    have : (fun y : Fin g → ℂ => fderiv ℂ (fun v : Fin g → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j (1 : ℂ) : Fin g → ℂ) k := by
      funext y
      rw [(hasFDerivAt_apply (𝕜 := ℂ) k y).fderiv]
      rfl
    rw [this, TM.tay_const, MvPowerSeries.pderiv_X]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Pi.single_apply]

theorem psJet_X {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (s : κ) :
    psJet m (MvPowerSeries.X s : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X s) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem jetN_coord {n g : ℕ} (m : ℕ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j) = Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  unfold jetN jetOf
  show renN n g m (psJet m (tay (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) 0)) = _
  rw [tay_coord, psJet_X]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

def swapL (g : ℕ) : (Fin 2 → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Equiv.swap (0 : Fin 2) 1 i)

def swapI : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.finsetCongr (Equiv.swap (0 : Fin 2) 1)).trans Equiv.ulift.symm)

theorem psumL_swap (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) :
    psumL 2 g I ∘ₗ swapL g = psumL 2 g (swapI I) := by
  refine LinearMap.ext fun w => ?_
  simp [psumL, swapL, swapI, Equiv.finsetCongr_apply]

theorem cε_swap (I : ULift.{0} (Finset (Fin 2))) : cε 2 (swapI I) = cε 2 I := by
  simp [cε, swapI, Equiv.finsetCongr_apply]

theorem jetMap_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n m : ℕ} {ψ ψ' : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) (h' : Φ.JetMap m ψ' Λ) : ψ = ψ' := by
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := h'
  rfl

theorem sy_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m (anFB ty).sy ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m) (scaleGen _ _ (unitΓ u⁻¹) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e he m
  refine ⟨1, ?_, ?_⟩
  · show (1 : Jet ℂ (Fin 2 × Fin g) m) = psJet m 1
    rw [← MvPolynomial.coe_one, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, map_one]
  have hR := (he m).2
  have hS := GlobalTheory.T.jetReading_linearSubstitution_points _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 2 m (swapL g)
    (fun p : Fin 2 × Fin g => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] :
      Fin 2 → Fin g → MvPolynomial (Fin 2 × Fin g) ℂ) p.1 p.2) (by
      rintro ⟨i, j⟩
      rw [psJet_X]
      refine Eq.trans ?_ (jetN_coord m (Equiv.swap (0 : Fin 2) 1 i) j).symm
      show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
      fin_cases i <;> simp) _ _ _ _ _ hR
  have hC := GlobalTheory.T.corr_of_jets_of_analytic_frame_products _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hI 2 m _ _ _ _ _ _ _ _ _ _ hR hS (by
    intro ψ
    refine (Fintype.sum_equiv swapI _ _ fun I => ?_).symm
    have h1 := hS.1 I
    beta_reduce at h1 ⊢
    rw [psumL_swap] at h1
    rw [jetMap_unique _ h1 (hR.1 (swapI I)), cε_swap])
  intro j j' h1 h2 h3
  refine (hC j j' h1 h2 h3).trans ?_
  congr 1
  show _ = res le_top (unitΓ (1 : (Jet ℂ (Fin 2 × Fin g) m)ˣ)⁻¹) * _
  rw [inv_one, unitΓ, map_one]
  have : ∀ (X : Scheme.{0}) (U : X.Opens), res (le_top : U ≤ ⊤) (1 : Γ(X, ⊤)ˣ) = 1 := fun X U => map_one _
  rw [this]
  exact (_root_.one_mul _).symm

end GlobalTheory.AnVal.Sym
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFrame_symmetry_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m (anFB ty).sy ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m) (scaleGen _ _ (unitΓ u⁻¹) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  atlas_forward_decl GlobalTheory.AnVal.Sym.sy_trivial
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] [StarRing (𝓞 E)] {y : FrPt Xo c ℂ} {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem isFrame_of_isAnE (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) :
    IsFrame y g Φ.jx (anFB ty).G.F (anFB ty).A.act (anFB ty).ph1 (anFB ty).ph2 (anFB ty).sy (anFB ty).ad e := by
  have hI := GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ
  exact ⟨fun m => (he m).1, GlobalTheory.T.analyticFrame_first_partial_law_trivial E H Dw l Xo c y g ty el Φ hI e he,
    GlobalTheory.T.analyticFrame_second_partial_law_trivial E H Dw l Xo c y g ty el Φ hI e he, GlobalTheory.T.analyticFrame_symmetry_trivial E H Dw l Xo c y g ty el Φ hI e he,
    GlobalTheory.T.analyticFrame_adjointness_series_trivial E H Dw l Xo c y g ty el Φ hI hst e he⟩

theorem isGerm_tay_of_rd (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (wP : PrimTy H Xo) (hw : IsPrim wP) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ)
    (hF : Φ.toAnFr.Rd k F θ) : IsGerm y g Φ.jx (anFB ty).A.act e wP k F (tay θ 0) := by
  simp only [IsGerm]
  intro m
  have hJ : Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) :=
    (GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ 1 m).2.2.2.2
  obtain ⟨τ, -, hτ⟩ := GlobalTheory.T.exists_generator_jet_reading _ _ _ _ _ Φ.toAnFr 1 m (Fin 1) (fun _ => (Φ.jx m).left) (fun _ => (k : ℤ))
    (fun _ => LinearMap.proj 0) (fun _ => hJ)
  obtain ⟨F', hpull, hval⟩ := GlobalTheory.T.isValueAt_jetPoint_cmFrame_section E H Dw l Xo c y g ty el Φ m k F θ τ hF hτ
  have hc := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ) e wP he hw).1 m k τ hτ
  exact ⟨F', τ, hpull, hc, hval⟩

noncomputable def AnPt.chartOf (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e)
    (wP : PrimTy H Xo) (hw : IsPrim wP) : ChartAt Xo c y where
  d := g
  B := anFB ty
  uvec := anUvec el
  x := Φ.jx
  e := e
  wP := wP
  h := 0
  chart := GlobalTheory.T.cmFrame_exponential_jets_isChart E H Dw l Xo c y g ty el Φ
  frame := isFrame_of_isAnE Φ hst e he
  prim := hw
  gauge := anFB_canon ty
  rig0 := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ) e wP he hw).2

end

theorem rename_cast_refl {g : ℕ} (f : MvPowerSeries (Fin 1 × Fin g) ℂ) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) f = f := by
  have h : (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) = id := funext fun p => rfl
  rw [h]
  exact MvPowerSeries.rename_id_apply f

theorem exists_analytic_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hst
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_analyticFrame_jetPair_isAnE E H Dw l Xo c y g ty el Φ
  obtain ⟨wP, hw⟩ := (GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ).1
  refine ⟨AnPt.chartOf Φ hst e he wP hw, rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    first
      | rfl
      | simp [AnPt.chartOf, anFB, Germ.FB.triv, addFGLaw]
  · intro ℓ i'
    first
      | rfl
      | simp [AnPt.chartOf, anUvec, Pi.single_apply, eq_comm]
      | (simp only [AnPt.chartOf, anUvec]; done)
  · intro k F θ hF
    show IsGerm y g Φ.jx (anFB ty).A.act e wP k F
      (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) (tay θ 0))
    rw [rename_cast_refl]
    exact isGerm_tay_of_rd Φ e he wP hw k F θ hF

end GlobalTheory.AnVal
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_biextension_chart_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  atlas_forward_decl GlobalTheory.AnVal.exists_analytic_chart
end
