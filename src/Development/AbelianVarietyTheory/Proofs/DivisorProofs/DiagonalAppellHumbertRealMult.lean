import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalReal
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplication
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyPositivePolarizationProjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import BuildAid.ForwardExisting

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_diagonal_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ (c' : 𝔠.elt) (l l' : u.Λ), ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (((e j ((c' : F) / (2 * (c : F))) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = n := by
  first | exact @GlobalTheory.RiemInt.riemannForm_int | exact GlobalTheory.RiemInt.riemannForm_int | (intros; apply GlobalTheory.RiemInt.riemannForm_int <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.TorusRM GlobalTheory.RosatiAH GlobalTheory.AppellHumbertTrivial in

theorem GlobalTheory.RosatiAH.hermForm_prod_halfDiag : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ (U : HolUnif (X.A ⊗ X.A) (X.P c) (Module.finrank ℚ F + Module.finrank ℚ F))
      (H : Matrix (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) ℂ)
      (χ' : U.Λ → ℂ), (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → GlobalTheory.TorusRM.IsFactorAH U H χ' →
    ∀ x y x' y' : Fin (Module.finrank ℚ F) → ℂ,
      hermForm H (Fin.append x y) (Fin.append x' y') =
        (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x y' + hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) y x') / 2 := by
  intro F _ _ _ 𝔠 X c _ u e hu h χ hAH U H χ' hexU hFU
  set Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ := Matrix.diagonal fun j ↦ (h j : ℂ) with hHm
  obtain ⟨U0, hU0⟩ := GlobalTheory.T.product_abelian_uniformization X.A X.ab (X.diag c) _ u
  have hAb2 := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  obtain ⟨U2, H2, χ2, hex2', hF2⟩ := GlobalTheory.T.exists_appell_humbert_line_bundle (X.A ⊗ X.A) hAb2 _ _ U0 (X.P ((2 : 𝓞 F) • c)) (X.isLB _)
  have hex2 : ∀ x y, U2.ex (Fin.append x y) = lift (u.ex x) (u.ex y) := fun x y => by rw [hex2']; exact hU0 x y
  have hswap : ∀ {c' : 𝔠.elt} (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F)),
      (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) →
      ∀ v, U.ex (fswap _ v) = U.ex v ≫ lift (snd X.A X.A) (fst X.A X.A) := by
    intro c' U hex v
    rw [eq_append v, fswap_append, hex, hex]
    simp
  have hS : ∀ {c' : 𝔠.elt} (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F)) H χ',
      (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → IsFactorAH U H χ' →
      ∀ x y x' y', hermForm H (Fin.append x y) (Fin.append x' y') = hermForm H (Fin.append y x) (Fin.append y' x') := by
    intro c' U H χ' hex hF x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P c') (X.P c') (X.isLB c') (X.isLB c') _ _ U U H χ' H χ'
      hF hF (lift (snd X.A X.A) (fst X.A X.A)) (fswap _) (hswap U hex) (X.symm c') (Fin.append x y) (Fin.append x' y')
    rwa [fswap_append, fswap_append] at this
  have h2F : (((2 : 𝓞 F)) : F) = 2 := by norm_cast
  have h2 : (dmul fun j => ((e j (((2 : 𝓞 F) : F)) : ℝ) : ℂ)) = (2 : ℂ) • LinearMap.id := by
    refine LinearMap.ext fun z => funext fun k => ?_
    simp only [dmul_apply, h2F, map_ofNat, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  have hmul2 : ∀ v, U.ex (fmul (dmul fun j => ((e j (((2 : 𝓞 F) : F)) : ℝ) : ℂ)) v) =
      U2.ex v ≫ lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act (2 : 𝓞 F)) := by
    intro v
    rw [eq_append v, fmul_append, hex2, hexU, dmul_apply, hu]
    simp
  have hM2 : ∀ x y x' y', hermForm H2 (Fin.append x y) (Fin.append x' y') =
      hermForm H (Fin.append x ((2 : ℂ) • y)) (Fin.append x' ((2 : ℂ) • y')) := by
    intro x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P ((2 : 𝓞 F) • c)) (X.P c) (X.isLB _) (X.isLB c) _ _ U2 U H2 χ2
      H χ' hF2 hFU (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act (2 : 𝓞 F))) (fmul (dmul fun j => ((e j (((2 : 𝓞 F) : F)) : ℝ) : ℂ)))
      hmul2 (X.smul (2 : 𝓞 F) c) (Fin.append x y) (Fin.append x' y')
    rwa [fmul_append, fmul_append, h2] at this
  have hSc := hS U H χ' hexU hFU
  have hS2 := hS U2 H2 χ2 hex2 hF2
  have hA : ∀ x x', hermForm H (Fin.append x 0) (Fin.append x' 0) = 0 := by
    intro x x'
    have e1 := hM2 x 0 x' 0
    have e2 := hS2 x 0 x' 0
    have e3 := hM2 0 x 0 x'
    have e4 := hSc x 0 x' 0
    simp only [smul_zero] at e1
    have e5 : Fin.append (0 : Fin (Module.finrank ℚ F) → ℂ) ((2 : ℂ) • x) = (2 : ℂ) • Fin.append 0 x := by
      rw [← append_smul, smul_zero]
    have e6 : Fin.append (0 : Fin (Module.finrank ℚ F) → ℂ) ((2 : ℂ) • x') = (2 : ℂ) • Fin.append 0 x' := by
      rw [← append_smul, smul_zero]
    rw [e5, e6, hermForm_smul_left, hermForm_smul_right] at e3
    have hs : (star (2 : ℂ)) = 2 := by simp
    rw [hs] at e3
    have : hermForm H (Fin.append x 0) (Fin.append x' 0) =
        4 * hermForm H (Fin.append x 0) (Fin.append x' 0) := by
      calc _ = hermForm H2 (Fin.append x 0) (Fin.append x' 0) := e1.symm
        _ = hermForm H2 (Fin.append 0 x) (Fin.append 0 x') := e2
        _ = 2 * (2 * hermForm H (Fin.append 0 x) (Fin.append 0 x')) := e3
        _ = 4 * hermForm H (Fin.append x 0) (Fin.append x' 0) := by rw [e4]; ring
    linear_combination (-1/3 : ℂ) * this
  have hA2 : ∀ y y', hermForm H (Fin.append 0 y) (Fin.append 0 y') = 0 := by
    intro y y'
    rw [← hSc y 0 y' 0]
    exact hA y y'
  have hBC : ∀ x y', hermForm H (Fin.append 0 x) (Fin.append y' 0) = hermForm H (Fin.append x 0) (Fin.append 0 y') :=
    fun x y' => (hSc x 0 0 y').symm
  have hdiag : ∀ z, U.ex (fdiag _ z) = u.ex z ≫ lift (𝟙 X.A) (𝟙 X.A) := by
    intro z
    rw [fdiag_apply, hexU]
    simp
  have hdLB : (X.diag c).IsLB := LB.isLB_pull (X.isLB c) _
  have hD := hermForm_eq_of_lbIso_pull X.A (X.A ⊗ X.A) (X.diag c) (X.P c) hdLB (X.isLB c) _ _ u U Hm χ H χ'
    (isFactorAH_of_isAH hAH) hFU (lift (𝟙 X.A) (𝟙 X.A)) (fdiag _) hdiag (by unfold Obj.diag; exact GlobalTheory.lbIso_refl hdLB)
  have hB : ∀ z w, hermForm Hm z w = 2 * hermForm H (Fin.append z 0) (Fin.append 0 w) := by
    intro z w
    rw [hD, fdiag_apply, fdiag_apply, herm_append H z z w w, hA, hA2, hBC]
    ring
  intro x y x' y'
  rw [hB, hB, herm_append H x y x' y', hA, hA2, hBC]
  ring
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_real_mult_appell_humbert : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ (U : HolUnif (X.A ⊗ X.A) (X.P c) (Module.finrank ℚ F + Module.finrank ℚ F))
      (H : Matrix (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) ℂ)
      (χ' : U.Λ → ℂ), (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → GlobalTheory.TorusRM.IsFactorAH U H χ' →
    ∀ x y x' y' : Fin (Module.finrank ℚ F) → ℂ,
      hermForm H (Fin.append x y) (Fin.append x' y') =
        (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x y' + hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) y x') / 2 := by
  atlas_forward_decl GlobalTheory.RosatiAH.hermForm_prod_halfDiag
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.PullHermitian in

theorem GlobalTheory.TorusRM.char_axis_eq_one_of_herm_axis_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left), L.IsLB → HasGen (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∀ (U : HolUnif (A ⊗ A) L (g + g)) (H : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) (χ' : U.Λ → ℂ),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → GlobalTheory.TorusRM.IsFactorAH U H χ' →
    (∀ z w : Fin g → ℂ, hermForm H (Fin.append z 0) (Fin.append w 0) = 0) →
    ∀ (m : U.Λ) (l : Fin g → ℂ), (m : Fin (g + g) → ℂ) = Fin.append l 0 → χ' m = 1 := by
  intro A _ L₀ g u L hL ht0 U H χ' hU hF hH0 m l hm
  set φ := (lift (𝟙 A) (1 : A ⟶ A)).left with hφ
  obtain ⟨t, ht⟩ := ht0
  have e0 : u.ex 0 = 1 := by
    have h := u.ex_add 0 0
    simpa using h
  have comp1 : ∀ {X : Over (Sp ℂ)} (f : X ⟶ A), f ≫ (1 : A ⟶ A) = 1 := fun f => by
    rw [Hom.one_def, Hom.one_def]; simp
  have hx : ∀ z, (U.ex (Fin.append z 0)).left = (u.ex z).left ≫ φ := fun z => by
    rw [hU, e0, hφ, ← Over.comp_left, comp_lift, Category.comp_id, comp1]
  have hmem : ∀ l' : Fin g → ℂ, Fin.append l' 0 ∈ U.Λ ↔ l' ∈ u.Λ := by
    intro l'
    rw [← U.ker, ← u.ker, hU, e0]
    constructor
    · intro h
      have := congrArg (· ≫ fst A A) h
      simpa using this
    · intro h
      rw [h]
      first | simp | (ext <;> simp) | rfl
  have hper : ∀ (l' : u.Λ) z, u.ex (z + l') = u.ex z := fun l' z => by
    rw [u.ex_add, (u.ker l').2 l'.2, _root_.mul_one]
  have happ : ∀ z w : Fin g → ℂ, Fin.append z 0 + Fin.append w 0 = Fin.append (z + w) (0 : Fin g → ℂ) := by
    intro z w
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.add_apply]
    · simp only [Fin.append_right, Pi.add_apply, Pi.zero_apply, add_zero]
  have hapd : Differentiable ℂ (fun z : Fin g → ℂ => Fin.append z (0 : Fin g → ℂ)) := by
    refine differentiable_pi.2 fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using differentiable_apply j
    · simpa only [Fin.append_right, Pi.zero_apply] using differentiable_const (0 : ℂ)
  set V : L.ι → Set (Fin g → ℂ) := fun p => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull φ).U (fun _ => p)} with hV
  have hVsub' : ∀ p z, z ∈ V p → ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ L.U p := fun p z hz q hq =>
    Set.mem_iInter.1 (hz hq) PUnit.unit
  have hVsub : ∀ p z, z ∈ V p → ⊤ ≤ (U.ex (Fin.append z 0)).left ⁻¹ᵁ L.U p := fun p z hz => by
    rw [hx]; exact hVsub' p z hz
  have hVof : ∀ p z, ⊤ ≤ (U.ex (Fin.append z 0)).left ⁻¹ᵁ L.U p → z ∈ V p := fun p z h =>
    wchart_of (u.ex z).left L φ p (hx z ▸ h)
  obtain ⟨r, hr, hrφ⟩ := exists_glue V
    (fun p => (u.hol _ 0).1)
    (fun z => by
      obtain ⟨p, hp⟩ := exists_chart (U.ex (Fin.append z 0)).left hL
      exact ⟨p, hVof p z hp⟩)
    (fun p z => valAt' (u.ex z).left ((L.pull φ).U (fun _ => p)) (t.s (fun _ => p)).val /
      U.fr p (Fin.append z 0))
    (fun p => by
      have d1 := (u.hol ((L.pull φ).U (fun _ => p)) (t.s (fun _ => p)).val).2
      have d2 : DifferentiableOn ℂ (fun z => U.fr p (Fin.append z 0)) (V p) := (U.fr_hol p).comp (s := V p) hapd.differentiableOn fun z hz => hVsub p z hz
      simp only [div_eq_mul_inv]
      exact d1.mul (d2.inv fun z hz => U.fr_ne p _ (hVsub p z hz)))
    (fun p q z hp hq => by
      have hpq := inf_of (u.ex z).left hp hq
      have h1 := ht (fun _ => p) (fun _ => q)
      have h2 := congrArg (unitVal (u.ex z).left hpq) h1
      rw [map_mul, unitVal_res (u.ex z).left _ hpq hp, unitVal_res (u.ex z).left _ hpq hq] at h2
      have h3 := unitVal_linComb (u.ex z).left L φ 1 p q hpq (inf_of _ (hVsub' p z hp) (hVsub' q z hq))
      have h4 := U.fr_compat p q (Fin.append z 0) (inf_of _ (hVsub p z hp) (hVsub q z hq))
      rw [hx] at h4
      rw [valAt'_eq_unitVal _ hp, valAt'_eq_unitVal _ hq, h4,
        valAt'_eq_unitVal _ (inf_of _ (hVsub' p z hp) (hVsub' q z hq)), h2, h3]
      have h5 := U.fr_ne q _ (hVsub q z hq)
      simp only [Units.val_mul, zpow_one]
      field_simp)
  haveI := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0
    (fun l' => χ' ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩) r Matrix.isHermitian_zero
    (fun l' => hF.2.1 _) hr
    (fun z => by
      obtain ⟨p, hp⟩ := exists_chart (U.ex (Fin.append z 0)).left hL
      have hp' := hVof p z hp
      rw [hrφ p z hp', valAt'_eq_unitVal _ hp']
      exact div_ne_zero (Units.ne_zero _) (U.fr_ne p _ hp))
    (fun l' z => by
      obtain ⟨p, hp⟩ := exists_chart (U.ex (Fin.append z 0)).left hL
      have hz := hVof p z hp
      have hz' : z + l' ∈ V p := by
        show ⊤ ≤ (u.ex (z + l')).left ⁻¹ᵁ _
        rw [hper]; exact hz
      rw [hrφ p _ hz', hrφ p z hz, hper]
      have hf := hF.2.2 ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩ p (Fin.append z 0) hp
      have e1 : Fin.append z 0 ⬝ᵥ H.mulVec (star (Fin.append (l' : Fin g → ℂ) 0)) = 0 := hH0 z l'
      have e2 : Fin.append (l' : Fin g → ℂ) 0 ⬝ᵥ H.mulVec (star (Fin.append (l' : Fin g → ℂ) 0)) = 0 :=
        hH0 l' l'
      simp only [e1, e2, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one, happ] at hf
      have hc : χ' ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩ ≠ 0 :=
        norm_ne_zero_iff.1 (by rw [hF.2.1]; exact one_ne_zero)
      have h6 := U.fr_ne p _ (hVsub p _ hz')
      simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero, mul_zero, add_zero, Complex.exp_zero,
        _root_.mul_one]
      rw [hf]
      field_simp)
  have hm' : m = ⟨Fin.append l 0, hm ▸ m.2⟩ := Subtype.ext hm
  rw [hm']
  exact key.2.1 ⟨l, (hmem l).1 (hm ▸ m.2)⟩
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_torus_factor_appell_humbert : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left), L.IsLB → HasGen (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∀ (U : HolUnif (A ⊗ A) L (g + g)) (H : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) (χ' : U.Λ → ℂ),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → GlobalTheory.TorusRM.IsFactorAH U H χ' →
    (∀ z w : Fin g → ℂ, hermForm H (Fin.append z 0) (Fin.append w 0) = 0) →
    ∀ (m : U.Λ) (l : Fin g → ℂ), (m : Fin (g + g) → ℂ) = Fin.append l 0 → χ' m = 1 := by
  atlas_forward_decl GlobalTheory.TorusRM.char_axis_eq_one_of_herm_axis_zero
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory
namespace TorusPullFrame

open GlobalTheory.PullHermitian

variable {X Y : Scheme.{0}}

lemma chart_pull_iff (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) :=
  ⟨fun h _ hp => Set.mem_iInter.1 (h hp) PUnit.unit, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩

lemma le_left {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ U :=
  h.trans (fun _ hp => And.left hp)

lemma le_right {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ V :=
  h.trans (fun _ hp => And.right hp)

lemma valAt'_pull_g (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (i j : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull f).U i ⊓ (L.pull f).U j)) :
    valAt' x ((L.pull f).U i ⊓ (L.pull f).U j) ((L.pull f).g i j).val =
      valAt' (x ≫ f) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
        (L.g (i PUnit.unit) (j PUnit.unit)).val := by
  have hi := (chart_pull_iff x L f i).1 (le_left h)
  have hj := (chart_pull_iff x L f j).1 (le_right h)
  rw [valAt'_eq_unitVal x h, valAt'_eq_unitVal _ (inf_of _ hi hj)]
  have := unitVal_linComb x L f 1 (i PUnit.unit) (j PUnit.unit) h (inf_of _ hi hj)
  exact congrArg Units.val (this.trans (zpow_one _))

lemma differentiable_append {g : ℕ} (x₀ : Fin g → ℂ) :
    Differentiable ℂ (fun z : Fin g → ℂ => (Fin.append z x₀ : Fin (g + g) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [Fin.append_left]; exact differentiable_apply a
  · simp only [Fin.append_right]; exact differentiable_const _

theorem exists_holUnif_pull_right : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left) (U : HolUnif (A ⊗ A) L (g + g)),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → ∀ x₀ : Fin g → ℂ,
    ∃ u' : HolUnif A (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left) g, u'.ex = u.ex ∧
      (∀ j z, (⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left).U j ↔
        ⊤ ≤ (U.ex (Fin.append z x₀)).left ⁻¹ᵁ L.U (j PUnit.unit))) ∧
      ∀ j z, u'.fr j z = U.fr (j PUnit.unit) (Fin.append z x₀) := by
  intro A _ L₀ g u L U hU x₀
  have key : ∀ z, u.ex z ≫ lift (𝟙 A) (toUnit A ≫ u.ex x₀) = U.ex (Fin.append z x₀) := by
    intro z
    rw [hU, comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _), Category.id_comp]
  have keyl : ∀ z, (u.ex z).left ≫ (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left =
      (U.ex (Fin.append z x₀)).left := fun z => by rw [← Over.comp_left, key]
  have hch : ∀ j z, (⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left).U j ↔
      ⊤ ≤ (U.ex (Fin.append z x₀)).left ⁻¹ᵁ L.U (j PUnit.unit)) := fun j z =>
    (chart_pull_iff _ L _ j).trans (iff_of_eq (by rw [keyl z]))
  refine ⟨⟨u.ex, u.ex_add, u.ex_onto, u.Λ, u.ker, u.discrete, u.full, u.hol,
      fun j z => U.fr (j PUnit.unit) (Fin.append z x₀),
      fun j => (U.fr_hol (j PUnit.unit)).comp (differentiable_append x₀).differentiableOn
        (fun z hz => (hch j z).1 hz),
      fun j z hz => U.fr_ne _ _ ((hch j z).1 hz),
      fun i j z h => by
        have hi := (hch i z).1 (le_left h)
        have hj := (hch j z).1 (le_right h)
        show U.fr (i PUnit.unit) (Fin.append z x₀) = _ * U.fr (j PUnit.unit) (Fin.append z x₀)
        rw [valAt'_pull_g _ L _ i j h, keyl z]
        exact U.fr_compat _ _ _ (inf_of _ hi hj)⟩, rfl, hch, fun _ _ => rfl⟩

end TorusPullFrame
end GlobalTheory
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_uniformization_pullback : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left) (U : HolUnif (A ⊗ A) L (g + g)),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → ∀ x₀ : Fin g → ℂ,
    ∃ u' : HolUnif A (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left) g, u'.ex = u.ex ∧
      (∀ j z, (⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left).U j ↔
        ⊤ ≤ (U.ex (Fin.append z x₀)).left ⁻¹ᵁ L.U (j PUnit.unit))) ∧
      ∀ j z, u'.fr j z = U.fr (j PUnit.unit) (Fin.append z x₀) := by
  atlas_forward_decl GlobalTheory.TorusPullFrame.exists_holUnif_pull_right
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_nonvanishing_bundle_generated : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M : LB A.left), M.IsLB → ∀ (g : ℕ) (u : HolUnif A M g) (θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ →
    (∀ z, θ z ≠ 0) →
    (∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) →
    HasGen M := by
  first | exact @GlobalTheory.HolUnifSec.hasGen_of_periodic | exact GlobalTheory.HolUnifSec.hasGen_of_periodic | (intros; apply GlobalTheory.HolUnifSec.hasGen_of_periodic <;> assumption)
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_positive_polarization_projective : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → IsProjOver X.A.hom := by
  first | exact @GlobalTheory.RealMult.ProjOverC.isProjOver_A | exact GlobalTheory.RealMult.ProjOverC.isProjOver_A | (intros; apply GlobalTheory.RealMult.ProjOverC.isProjOver_A <;> assumption)
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.RiemFormKer.smul_mem_lattice : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ x : Fin (Module.finrank ℚ F) → ℂ, (∀ l : u.Λ, ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (x j * starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im = 2 * n) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → (fun j ↦ (e j (a : F) : ℂ) * x j) ∈ u.Λ := by
  intro F _ _ _ 𝔠 X c hc u e hu h χ hAH x hx a ha
  obtain ⟨U0, hU0⟩ := GlobalTheory.T.product_abelian_uniformization X.A X.ab (X.diag c) _ u
  have hAb2 := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  obtain ⟨U, H, χ', hUex, hF⟩ := GlobalTheory.T.exists_appell_humbert_line_bundle (X.A ⊗ X.A) hAb2 _ _ U0 (X.P c) (X.isLB c)
  have hex : ∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y) := fun x y => by rw [hUex]; exact hU0 x y
  have hb := GlobalTheory.T.torus_real_mult_appell_humbert F 𝔠 X c hc u e hu h χ hAH U H χ' hex hF
  have hχ := GlobalTheory.T.product_torus_factor_appell_humbert X.A (X.diag c) _ u (X.P c) (X.isLB c) (X.rig₂ c) U H χ' hex hF
    (fun z w => by rw [hb]; simp [hermForm])
  obtain ⟨u', hu'ex, hu'ch, hu'fr⟩ := GlobalTheory.T.translated_uniformization_pullback X.A (X.diag c) _ u (X.P c) U hex x
  have hgen : HasGen ((X.P c).pull (lift (𝟙 X.A) (toUnit X.A ≫ u.ex x)).left) := by
    refine GlobalTheory.T.theta_nonvanishing_bundle_generated X.A X.ab (GlobalTheory.T.totally_positive_polarization_projective F 𝔠 X c hc) _ (LB.isLB_pull (X.isLB c) _) _ u'
      (fun z => Complex.exp (Real.pi * hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) z x / 2)) ?_
      (fun z => Complex.exp_ne_zero _) ?_
    · simp only [hermForm, dotProduct]
      fun_prop
    · intro l hl i z hz
      have hlu : l ∈ u.Λ := by rw [← u.ker, ← hu'ex]; exact (u'.ker l).2 hl
      have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
      have hm : Fin.append l (0 : Fin (Module.finrank ℚ F) → ℂ) ∈ U.Λ := by
        rw [← U.ker, hex, (u.ker l).2 hlu, ← h0, ← hex]
        have hz0 : Fin.append (0 : Fin (Module.finrank ℚ F) → ℂ) (0 : Fin (Module.finrank ℚ F) → ℂ) = 0 := by
          funext k
          refine Fin.addCases (fun k => ?_) (fun k => ?_) k
          · simp only [Fin.append_left, Pi.zero_apply]
          · simp only [Fin.append_right, Pi.zero_apply]
        rw [hz0]
        exact (U.ker 0).2 U.Λ.zero_mem
      have hz' : ⊤ ≤ (U.ex (Fin.append z x)).left ⁻¹ᵁ (X.P c).U (i PUnit.unit) := (hu'ch i z).1 hz
      have happ : Fin.append z x + Fin.append l 0 = Fin.append (z + l) x := by
        funext k
        refine Fin.addCases (fun k => ?_) (fun k => ?_) k
        · simp only [Pi.add_apply, Fin.append_left]
        · simp only [Pi.add_apply, Fin.append_right, Pi.zero_apply, add_zero]
      have e1 : hermForm H (Fin.append z x) (Fin.append l 0) =
          hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l / 2 := by
        rw [hb]; simp [hermForm]
      have e2 : hermForm H (Fin.append l 0) (Fin.append l 0) = 0 := by
        rw [hb]; simp [hermForm]
      have hf : U.fr (i PUnit.unit) (Fin.append z x) = Complex.exp (Real.pi *
          (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l / 2)) * U.fr (i PUnit.unit) (Fin.append (z + l) x) := by
        have h3 := hF.2.2 ⟨_, hm⟩ (i PUnit.unit) (Fin.append z x) hz'
        rw [hχ ⟨_, hm⟩ l rfl, _root_.one_mul] at h3
        dsimp only at h3
        rw [h3, happ]
        congr 2
        rw [show (Fin.append z x ⬝ᵥ H.mulVec (star (Fin.append l 0))) = hermForm H (Fin.append z x) (Fin.append l 0) from rfl,
          show (Fin.append l 0 ⬝ᵥ H.mulVec (star (Fin.append l 0))) = hermForm H (Fin.append l 0) (Fin.append l 0) from rfl,
          e1, e2]
        ring
      obtain ⟨n, hn⟩ := hx ⟨l, hlu⟩
      have hs : hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l = ∑ j, (h j : ℂ) * (x j * starRingEnd ℂ (l j)) := by
        simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hsw : hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) l x =
          starRingEnd ℂ (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l) := by
        simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def, map_sum, map_mul,
          Complex.conj_conj, Complex.conj_ofReal]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hadd : hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) (z + l) x =
          hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) z x + hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) l x := by
        simp only [hermForm, add_dotProduct]
      have hc : starRingEnd ℂ (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l) =
          hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l - 4 * n * Complex.I := by
        rw [hs]
        apply Complex.ext
        · simp
        · simp only [Complex.conj_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]
          rw [hn]
          simp
          ring
      rw [hu'fr, hu'fr, hf]
      beta_reduce
      rw [← _root_.mul_assoc, ← Complex.exp_add]
      congr 1
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-n, ?_⟩
      rw [hadd, hsw, hc]
      push_cast
      ring
  have hgen2 : HasGen ((X.P c).pull (lift (fst X.A (𝟙_ (Over (Sp ℂ)))) (snd X.A (𝟙_ (Over (Sp ℂ))) ≫ u.ex x)).left) := by
    obtain ⟨t, ht⟩ := hgen
    have hm : lift (fst X.A (𝟙_ (Over (Sp ℂ)))) (snd X.A (𝟙_ (Over (Sp ℂ))) ≫ u.ex x) =
        fst X.A (𝟙_ (Over (Sp ℂ))) ≫ lift (𝟙 X.A) (toUnit X.A ≫ u.ex x) := by
      ext
      · simp
      · have hs : snd X.A (𝟙_ (Over (Sp ℂ))) = fst X.A (𝟙_ (Over (Sp ℂ))) ≫ toUnit X.A := toUnit_unique _ _
        simp [hs]
    rw [hm, Over.comp_left]
    exact ⟨LB.pullGen _ (fun _ : PUnit => _) (fun _ => 1) t (fst X.A _).left, DVR.pullGen_isGen _ _ _ t ht _⟩
  have h1 := X.ker c (𝟙_ _) (u.ex x) hgen2 a ha
  rw [← u.ker, hu a x]
  exact h1
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_diagonal_real_dual : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ x : Fin (Module.finrank ℚ F) → ℂ, (∀ l : u.Λ, ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (x j * starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im = 2 * n) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → (fun j ↦ (e j (a : F) : ℂ) * x j) ∈ u.Λ := by
  atlas_forward_decl GlobalTheory.RiemFormKer.smul_mem_lattice
end

section
section
open NumberField GlobalTheory.RealMult

namespace GlobalTheory.RealMult

theorem exists_trace_pairing_of_integral : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (h : Fin (Module.finrank ℚ F) → ℝ),
    (∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ Λ → (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ Λ) →
    (∀ (c' : 𝔠.elt) (l l' : Λ), ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (((e j ((c' : F) / (2 * (c : F))) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = n) →
    ∃ P : Λ → Λ → F, (∀ l l' : Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : Λ, P l l' ∈ dualLat 𝔠) := by
  intro F _ _ _ 𝔠 c hc Λ e h hΛ hint
  have hc0 : (c : F) ≠ 0 := by
    intro h0
    have := hc (e ⟨0, Module.finrank_pos⟩)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  let G : Λ → Λ → Fin (Module.finrank ℚ F) → ℝ := fun l l' j =>
    h j * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j)).im
  have conv : ∀ (t : F) (l l' : Λ), (∑ j, (h j : ℂ) * (((e j t : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = ∑ j, e j t * G l l' j := by
    intro t l l'
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [G]
    rw [Complex.im_ofReal_mul, mul_assoc, Complex.im_ofReal_mul]; ring
  have rat : ∀ (l l' : Λ) (t : F), ∃ q : ℚ, (q : ℝ) = ∑ j, e j t * G l l' j := by
    intro l l' t
    obtain ⟨y, hy0, hyi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic t)).exists_integral_multiple
    let x : 𝓞 F := ⟨y • t, hyi⟩
    have hx : ((x : 𝓞 F) : F) = (y : F) * t := by
      show y • t = _
      rw [zsmul_eq_mul]
    let c' : 𝔠.elt := ⟨((2 : 𝓞 F) * x) • (c : F), Submodule.smul_mem _ _ c.2⟩
    obtain ⟨k, hk⟩ := hint c' l l'
    have hq : (c' : F) / (2 * c) = (y : F) * t := by
      show (((2 : 𝓞 F) * x) • (c : F)) / (2 * c) = _
      rw [Algebra.smul_def, map_mul, map_ofNat]
      change 2 * ((x : 𝓞 F) : F) * (c : F) / (2 * c) = _
      rw [hx]
      field_simp
    rw [conv, hq] at hk
    refine ⟨(k : ℚ) / y, ?_⟩
    have hsum : ∑ j, e j ((y : F) * t) * G l l' j = (y : ℝ) * ∑ j, e j t * G l l' j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_intCast]; ring
    rw [hsum] at hk
    have hy : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
    push_cast
    rw [← hk]
    field_simp
  have hnd := traceForm_nondegenerate ℚ F
  have exQ : ∀ l l' : Λ, ∃ Q : F, ∀ t : F,
      ((Algebra.trace ℚ F (t * Q) : ℚ) : ℝ) = ∑ j, e j t * G l l' j := by
    intro l l'
    choose q hq using rat l l'
    let φ : Module.Dual ℚ F :=
      { toFun := q
        map_add' := fun x y => by
          apply Rat.cast_injective (α := ℝ)
          push_cast
          rw [hq, hq, hq, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_add]; ring
        map_smul' := fun r x => by
          apply Rat.cast_injective (α := ℝ)
          simp only [RingHom.id_apply, smul_eq_mul]
          push_cast
          rw [hq, hq, Rat.smul_def, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, map_ratCast]; ring }
    refine ⟨((Algebra.traceForm ℚ F).toDual hnd).symm φ, fun t => ?_⟩
    rw [mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
    exact hq t
  choose Q hQ using exQ
  have uniq : ∀ x y : F, (∀ t : F, ((Algebra.trace ℚ F (t * x) : ℚ) : ℝ) =
      ((Algebra.trace ℚ F (t * y) : ℚ) : ℝ)) → x = y := by
    intro x y hxy
    apply ((Algebra.traceForm ℚ F).toDual hnd).injective
    refine LinearMap.ext fun t => ?_
    rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply,
      Algebra.traceForm_apply, mul_comm x, mul_comm y]
    exact_mod_cast hxy t
  refine ⟨fun l l' => Q l l' / (2 * c), ?_, ?_, ?_, ?_, ?_⟩
  · intro l l'
    simp only
    rw [← neg_div]; congr 1
    apply uniq; intro t
    rw [mul_neg, map_neg, Rat.cast_neg, hQ, hQ, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [G, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  · intro l₁ l₂ l'
    simp only
    rw [← add_div]; congr 1
    apply uniq; intro t
    rw [mul_add, map_add, Rat.cast_add, hQ, hQ, hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [G, Submodule.coe_add, Pi.add_apply, add_mul, Complex.add_im]
    ring
  · intro a l l' al hal
    simp only
    rw [← mul_div_assoc]; congr 1
    apply uniq; intro t
    rw [← mul_assoc, hQ, hQ]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [G, hal, map_mul]
    rw [mul_assoc ((e j (a : F) : ℂ)), Complex.im_ofReal_mul]
    ring
  · intro l l'
    have h1 := hQ l l' 1
    simp only [one_mul, map_one] at h1
    have htr : Algebra.trace ℚ F ((c : F) * (Q l l' / (2 * c))) = Algebra.trace ℚ F (Q l l') / 2 := by
      rw [show (c : F) * (Q l l' / (2 * c)) = (1 / 2 : ℚ) • Q l l' by
        rw [Rat.smul_def]; push_cast; field_simp]
      rw [map_smul, smul_eq_mul]; ring
    rw [htr, Complex.im_sum]
    simp_rw [Complex.im_ofReal_mul]
    push_cast
    rw [h1]
    ring
  · intro l l'
    have hI : ((𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) ≠ 0 := 𝔠.ne_zero
    unfold dualLat
    rw [FractionalIdeal.mem_dual hI]
    intro a ha
    obtain ⟨k, hk⟩ := hint ⟨a, ha⟩ l l'
    rw [conv] at hk
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    apply Rat.cast_injective (α := ℝ)
    rw [show Q l l' / (2 * c) * a = (a / (2 * c)) * Q l l' by ring, hQ]
    simp only [eq_intCast, Rat.cast_intCast]
    exact hk.symm

end GlobalTheory.RealMult
end

open NumberField GlobalTheory.RealMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_real_multiplication_integral : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (h : Fin (Module.finrank ℚ F) → ℝ),
    (∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ Λ → (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ Λ) →
    (∀ (c' : 𝔠.elt) (l l' : Λ), ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (((e j ((c' : F) / (2 * (c : F))) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = n) →
    ∃ P : Λ → Λ → F, (∀ l l' : Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : Λ, P l l' ∈ dualLat 𝔠) := by
  atlas_forward_decl GlobalTheory.RealMult.exists_trace_pairing_of_integral
end

section
section
open NumberField GlobalTheory.RealMult
open scoped nonZeroDivisors

namespace GlobalTheory.RealMult.SpanDual

theorem exists_im_ne_zero {n : ℕ} (hn : 0 < n) (Λ : Submodule ℤ (Fin n → ℂ))
    (hspan : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤) (h : Fin n → ℝ) (hpos : ∀ j, 0 < h j) :
    ∃ l ∈ Λ, ∃ l' ∈ Λ, (∑ j, (h j : ℂ) * (l j * starRingEnd ℂ (l' j))).im ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun z w ↦ (∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j))).im)
      (fun z z' w ↦ by simp [add_mul, mul_add, Finset.sum_add_distrib])
      (fun r z w ↦ by
        have : (∑ j, (h j : ℂ) * ((r • z) j * starRingEnd ℂ (w j))) =
            (r : ℂ) * ∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [Pi.smul_apply, Complex.real_smul]; ring
        rw [this, Complex.im_ofReal_mul, smul_eq_mul])
      (fun z w w' ↦ by simp [add_mul, mul_add, Finset.sum_add_distrib])
      (fun r z w ↦ by
        have : (∑ j, (h j : ℂ) * (z j * starRingEnd ℂ ((r • w) j))) =
            (r : ℂ) * ∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring
        rw [this, Complex.im_ofReal_mul, smul_eq_mul])
  have h1 : ∀ l ∈ Λ, B l = 0 := fun l hl ↦
    LinearMap.ext_on hspan (fun w hw ↦ by simpa [B] using hcon l hl w hw)
  have h2 : B = 0 := LinearMap.ext_on hspan (fun z hz ↦ by rw [h1 z hz]; rfl)
  have h3 := congrArg (fun B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ ↦
    B (Pi.single ⟨0, hn⟩ 1) (Pi.single ⟨0, hn⟩ Complex.I)) h2
  simp only [B, LinearMap.mk₂_apply] at h3
  rw [Finset.sum_eq_single ⟨0, hn⟩ (fun b _ hb ↦ by simp [Pi.single_apply, hb]) (by simp)] at h3
  simp at h3
  exact (hpos ⟨0, hn⟩).ne' h3

theorem isIntegral_of_stab {F : Type} [Field F] {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (Fin n → ℂ)) (e : Fin n → (F →+* ℝ))
    [DiscreteTopology Λ] (hspan : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤) (s : F)
    (hs : ∀ l ∈ Λ, (fun j ↦ (e j s : ℂ) * l j) ∈ Λ) : IsIntegral ℤ s := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let φ : F →+* (Fin n → ℂ) := Pi.ringHom fun j ↦ Complex.ofRealHom.comp (e j)
  letI : Module F (Fin n → ℂ) := Module.compHom _ φ
  have hsmul : ∀ (t : F) (z : Fin n → ℂ), t • z = fun j ↦ (e j t : ℂ) * z j := fun _ _ ↦ rfl
  haveI : IsScalarTower ℤ F (Fin n → ℂ) := ⟨fun k x y ↦ by
    funext j
    simp only [hsmul, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast]
    push_cast; ring⟩
  haveI : Module.IsTorsionFree F (Fin n → ℂ) := ⟨fun r hr z w hzw ↦ by
    have hr0 : r ≠ 0 := hr.ne_zero
    funext j
    have := congrFun hzw j
    simp only [hsmul] at this
    exact mul_left_cancel₀ (by simpa using (e j).injective.ne hr0 |>.trans_eq (map_zero _)) this⟩
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  haveI := ZLattice.module_finite ℝ Λ
  have hfg : Λ.FG := Module.Finite.iff_fg.mp inferInstance
  have hne : Λ ≠ ⊥ := by
    intro h0
    rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
    exact bot_ne_top hspan
  exact isIntegral_of_smul_mem_submodule Λ hne hfg s hs

theorem dualLat_le {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) (c : 𝔠.elt) (hc0 : (c : F) ≠ 0)
    (N : Submodule (𝓞 F) F) (hN0 : N ≠ ⊥) (hN : N ≤ dualLat 𝔠)
    (H : ∀ t : F, (∀ y ∈ N, ∃ m : ℤ, Algebra.trace ℚ F ((c : F) * t * y) = m) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → IsIntegral ℤ ((a : F) * t)) :
    (dualLat 𝔠 : Submodule (𝓞 F) F) ≤ N := by
  set C : FractionalIdeal (𝓞 F)⁰ F := (𝔠 : FractionalIdeal (𝓞 F)⁰ F) with hCdef
  have hC : C ≠ 0 := 𝔠.ne_zero
  have hcC : (c : F) ∈ C := c.2
  let Nf : FractionalIdeal (𝓞 F)⁰ F := ⟨N, FractionalIdeal.isFractional_of_le hN⟩
  have hNf : Nf ≠ 0 := by
    intro h0
    apply hN0
    have := congrArg (fun I : FractionalIdeal (𝓞 F)⁰ F ↦ (I : Submodule (𝓞 F) F)) h0
    simpa [Nf] using this
  set cs := FractionalIdeal.spanSingleton (𝓞 F)⁰ (c : F)
  have hcs : cs ≠ 0 := by simpa [cs, FractionalIdeal.spanSingleton_eq_zero_iff] using hc0
  have key : FractionalIdeal.dual ℤ ℚ (cs * Nf) * (cs * C⁻¹) ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro t ht u hu
    obtain ⟨v, hv, rfl⟩ := (FractionalIdeal.mem_singleton_mul).mp hu
    have hcv : (c : F) * v ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      have := FractionalIdeal.mul_mem_mul hcC hv
      rwa [mul_inv_cancel₀ hC] at this
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hcv
    have hint : IsIntegral ℤ ((a : F) * t) := by
      refine H t (fun y hy ↦ ?_) a (fun d ↦ ?_)
      · have hy' : (c : F) * y ∈ cs * Nf :=
          FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hy
        obtain ⟨m, hm⟩ := (FractionalIdeal.mem_dual (mul_ne_zero hcs hNf)).mp ht _ hy'
        refine ⟨m, ?_⟩
        rw [Algebra.traceForm_apply] at hm
        rw [show (c : F) * t * y = t * ((c : F) * y) by ring, ← hm]; simp
      · have hvd : v * d ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
          have := FractionalIdeal.mul_mem_mul hv d.2
          rwa [inv_mul_cancel₀ hC] at this
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp hvd
        refine ⟨b, Subtype.ext ?_⟩
        simp only [Submodule.coe_smul, Algebra.smul_def]
        change (a : F) * d = (b : F) * c
        change algebraMap (𝓞 F) F a = _ at ha
        change algebraMap (𝓞 F) F b = _ at hb
        change algebraMap (𝓞 F) F a * d = algebraMap (𝓞 F) F b * c
        rw [ha, hb]; ring
    rw [mul_comm, ← ha]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨_, hint⟩, rfl⟩
  rw [FractionalIdeal.dual_eq_mul_inv, mul_inv] at key
  have key2 : FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹ ≤ 1 := by
    convert key using 1
    calc FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹
        = FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹ * (cs⁻¹ * cs) := by rw [inv_mul_cancel₀ hcs, mul_one]
      _ = _ := by ring
  have key3 : FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹ * Nf ≤ 1 * Nf :=
    FractionalIdeal.mul_le.mpr fun i hi j hj ↦ FractionalIdeal.mul_mem_mul (key2 hi) hj
  simp only [mul_assoc, inv_mul_cancel₀ hNf, mul_one, one_mul] at key3
  have : dualLat 𝔠 ≤ Nf := by
    unfold dualLat
    rw [FractionalIdeal.dual_eq_mul_inv]
    exact key3
  exact (FractionalIdeal.coe_le_coe.mpr this)

theorem dualLat_le_span_values : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (h : Fin (Module.finrank ℚ F) → ℝ),
    (∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ Λ → (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin (Module.finrank ℚ F) → ℂ)) = ⊤ → (∀ j, 0 < h j) →
    ∀ P : Λ → Λ → F, (∀ l l' : Λ, P l l' = -P l' l) → (∀ l₁ l₂ l' : Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') →
      (∀ (a : 𝓞 F) (l l' al : Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') →
      (∀ l l' : Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) →
      (∀ l l' : Λ, P l l' ∈ dualLat 𝔠) →
    (∀ x : Fin (Module.finrank ℚ F) → ℂ, (∀ l : Λ, ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (x j * starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im = 2 * n) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → (fun j ↦ (e j (a : F) : ℂ) * x j) ∈ Λ) →
    ∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : Λ, t = P l l'} := by
  intro F _ _ _ 𝔠 c hc Λ e h hΛa hdisc hspan hpos P _hanti _hadd hlin htr hdual hker
  have hn : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hc0 : (c : F) ≠ 0 := fun h0 ↦ by
    have := hc (e ⟨0, hn⟩); rw [h0, map_zero] at this; exact lt_irrefl _ this

  have hb : ∀ (s : F) (l₀ l : Λ),
      (∑ j, (h j : ℂ) * (((e j s : ℂ) * (l₀ : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * s * P l₀ l) : ℚ) : ℝ) := by
    intro s l₀ l
    obtain ⟨m, hm0, hmint⟩ :=
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic s)).exists_integral_multiple
    let a : 𝓞 F := ⟨m • s, hmint⟩
    have ha : (a : F) = (m : F) * s := by simp [a, zsmul_eq_mul]
    have hal : (fun j ↦ (e j (a : F) : ℂ) * (l₀ : Fin (Module.finrank ℚ F) → ℂ) j) ∈ Λ := hΛa a l₀ l₀.2
    have h1 := htr ⟨_, hal⟩ l
    rw [hlin a l₀ l ⟨_, hal⟩ rfl] at h1
    have e1 : (∑ j, (h j : ℂ) * (((⟨_, hal⟩ : Λ) : Fin (Module.finrank ℚ F) → ℂ) j *
          starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))) =
        ((m : ℝ) : ℂ) * ∑ j, (h j : ℂ) * (((e j s : ℂ) * (l₀ : Fin (Module.finrank ℚ F) → ℂ) j) *
          starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [ha, map_mul, map_intCast]; push_cast; ring
    have e2 : Algebra.trace ℚ F ((c : F) * ((a : F) * P l₀ l)) =
        (m : ℚ) * Algebra.trace ℚ F ((c : F) * s * P l₀ l) := by
      rw [ha, show (c : F) * ((m : F) * s * P l₀ l) = (m : ℚ) • ((c : F) * s * P l₀ l) by
        rw [Algebra.smul_def, map_intCast]; ring, map_smul, smul_eq_mul]
    rw [e1, e2, Complex.im_ofReal_mul] at h1
    push_cast at h1
    have hm : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm0
    apply mul_left_cancel₀ hm
    rw [h1]; ring
  set N := Submodule.span (𝓞 F) {t | ∃ l l' : Λ, t = P l l'} with hNdef
  have hN : N ≤ dualLat 𝔠 := Submodule.span_le.mpr (by rintro _ ⟨l, l', rfl⟩; exact hdual l l')
  have hN0 : N ≠ ⊥ := by
    obtain ⟨l, hl, l', hl', hne⟩ := exists_im_ne_zero hn Λ hspan h hpos
    intro hbot
    have hmem : P ⟨l, hl⟩ ⟨l', hl'⟩ ∈ N := Submodule.subset_span ⟨_, _, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    apply hne
    have := htr ⟨l, hl⟩ ⟨l', hl'⟩
    rw [hmem] at this
    simpa using this
  intro t ht
  refine dualLat_le 𝔠 c hc0 N hN0 hN (fun s hs a ha ↦ ?_) ht
  refine isIntegral_of_stab hn Λ e hspan _ (fun l₀ hl₀ ↦ ?_)
  have hx := hker (fun j ↦ (e j s : ℂ) * l₀ j) (fun l ↦ ?_) a ha
  · convert hx using 1
    funext j
    simp only [map_mul]; push_cast; ring
  · obtain ⟨m, hm⟩ := hs (P ⟨l₀, hl₀⟩ l) (Submodule.subset_span ⟨_, _, rfl⟩)
    refine ⟨m, ?_⟩
    rw [hb s ⟨l₀, hl₀⟩ l, hm]
    push_cast; ring

end GlobalTheory.RealMult.SpanDual
end

open NumberField GlobalTheory.RealMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_real_multiplication_span : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (h : Fin (Module.finrank ℚ F) → ℝ),
    (∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ Λ → (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin (Module.finrank ℚ F) → ℂ)) = ⊤ → (∀ j, 0 < h j) →
    ∀ P : Λ → Λ → F, (∀ l l' : Λ, P l l' = -P l' l) → (∀ l₁ l₂ l' : Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') →
      (∀ (a : 𝓞 F) (l l' al : Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') →
      (∀ l l' : Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) →
      (∀ l l' : Λ, P l l' ∈ dualLat 𝔠) →
    (∀ x : Fin (Module.finrank ℚ F) → ℂ, (∀ l : Λ, ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (x j * starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im = 2 * n) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → (fun j ↦ (e j (a : F) : ℂ) * x j) ∈ Λ) →
    ∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : Λ, t = P l l'} := by
  atlas_forward_decl GlobalTheory.RealMult.SpanDual.dualLat_le_span_values
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRiem

theorem riemannForm_eq_two_trace : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∃ P : u.Λ → u.Λ → F, (∀ l l' : u.Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : u.Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : u.Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : u.Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : u.Λ, P l l' ∈ dualLat 𝔠) ∧
      (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : u.Λ, t = P l l'}) := by
  intro F _ _ _ 𝔠 X c hc u e hu h χ hAH
  have hΛa : ∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ u.Λ →
      (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ u.Λ := by
    intro a l hl
    rw [← u.ker, hu, (u.ker l).2 hl]
    haveI := X.rm.hom a
    simp
  have hpos : ∀ j, 0 < h j := by
    intro j
    have := hAH.2.1 (Pi.single j 1) (by simp)
    simpa [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply] using this
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.lattice_real_multiplication_integral F 𝔠 c hc u.Λ e h hΛa (GlobalTheory.T.appell_humbert_diagonal_real F 𝔠 X c hc u e hu h χ hAH)
  exact ⟨P, h1, h2, h3, h4, h5, GlobalTheory.T.lattice_real_multiplication_span F 𝔠 c hc u.Λ e h hΛa u.discrete u.full hpos P h1 h2 h3 h4 h5
    (fun x hx a ha => GlobalTheory.T.appell_humbert_diagonal_real_dual F 𝔠 X c hc u e hu h χ hAH x hx a ha)⟩

end GlobalTheory.TorusRiem
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_appell_humbert_real_mult : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∃ P : u.Λ → u.Λ → F, (∀ l l' : u.Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : u.Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : u.Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : u.Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : u.Λ, P l l' ∈ dualLat 𝔠) ∧
      (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : u.Λ, t = P l l'}) := by
  atlas_forward_decl GlobalTheory.TorusRiem.riemannForm_eq_two_trace
end
