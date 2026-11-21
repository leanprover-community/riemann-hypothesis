import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionForStatement

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.Published

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem ArFormExists.exists_isArithHeight (H : ArFormExists) (hX : IsArithVar p D) (L : HermLB p) :
    ∃ h, L.IsArithHeight h := by
  obtain ⟨Φ, hΦ⟩ := H k X p D hX Unit fun _ => L
  obtain ⟨h, hh, -⟩ := hΦ.1 (Pi.single () 1)
  exact ⟨h, (isometric_comb_single (fun _ : Unit => L) ()).isArithHeight hX hh⟩

theorem ArMix.fnB_of_height (H : ArMix) (hX : IsArithVar p D) {ι : Type} [Fintype ι] {L : ι → HermLB p}
    {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} {hu : ∀ σ y, CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim (ArInt.fnB u hu hc) L) D Φ) (n : ι → ℤ) {h : X → ℝ}
    (hh : (comb L n).IsArithHeight h) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u := by
  have := hX.isLocallyNoetherian
  have hr : IsRatSec (ArInt.fnB u hu hc).B fun _ => 1 := fun a b h =>
    (map_one _).symm.trans (mul_one _).symm
  have he (z : X) : ((ArInt.fnB u hu hc).div hr).IsEqn z 1 :=
    (presents_divOfRatSec _ hr).isEqn PUnit.unit z trivial
  have h₁ (z : X) : ((ArInt.fnB u hu hc).div hr).mult z = 0 := (he z).mult_eq.trans (unitAt_one z).ord_eq_zero
  have h₂ (σ) : offSupp p σ ((ArInt.fnB u hu hc).div hr) = Set.univ :=
    Set.eq_univ_of_forall fun y => mem_offSupp.2 fun hy => (he _).mem_supp_iff.1 hy (unitAt_one _)
  have h₃ (σ) : logNorm ((ArInt.fnB u hu hc).φ σ) (fun _ => 1) = fun y => -(1 / 2) * u σ y := funext fun y => by
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    rw [logNorm, Units.val_one, e, norm_one, Real.log_one]
    change 0 - u σ y / 2 = _
    ring
  rw [(H k X p D hX ι _ L Φ hΦ n h hh _ hr).2, HermLB.archInt, chInt]
  simp only [h₁, h₂, h₃, Weight.chernInt_const_mul, Int.cast_zero, zero_mul, finsum_zero, ← mul_finsum]
  ring

theorem arExists_of_form_of_mix : ArFormExists → ArMix → ArExists := by
  intro HF HM k _ X _ p D hX
  refine ⟨HF.exists_isArithHeight hX, fun ι _ L => ⟨HF k X p D hX ι L, ?_⟩⟩
  have hu (σ : k →+* ℂ) (y : CxPts p σ) : CInfAt (fun _ => (2 : ℝ)) y := cInfAt_const _ y
  have hc (σ σ' : k →+* ℂ) : (Weight.ofFun (p := p) (σ := σ) fun _ => (2 : ℝ)).IsConj
      (Weight.ofFun (σ := σ') fun _ => (2 : ℝ)) := fun _ _ _ _ _ => rfl
  obtain ⟨Φ, hΦ⟩ := HF k X p D hX _ fun o : Option ι => o.elim (ArInt.fnB (fun _ _ => 2) hu hc) L
  refine ⟨Φ ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) ∘ₗ (rename (R := ℝ) (some : ι → Option ι)).toLinearMap,
    fun n => ?_, fun P d hd hP => ?_⟩
  · obtain ⟨h, hh⟩ := HF.exists_isArithHeight hX (comb L n)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, LinearMap.mulLeft_apply,
      HM.fnB_of_height hX hΦ n hh, gdeg, chInt, chInt, mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← Weight.chernInt_const_mul]
    norm_num
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
    exact hΦ.2 _ (1 + d) (by omega) ((isHomogeneous_X ℝ none).mul hP.rename_isHomogeneous)

end GlobalTheory.Published
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive : GlobalTheory.Published.ArFormExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArExists := by
  atlas_forward_decl GlobalTheory.Published.arExists_of_form_of_mix
end

section
section
namespace GlobalTheory.Published

theorem arShift_of_arChange : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  intro hE hC k _ X _ p D hX L a t ha
  have h := GlobalTheory.TwistTop.isSelfInter_shift hE hC k X p D hX L a (fun _ => t) (fun _ => rfl) ha
  rw [← mul_finsum, ← mul_assoc] at h
  exact h

end GlobalTheory.Published
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithSelfInter_constantShift_of_trivialWeightFormula : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  atlas_forward_decl GlobalTheory.Published.arShift_of_arChange
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.HermLB

namespace GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} {ι : Type} [Fintype ι]

theorem mixed_eq_of_icls (hX : IsArithVar p D) {T M N : HermLB p} {L : ι → HermLB p}
    {Ψ : MvPolynomial (Option (Option ι)) ℝ →ₗ[ℝ] ℝ}
    (hΨ : IsArFun (fun o : Option (Option ι) => o.elim T fun o => o.elim M L) D Ψ) (a b : ℤ)
    (hN : N.icls = b • T.icls + a • M.icls) {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim N L) D Φ) (n : ι → ℤ) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
      b * Ψ (MvPolynomial.X none * rename (some ∘ some) (lin fun i => (n i : ℝ)) ^ D) +
      a * Ψ (MvPolynomial.X (some none) * rename (some ∘ some) (lin fun i => (n i : ℝ)) ^ D) := by
  classical
  let A : Option ι → Option (Option ι) → ℤ := fun j => j.elim (fun o => o.elim b fun o => o.elim a 0)
    fun i => Pi.single (some (some i)) 1
  have h := ((Published.arIso_holds k X p D hX).2 _ _ Ψ hΨ).2.2 (Option ι) (fun o : Option ι => o.elim N L) A (by
    rintro (_ | i)
    · exact icls_eq_iff.1 (by simp [A, icls_comb, Fintype.sum_option, hN])
    · exact isometric_comb_single _ (some (some i)))
  have e₀ : (lin fun i => (A none i : ℝ)) = (b : ℝ) • MvPolynomial.X none + (a : ℝ) • MvPolynomial.X (some none) := by
    simp [A, lin, Fintype.sum_option, smul_eq_C_mul]
  have e₁ (i : ι) : (lin fun j => (A (some i) j : ℝ)) = MvPolynomial.X (some (some i)) := lin_single _
  have e₂ : aeval (fun j => lin fun i => (A j i : ℝ)) (rename some (lin fun i => (n i : ℝ))) =
      rename (some ∘ some) (lin fun i => (n i : ℝ)) := by
    conv_lhs => rw [aeval_rename]
    simp only [Function.comp_def, e₁]
    rw [rename_eq_aeval]
    rfl
  rw [Model.isArFun_unique hX hΦ h, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_pow, e₂, aeval_X, e₀,
    add_mul, smul_mul_assoc, smul_mul_assoc, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end GlobalTheory.ArInt

namespace GlobalTheory.Published

theorem arMetric_of_arMix : ArExists → ArMix → ArMetric := by
  intro HE H k _ X _ p D hX ι _ M L u hu hc Φ Φ' hΦ hΦ' n
  obtain ⟨Ψ, hΨ⟩ := ((HE k X p D hX).2 _
    fun o : Option (Option ι) => o.elim (ArInt.fnB u hu hc) fun o => o.elim M L).1
  obtain ⟨Θ, hΘ⟩ := ((HE k X p D hX).2 _ fun o : Option ι => o.elim (ArInt.fnB u hu hc) L).1
  obtain ⟨h₁, h₂⟩ := H.fnB HE hX hΘ n
  refine ⟨h₁, ?_⟩
  rw [← h₂, mixed_eq_of_icls hX hΨ 1 0 (by simp) hΦ, mixed_eq_of_icls hX hΨ 0 1 (by simp) hΘ,
    mixed_eq_of_icls hX hΨ 1 1 (by
      rw [← icls_eq_iff.2 (isometric_tens_fnB M u hu hc), icls_tens, one_smul, one_smul, add_comm]) hΦ']
  push_cast
  ring

end GlobalTheory.Published
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithInterChangeOfMetric_of_mixedInductive : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArMetric := by
  atlas_forward_decl GlobalTheory.Published.arMetric_of_arMix
end

section
namespace GlobalTheory.Published

theorem arCalc_of_form_mix_projection : ArFormExists → ArMix → HeightProjection → ArCalc := fun hF hM hP =>
  have hE : ArExists := GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive hF hM
  have hC : ArChange := arChange_of_arMix hE hM
  ⟨hE, hC, GlobalTheory.T.arithSelfInter_constantShift_of_trivialWeightFormula hE hC, hM, GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula hP, arIso_holds, GlobalTheory.T.arithInterChangeOfMetric_of_mixedInductive hE hM⟩

end GlobalTheory.Published
end
