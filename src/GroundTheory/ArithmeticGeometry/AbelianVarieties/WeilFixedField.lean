import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsPullback

section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic]

local notation "ι" => algebraMap F W.toAffine.FunctionField

theorem translate_add (R S : W.toAffine.Point) :
    translate W (R + S) = (translate W R).comp (translate W S) := by
  apply algHom_eq_of_map_genericPoint
  rw [map_translate_genericPoint, ← Point.map_map, map_translate_genericPoint,
    map_add (Point.map (translate W R)), map_translate_genericPoint, map_constPoint,
    map_add (constPoint W), add_assoc]

theorem translate_translate (R S : W.toAffine.Point) (f : W.toAffine.FunctionField) :
    translate W R (translate W S f) = translate W (R + S) f := by
  rw [translate_add]
  rfl

theorem translate_algebraMap (R : W.toAffine.Point) (c : F) : translate W R (ι c) = ι c :=
  (translate W R).commutes c

theorem translate_injective (R : W.toAffine.Point) : Function.Injective (translate W R) :=
  (translate W R).toRingHom.injective

theorem translate_ne_zero (R : W.toAffine.Point) {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    translate W R f ≠ 0 :=
  (map_ne_zero_iff _ (translate_injective W R)).mpr hf

theorem valuationPoint_translate (P R : W.toAffine.Point) (f : W.toAffine.FunctionField) :
    valuationPoint W P (translate W R f) = valuationPoint W (P + R) f := by
  rw [← valuationInfty_translate, ← valuationInfty_translate, translate_translate]

theorem ordPoint_translate (P R : W.toAffine.Point) {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    ordPoint W P (translate W R f) = ordPoint W (P + R) f := by
  have h := valuationPoint_translate W P R f
  rw [valuationPoint_eq_exp W P (translate_ne_zero W R hf), valuationPoint_eq_exp W (P + R) hf,
    exp_inj] at h
  exact neg_injective h


omit [DecidableEq F] [IsAlgClosed F] in

theorem mulPullback_mul {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    mulPullback W (m * n) (mul_ne_zero hm hn) = (mulPullback W m hm).comp (mulPullback W n hn) := by
  apply algHom_eq_of_map_genericPoint
  rw [map_mulPullback_genericPoint, ← Point.map_map, map_mulPullback_genericPoint, map_zsmul,
    map_mulPullback_genericPoint, mul_comm, mul_zsmul]

omit [DecidableEq F] [IsAlgClosed F] in
theorem mulPullback_algebraMap {n : ℤ} (hn : n ≠ 0) (c : F) : mulPullback W n hn (ι c) = ι c :=
  (mulPullback W n hn).commutes c

omit [DecidableEq F] [IsAlgClosed F] in
theorem mulPullback_injective {n : ℤ} (hn : n ≠ 0) : Function.Injective (mulPullback W n hn) :=
  (mulPullback W n hn).toRingHom.injective

omit [DecidableEq F] [IsAlgClosed F] in
theorem mulPullback_ne_zero {n : ℤ} (hn : n ≠ 0) {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    mulPullback W n hn f ≠ 0 :=
  (map_ne_zero_iff _ (mulPullback_injective W hn)).mpr hf

theorem translate_mulPullback_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {S : W.toAffine.Point}
    (hS : n • S = 0) (f : W.toAffine.FunctionField) :
    translate W S (mulPullback W n hn f) = mulPullback W n hn f := by
  have h := DFunLike.congr_fun (translate_comp_mulPullback W hn S) f
  simp only [AlgHom.comp_apply, hS, translate_zero, AlgHom.id_apply] at h
  exact h

omit [DecidableEq F] [W.IsElliptic] in

theorem exists_algebraMap_eq_of_pow_eq {u : W.toAffine.FunctionField} {n : ℕ} (hn : n ≠ 0) {c : F}
    (h : u ^ n = ι c) : ∃ d : F, ι d = u := by
  apply exists_algebraMap_eq_of_isAlgebraic W
  refine ⟨X ^ n - C c, X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) c, ?_⟩
  simp [h]

theorem exists_algebraMap_eq_of_divisorOf_eq_zero {f : W.toAffine.FunctionField} (hf : f ≠ 0)
    (h : divisorOf W f = 0) : ∃ c : F, ι c = f := by
  have hint : f ∈ (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField).range := by
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have h0 : ordAtIdeal W v f = 0 := by
      rw [← divisorOf_pointOfIdeal, h, Finsupp.zero_apply]
    rw [valuation_eq_exp_neg_ordAtIdeal W v hf, h0, neg_zero, exp_zero]
  obtain ⟨a, rfl⟩ := hint
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf (map_zero _)
  have hinf : ordInfty W (algebraMap _ W.toAffine.FunctionField a) = 0 := by
    rw [← ordPoint_zero, ← divisorOf_apply, h, Finsupp.zero_apply]
  rw [ordInfty_algebraMap W ha, neg_eq_zero, Nat.cast_eq_zero] at hinf
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  by_cases hq : q = 0
  · subst hq
    have h2 := natDegree_norm_smul_basis_of_q_eq_zero (W := W) (p := p)
    rw [hinf] at h2
    have hp0 : p.natDegree = 0 := by omega
    rw [natDegree_eq_zero] at hp0
    obtain ⟨c, rfl⟩ := hp0
    refine ⟨c, ?_⟩
    rw [algebraMap_smul_basis, map_zero, zero_mul, add_zero, ← algebraMap_C_functionField]
  · exfalso
    by_cases hp : p = 0
    · subst hp
      have h2 := natDegree_norm_smul_basis_of_p_eq_zero (W := W) hq
      have h3 : 2 * q.natDegree + 3 = 0 := h2.symm.trans hinf
      omega
    · have h2 := natDegree_norm_smul_basis_of_ne_zero (W := W) hp hq
      have h3 : max (2 * p.natDegree) (2 * q.natDegree + 3) = 0 := h2.symm.trans hinf
      have h4 := le_max_right (2 * p.natDegree) (2 * q.natDegree + 3)
      omega

theorem exists_algebraMap_mul_eq_of_divisorOf_eq {f g : W.toAffine.FunctionField} (hf : f ≠ 0)
    (hg : g ≠ 0) (h : divisorOf W f = divisorOf W g) : ∃ c : F, c ≠ 0 ∧ ι c * f = g := by
  have hq : g / f ≠ 0 := div_ne_zero hg hf
  have hd : divisorOf W (g / f) = 0 := by
    have := divisorOf_mul W hq hf
    rw [div_mul_cancel₀ g hf, h] at this
    exact add_eq_right.mp this.symm
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_divisorOf_eq_zero W hq hd
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hc
    exact hq hc.symm
  · rw [hc, div_mul_cancel₀ g hf]

theorem exists_zsmul_eq {n : ℤ} (hn : n ≠ 0) (Q : W.toAffine.Point) : ∃ P, n • P = Q := by
  classical
  cases Q with
  | zero => exact ⟨0, smul_zero n⟩
  | some xQ yQ hQ =>
    set p : F[X] := W.Φ n - C xQ * W.ΨSq n with hpdef
    have hlt : (C xQ * W.ΨSq n).natDegree < (W.Φ n).natDegree := by
      rw [natDegree_Φ]
      calc (C xQ * W.ΨSq n).natDegree ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
        _ ≤ n.natAbs ^ 2 - 1 := natDegree_ΨSq_le W n
        _ < n.natAbs ^ 2 := by
          have : 0 < n.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hn) 2
          omega
    have hdeg : p.natDegree = n.natAbs ^ 2 := by
      rw [hpdef, natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_Φ]
    have hpos : 0 < p.natDegree := by rw [hdeg]; exact pow_pos (Int.natAbs_pos.mpr hn) 2
    have hdeg0 : p.degree ≠ 0 := (natDegree_pos_iff_degree_pos.mp hpos).ne'
    obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root p hdeg0
    have hx₀' : (W.Φ n).eval x₀ = xQ * (W.ΨSq n).eval x₀ := by
      rw [IsRoot, hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero] at hx₀
      exact hx₀
    have hψ : (W.ΨSq n).eval x₀ ≠ 0 := by
      intro h0
      obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W n
      have := congrArg (eval x₀) hab
      rw [eval_add, eval_mul, eval_mul, h0, hx₀', h0, mul_zero, mul_zero, mul_zero, add_zero,
        eval_one] at this
      exact zero_ne_one this
    obtain ⟨y₀, hy₀⟩ := exists_equation W x₀
    have h₀ : W.toAffine.Nonsingular x₀ y₀ := equation_iff_nonsingular.mp hy₀
    have hne : n • Point.some x₀ y₀ h₀ ≠ 0 := fun h => hψ ((zsmul_eq_zero_iff W h₀ n).mp h)
    have hx : xOf W (n • Point.some x₀ y₀ h₀) = xQ := by
      rw [xOf_zsmul W h₀ n hψ, hx₀', mul_div_cancel_right₀ _ hψ]
    have key : ∀ {x y : F} (h : W.toAffine.Nonsingular x y), x = xQ →
        Point.some x y h = Point.some xQ yQ hQ ∨ Point.some x y h = -Point.some xQ yQ hQ := by
      rintro x y h rfl
      rcases Y_eq_of_X_eq h.1 hQ.1 rfl with hy | hy
      · left
        subst hy
        rfl
      · right
        rw [Point.neg_some]
        subst hy
        rfl
    obtain ⟨y', h', he⟩ := exists_eq_some_xOf W hne
    rcases key h' hx with e | e
    · exact ⟨_, he.trans e⟩
    · refine ⟨-Point.some x₀ y₀ h₀, ?_⟩
      rw [smul_neg, he, e, neg_neg]
end Abelian
end Arith
end GroundTheory
end

section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic]

theorem translate_inj {S S' : W.toAffine.Point} (h : translate W S = translate W S') : S = S' := by
  have e := congrArg (fun ψ => Point.map ψ (genericPoint W)) h
  simp only [map_translate_genericPoint, add_right_inj] at e
  exact Point.map_injective (W' := W) (f := Algebra.ofId F W.toAffine.FunctionField) e

noncomputable abbrev mulPullbackField {n : ℤ} (hn0 : n ≠ 0) :
    IntermediateField F W.toAffine.FunctionField :=
  (mulPullback W n hn0).fieldRange

noncomputable def translateEquiv {n : ℤ} (hn0 : n ≠ 0) (S : W.toAffine.Point) (hS : n • S = 0) :
    W.toAffine.FunctionField ≃ₐ[mulPullbackField W hn0] W.toAffine.FunctionField :=
  AlgEquiv.ofRingEquiv (f := {
      toFun := translate W S
      invFun := translate W (-S)
      left_inv := fun f => by rw [translate_translate, neg_add_cancel, translate_zero]; rfl
      right_inv := fun f => by rw [translate_translate, add_neg_cancel, translate_zero]; rfl
      map_mul' := map_mul (translate W S)
      map_add' := map_add (translate W S) }) (by
    rintro ⟨m, hm⟩
    obtain ⟨f, rfl⟩ := AlgHom.mem_fieldRange.mp hm
    exact translate_mulPullback_of_zsmul_eq_zero W hn0 hS f)

noncomputable def torsionTranslations {n : ℤ} (hn0 : n ≠ 0) :
    Subgroup (W.toAffine.FunctionField ≃ₐ[mulPullbackField W hn0] W.toAffine.FunctionField) where
  carrier := {σ | ∃ S : W.toAffine.Point, n • S = 0 ∧ ∀ f, σ f = translate W S f}
  mul_mem' := by
    rintro σ τ ⟨S, hS, hσ⟩ ⟨T, hT, hτ⟩
    refine ⟨S + T, by rw [smul_add, hS, hT, add_zero], fun f => ?_⟩
    rw [AlgEquiv.mul_apply, hτ, hσ, translate_translate]
  one_mem' := ⟨0, smul_zero n, fun f => by rw [translate_zero]; rfl⟩
  inv_mem' := by
    rintro σ ⟨S, hS, hσ⟩
    refine ⟨-S, by rw [smul_neg, hS, neg_zero], fun f => ?_⟩
    apply (translate_injective W S)
    rw [← hσ, translate_translate, add_neg_cancel, translate_zero, AlgHom.id_apply]
    exact σ.apply_symm_apply f

theorem card_torsionTranslations {n : ℤ} (hn : (n : F) ≠ 0) (hn0 : n ≠ 0) :
    Nat.card (torsionTranslations W hn0) = n.natAbs ^ 2 := by
  rw [← card_zsmul_eq_zero W hn]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun S => ⟨translateEquiv W hn0 S.1 S.2, S.1, S.2, fun _ => rfl⟩) ⟨?_, ?_⟩)
  · rintro ⟨S, hS⟩ ⟨S', hS'⟩ h
    have h' : translate W S = translate W S' := AlgHom.ext fun f =>
      DFunLike.congr_fun (congrArg Subtype.val h) f
    exact Subtype.ext (translate_inj W h')
  · rintro ⟨σ, S, hS, hσ⟩
    exact ⟨⟨S, hS⟩, Subtype.ext (AlgEquiv.ext fun f => (hσ f).symm)⟩

theorem exists_mulPullback_eq_of_forall_translate_eq {n : ℤ} (hn : (n : F) ≠ 0) (hn0 : n ≠ 0)
    {g : W.toAffine.FunctionField} (h : ∀ S : W.toAffine.Point, n • S = 0 → translate W S g = g) :
    ∃ f, mulPullback W n hn0 f = g := by
  set M := mulPullbackField W hn0
  set H := torsionTranslations W hn0
  have hdeg : Module.finrank M W.toAffine.FunctionField = n.natAbs ^ 2 :=
    degree_mulIsogeny W hn0
  have hpos : 0 < n.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hn0) 2
  have : FiniteDimensional M W.toAffine.FunctionField :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact hpos)
  have hfix : Module.finrank (IntermediateField.fixedField H) W.toAffine.FunctionField =
      n.natAbs ^ 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, card_torsionTranslations W hn hn0]
  have hone : Module.finrank M (IntermediateField.fixedField H) = 1 := by
    have : Module.Free M (IntermediateField.fixedField H) := Module.Free.of_divisionRing _ _
    have : Module.Free (IntermediateField.fixedField H) W.toAffine.FunctionField :=
      Module.Free.of_divisionRing _ _
    have := Module.finrank_mul_finrank M (IntermediateField.fixedField H) W.toAffine.FunctionField
    rw [hfix, hdeg] at this
    exact (Nat.mul_eq_right hpos.ne').mp this
  have hbot : IntermediateField.fixedField H = ⊥ := IntermediateField.finrank_eq_one_iff.mp hone
  have hg : g ∈ IntermediateField.fixedField H := by
    rintro ⟨σ, S, hS, hσ⟩
    exact (hσ g).trans (h S hS)
  rw [hbot, IntermediateField.mem_bot] at hg
  obtain ⟨⟨m, hm⟩, rfl⟩ := hg
  obtain ⟨f, rfl⟩ := AlgHom.mem_fieldRange.mp hm
  exact ⟨f, rfl⟩

end GroundTheory.Arith.Abelian
end
