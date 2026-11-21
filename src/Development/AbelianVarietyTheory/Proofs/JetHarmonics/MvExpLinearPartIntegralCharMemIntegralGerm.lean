import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegral
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqMvExpOfAdditive
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory

section

variable {C : Type} [Field C] [CharZero C] {σ : Type}

omit [CharZero C] in
theorem mvExp_coeff_apply (a : MvPowerSeries σ C) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (mvExp a) =
      ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (a ^ k) / (k.factorial : C) := rfl

theorem mvExp_eq_subst_exp (a : MvPowerSeries σ C) (ha : MvPowerSeries.constantCoeff a = 0) :
    mvExp a = PowerSeries.subst a (PowerSeries.exp C) := by
  ext m
  rw [mvExp_coeff_apply, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  · intro k hk
    by_contra hk'
    apply hk
    have hlt : m.degree < k := by simpa using hk'
    have : MvPowerSeries.coeff m (a ^ k) = 0 :=
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt)
        (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k ha))
    simp [this]

theorem mfact_mul_coeff_mvExp_linear [Fintype σ] (y : σ → C) (m : σ →₀ ℕ) :
    (mfact m : C) * MvPowerSeries.coeff m (mvExp (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C))) =
      ∏ i ∈ m.support, y i ^ m i := by
  classical
  have hL : (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C)) =
      ((∑ s, y s • (MvPolynomial.X s : MvPolynomial σ C) : MvPolynomial σ C) : MvPowerSeries σ C) := by
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.coe_mul,
      MvPolynomial.coe_C, MvPolynomial.coe_X, MvPowerSeries.smul_eq_C_mul]
  have hdeg : (m.sum fun _ e => e) = m.degree := by
    rw [Finsupp.degree_apply]; rfl
  rw [mvExp_coeff_apply, hL, Finset.sum_eq_single m.degree]
  · rw [← MvPolynomial.coe_pow, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
    have hs : mfact m * m.multinomial = m.degree.factorial := by
      rw [Finsupp.multinomial_eq, Finsupp.degree_apply, ← Nat.multinomial_spec]; rfl
    have hs' : (mfact m : C) * (m.multinomial : C) = (m.degree.factorial : C) := by exact_mod_cast hs
    have h0 : (m.degree.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← mul_div_assoc, ← mul_assoc, hs', mul_div_cancel_left₀ _ h0]
    rfl
  · intro k _ hk
    rw [← MvPolynomial.coe_pow, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_linearCombination_X_pow_of_fintype, if_neg (by rw [hdeg]; exact Ne.symm hk), zero_div]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

end

theorem mvExp_add_subst_linear : ∀ (C : Type) [Field C] [CharZero C] (σ : Type) [Fintype σ],
  (∀ a b : MvPowerSeries σ C, MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 → mvExp (a + b) = mvExp a * mvExp b) ∧
  (∀ a : MvPowerSeries σ C, MvPowerSeries.constantCoeff a = 0 → mvExp a = PowerSeries.subst a (PowerSeries.exp C)) ∧
  (∀ (τ : Type) [Fintype τ] (φ : σ → MvPowerSeries τ C) (a : MvPowerSeries σ C), (∀ s, MvPowerSeries.constantCoeff (φ s) = 0) → MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.subst φ (mvExp a) = mvExp (MvPowerSeries.subst φ a)) ∧
  (∀ (y : σ → C) (P : MvPolynomial σ C), jetAt0 P (mvExp (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C))) = MvPolynomial.eval y P) := by
  intro C _ _ σ _
  refine ⟨fun a b ha hb => ?_, fun a ha => mvExp_eq_subst_exp a ha, fun τ _ φ a hφ ha => ?_, fun y P => ?_⟩
  · rw [mvExp_eq_subst_exp a ha, mvExp_eq_subst_exp b hb,
      mvExp_eq_subst_exp (a + b) (by rw [map_add, ha, hb, add_zero])]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ha hb
  · have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
    rw [mvExp_eq_subst_exp a ha,
      mvExp_eq_subst_exp _ (MvPowerSeries.constantCoeff_subst_eq_zero hs hφ ha),
      PowerSeries.subst_def, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero ha).const hs]
  · rw [MvPolynomial.eval_eq, jetAt0]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_assoc, mfact_mul_coeff_mvExp_linear]

end GlobalTheory
end

section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.CharGerm

open MvPowerSeries GlobalTheory.RowLaw.GermRing GlobalTheory.FormalInv

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {Y : RawChart C d I κ} {V : VF C}

theorem const_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (F : MvPowerSeries σ C) : constantCoeff (subst a F) = constantCoeff F := by
  have hs := hasSubst_of_constantCoeff_zero ha
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [e, subst_add hs, map_add, constantCoeff_subst_zero ha (by simp), subst_C]
  simp

theorem coeff_single_subst_lg (hY : RLaw Y V) (F : MvPowerSeries κ C) (i : κ) :
    coeff (Finsupp.single i 1) (subst Y.lg F) = coeff (Finsupp.single i 1) F := by
  have hs := hasSubst_of_constantCoeff_zero (lg_const hY)
  have h := subst_sub_subst_mem_degGe (a := Y.lg) (b := (X : κ → MvPowerSeries κ C)) (k := 1) (m := 1)
    (fun s => mem_degGe_one.2 (lg_const hY s)) (fun s => mem_degGe_one.2 (constantCoeff_X s))
    (fun s => mem_degGe.2 fun μ hμ => by rw [map_sub, hY.lin s μ (by omega), sub_self])
    (f := F - MvPowerSeries.C (constantCoeff F)) (mem_degGe_one.2 (by simp))
  have h2 := mem_degGe.1 h (Finsupp.single i 1) (by simp)
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [map_sub, sub_eq_zero, congrFun subst_self] at h2
  conv_lhs => rw [e, subst_add hs, map_add, h2, subst_C]
  rw [← map_add]
  exact congrArg _ e.symm

theorem subst_ex_eq_mvExp (hY : RLaw Y V) (χ : MvPowerSeries κ C) (h0 : constantCoeff χ = 1)
    (hχ : subst (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1)) χ =
      subst (gp C κ (0 : Fin 2)) χ * subst (gp C κ (1 : Fin 2)) χ) :
    subst Y.ex χ = mvExp (∑ i : κ, coeff (Finsupp.single i 1) χ • (X i : MvPowerSeries κ C)) := by
  haveI := hY.charZero
  have hex := hasSubst_of_constantCoeff_zero hY.exc
  have hlg := hasSubst_of_constantCoeff_zero (lg_const hY)
  have hlin : ∀ i, coeff (Finsupp.single i 1) χ = coeff (Finsupp.single i 1) (subst Y.ex χ) := by
    intro i
    rw [← coeff_single_subst_lg hY (subst Y.ex χ), subst_comp_subst_apply hex hlg]
    simp only [hY.exlg]
    exact congrArg _ (congrFun subst_self χ).symm
  simp only [hlin]
  refine GlobalTheory.AddChar.eq_mvExp_of_additive C κ _ (by rw [const_subst hY.exc, h0]) ?_
  have hg : ∀ (j : Fin 2) x, constantCoeff (gp C κ j x) = 0 := fun j x => constantCoeff_X _
  have hgs : ∀ j : Fin 2, HasSubst (gp C κ j) := fun j => hasSubst_of_constantCoeff_zero (hg j)
  let e : Fin 2 × κ → MvPowerSeries (Fin 2 × κ) C := fun p => subst (gp C κ p.1) (Y.ex p.2)
  have he0 : ∀ p, constantCoeff (e p) = 0 := fun p => constantCoeff_subst_zero (hg _) (hY.exc _)
  have hes := hasSubst_of_constantCoeff_zero he0
  have hadd : ∀ i, constantCoeff (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1) i) = 0 := fun i =>
    constantCoeff_subst_zero (log_add_const hY (hg 0) (hg 1)) (hY.exc i)
  have hA : HasSubst (fun i : κ => (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have k1 : ∀ (j : Fin 2) (F : MvPowerSeries κ C),
      subst e (subst (gp C κ j) F) = subst (fun x => subst (gp C κ j) (Y.ex x)) F := by
    intro j F
    rw [subst_comp_subst_apply (hgs j) hes]
    congr 1
    funext x
    rw [gp, subst_X hes]
  have h1 := congrArg (subst e) hχ
  rw [subst_mul hes, k1, k1, ← subst_comp_subst_apply hex (hgs 0), ← subst_comp_subst_apply hex (hgs 1),
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hadd) hes] at h1
  refine Eq.trans ?_ h1
  rw [subst_comp_subst_apply hex hA]
  congr 1
  funext i
  unfold addP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (log_add_const hY (hg 0) (hg 1))) hes]
  congr 1
  funext x
  rw [subst_add hes, k1, k1, lg_ex hY (hg 0), lg_ex hY (hg 1)]
  rfl

end GlobalTheory.RowLaw.CharGerm

namespace GlobalTheory.RowLaw

open MvPowerSeries GlobalTheory.RowLaw.GermRing GlobalTheory.RowLaw.CharGerm in

theorem upG_mvExp_char_mem_intGerm : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (χ : MvPowerSeries κ C), IntS V χ → MvPowerSeries.constantCoeff χ = 1 → MvPowerSeries.subst (addP X (gp C κ (0 : Fin 2)) (gp C κ 1)) χ = MvPowerSeries.subst (gp C κ (0 : Fin 2)) χ * MvPowerSeries.subst (gp C κ (1 : Fin 2)) χ → ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → upG g (mvExp (∑ x : I g, (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) χ * X.u g x i) • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t := by
  intro C _ V d _ I _ κ _ Y hY H χ hi h0 hχ g S t ht
  haveI := hY.charZero
  rw [intGerm_eq_expInt C V d I κ Y hY H S t ht]
  have hg : ∀ x, constantCoeff (gp C κ g x) = 0 := fun x => constantCoeff_X _
  refine ⟨subst (gp C κ g) χ, intS_subst hg (fun _ => intS_X _) hi, ?_⟩
  have hL : ∀ (g : Fin 2) (i : κ), constantCoeff (∑ c : I g, Y.u g c i •
      (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) = 0 := fun g i => by
    simp [map_sum]
  have hLs := hasSubst_of_constantCoeff_zero (hL g)
  have hes : HasSubst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => constantCoeff_subst_zero (hL _) (hY.exc _)
  have hU0 : ∀ x : I g, constantCoeff (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C) = 0 :=
    fun _ => constantCoeff_X _
  have hUs := hasSubst_of_constantCoeff_zero hU0
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hg) hes]
  have e : (fun s => subst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) (gp C κ g s)) = fun s =>
      subst (fun i : κ => ∑ c : I g, Y.u g c i • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C))
        (Y.ex s) := by
    funext s
    rw [gp, subst_X hes]
    rfl
  rw [e, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hY.exc) hLs, subst_ex_eq_mvExp hY χ h0 hχ,
    (GlobalTheory.mvExp_add_subst_linear C κ).2.2.1 _ _ _ (hL g) (by simp [map_sum])]
  unfold upG
  rw [(GlobalTheory.mvExp_add_subst_linear C (I g)).2.2.1 _ _ _ hU0 (by simp [map_sum])]
  congr 1
  rw [subst_sum_smul hLs, subst_sum_smul hUs]
  simp only [subst_X hLs, subst_X hUs, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

end GlobalTheory.RowLaw
end
