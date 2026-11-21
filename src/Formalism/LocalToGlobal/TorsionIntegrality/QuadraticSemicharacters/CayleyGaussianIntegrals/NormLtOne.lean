import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactVersion
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.GeneralIntegrality
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd

section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.H

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)

namespace FormalGroupLawNegation

section Formal

variable {K : Type} [Field K] {n : Type} [Fintype n]

theorem cc_lin {σ m : Type} [Fintype m] (c : m → K) {u : m → MvPowerSeries σ K}
    (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) :
    MvPowerSeries.constantCoeff (∑ j, MvPowerSeries.C (c j) * u j) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [map_mul, hu j, mul_zero]

theorem subst_lin {σ ρ m : Type} [Finite σ] [Fintype m] (c : m → K) (u : m → MvPowerSeries σ K)
    {φ : σ → MvPowerSeries ρ K} (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (∑ j, MvPowerSeries.C (c j) * u j) =
      ∑ j, MvPowerSeries.C (c j) * MvPowerSeries.subst φ (u j) := by
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
  rw [← MvPowerSeries.coe_substAlgHom h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom h, MvPowerSeries.subst_C]

theorem subst_tensor4 {ρ : Type} (T : MvPowerSeries n K) {φ : Fin 4 × n → MvPowerSeries ρ K}
    (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (tensor4 T) = ∏ a : Fin 4, MvPowerSeries.subst (fun i => φ (a, i)) T := by
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
  unfold tensor4
  rw [← MvPowerSeries.coe_substAlgHom h, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.coe_substAlgHom h, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _) h]
  congr 1
  funext i
  exact MvPowerSeries.subst_X h _

theorem subst_single_var {σ ρ : Type} [Finite σ] (s : σ) (f : PowerSeries K) {φ : σ → MvPowerSeries ρ K}
    (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (at1 s f) = PowerSeries.subst (φ s) f := by
  unfold at1
  rw [Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X s) hφ,
    MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ)]

theorem left_side {lg linv : PowerSeries K} (h : IsLogPair lg linv) {O : Type} [Semiring O] (τ : O →+* K)
    (γ : Matrix (Fin 4 × n) (Fin 4 × n) O) (B' : Matrix n n K) (M : Matrix (Fin 4 × n) (Fin 4 × n) K)
    (hM : ∀ (a : Fin 4) (i : n) (w : Fin 4 × n), ∑ j, B' i j * τ (γ (a, j) w) = M (a, i) w)
    (T : MvPowerSeries n K) :
    MvPowerSeries.subst (matCoord lg linv τ γ)
        (tensor4 (MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (B' i j) * at1 j lg) T)) =
      MvPowerSeries.subst (fun w => at1 w lg) (linSubst M (tensor4 T)) := by
  have hat : ∀ {σ : Type} (s : σ), MvPowerSeries.constantCoeff (at1 s lg : MvPowerSeries σ K) = 0 :=
    fun s => Formalism.L2.Th1.E.CompatibleChartOperations.constantCoeff_inVar_eq_zero s h.1
  have hmc : ∀ w, MvPowerSeries.constantCoeff (matCoord lg linv τ γ w) = 0 := fun w =>
    Formalism.L2.Th1.C.Pts.constantCoeff_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
  have hB : ∀ i, MvPowerSeries.constantCoeff
      (∑ j, MvPowerSeries.C (B' i j) * (at1 j lg : MvPowerSeries n K)) = 0 :=
    fun i => cc_lin _ fun j => hat j
  have hL : ∀ w, MvPowerSeries.constantCoeff
      (∑ w', MvPowerSeries.C (M w w') * (MvPowerSeries.X w' : MvPowerSeries (Fin 4 × n) K)) = 0 :=
    fun w => cc_lin _ fun j => MvPowerSeries.constantCoeff_X _
  rw [subst_tensor4 _ hmc, linSubst, subst_tensor4 _ hL,
    ← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => hat w), map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hB)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => hmc (a, i)),
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => hL (a, i))
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => hat w)]
  congr 1
  funext i
  rw [subst_lin _ _ fun j => hmc (a, j), subst_lin _ _ fun w => hat w]
  have h1 : ∀ j, MvPowerSeries.subst (fun i => matCoord lg linv τ γ (a, i)) (at1 j lg) =
      ∑ w, MvPowerSeries.C (τ (γ (a, j) w)) * at1 w lg := by
    intro j
    rw [subst_single_var _ _ fun j => hmc (a, j)]
    exact Formalism.L2.Th1.C.Pts.l_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => hat w), ← hM, map_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_assoc]

theorem right_side {lg : PowerSeries K} (hlg : PowerSeries.constantCoeff lg = 0) {m κ : Type} [Fintype m]
    (S : Finset κ) (r : κ → K) (f : κ → m → PowerSeries K) :
    MvPowerSeries.subst (fun w => at1 w lg) (∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w (f x w)) =
      ∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w ((f x w).subst lg) := by
  have hat : ∀ s : m, MvPowerSeries.constantCoeff (at1 s lg : MvPowerSeries m K) = 0 :=
    fun s => Formalism.L2.Th1.E.CompatibleChartOperations.constantCoeff_inVar_eq_zero s hlg
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hat
  rw [← MvPowerSeries.coe_substAlgHom h, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_prod, MvPowerSeries.coe_substAlgHom h, MvPowerSeries.subst_C]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [subst_single_var _ _ hat]
  unfold at1
  rw [Formalism.L2.Th1.C.Pts.subst_subst hlg (MvPowerSeries.constantCoeff_X w)]

end Formal

section Map

variable {K₀ K : Type} [Field K₀] [Field K] (ι : K₀ →+* K) {n : Type} [Fintype n]

theorem map_tensor4 (T : MvPowerSeries n K₀) :
    MvPowerSeries.map ι (tensor4 T) = tensor4 (MvPowerSeries.map ι T) := by
  unfold tensor4
  rw [map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.map_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _)]
  congr 1
  funext i
  exact MvPowerSeries.map_X _ _

theorem map_linSubst {m : Type} [Finite m] (M : Matrix m n K₀) (T : MvPowerSeries m K₀) :
    MvPowerSeries.map ι (linSubst M T) = linSubst (M.map ι) (MvPowerSeries.map ι T) := by
  have hs : MvPowerSeries.HasSubst
      (fun i => ∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X j : MvPowerSeries n K₀)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_lin _ fun j => MvPowerSeries.constantCoeff_X _
  unfold linSubst
  rw [MvPowerSeries.map_subst hs]
  congr 1
  funext i
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X, Matrix.map_apply]

theorem map_sumProd {κ : Type} (S : Finset κ) (r : κ → K₀) (f : κ → n → PowerSeries K₀) :
    MvPowerSeries.map ι (∑ x ∈ S, MvPowerSeries.C (r x) * ∏ w, at1 w (f x w)) =
      ∑ x ∈ S, MvPowerSeries.C (ι (r x)) * ∏ w, at1 w (PowerSeries.map ι (f x w)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_prod, MvPowerSeries.map_C]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  exact Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_inVar ι w _

end Map

end FormalGroupLawNegation

end Formalism.L2.Th1.H
end
end

section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)

namespace FormalGroupLawNegation

section Analytic

variable {n : Type} [Fintype n]

theorem analyticAt_tens4 {θ : (n → ℂ) → ℂ} (h : AnalyticAt ℂ θ 0) : AnalyticAt ℂ (tens4 θ) 0 := by
  unfold tens4
  refine Finset.analyticAt_fun_prod _ fun a _ => ?_
  exact h.comp_of_eq (f := slice a)
    ((ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 × n => ℂ) (a, i)).analyticAt 0)
    rfl

theorem analyticAt_prodFn {f : n → ℂ → ℂ} (h : ∀ i, AnalyticAt ℂ (f i) 0) : AnalyticAt ℂ (prodFn f) 0 := by
  unfold prodFn
  refine Finset.analyticAt_fun_prod _ fun i _ => ?_
  exact (h i).comp_of_eq (f := fun z : n → ℂ => z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) i).analyticAt 0) rfl

theorem analyticAt_opU (L : PeriodPair) (s : ℂ) {θ : ℂ → ℂ} (h : Differentiable ℂ θ) :
    AnalyticAt ℂ (Formalism.L2.Th1.F.opU L s θ) 0 := by
  have h1 : Differentiable ℂ (Formalism.L2.Th1.F.opU L s θ) := by
    unfold Formalism.L2.Th1.F.opU Formalism.L2.Th1.F.herm
    fun_prop
  exact h1.analyticAt 0

theorem taylorMv_sum [DecidableEq n] (hLin : TaylorMvLinear) {κ : Type} (S : Finset κ) (c : κ → ℂ)
    (F : κ → (n → ℂ) → ℂ) (hF : ∀ x, AnalyticAt ℂ (F x) 0) :
    AnalyticAt ℂ (fun z => ∑ x ∈ S, c x * F x z) 0 ∧
      taylorMv (fun z => ∑ x ∈ S, c x * F x z) = ∑ x ∈ S, MvPowerSeries.C (c x) * taylorMv (F x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using analyticAt_const, ?_⟩
    have h0 := (hLin n (fun _ => 0) (fun _ => 0) analyticAt_const analyticAt_const).2 0
    simpa using h0
  | insert a S ha ih =>
    have h1 : AnalyticAt ℂ (fun z => c a * F a z) 0 := analyticAt_const.mul (hF a)
    simp only [Finset.sum_insert ha]
    refine ⟨h1.add ih.1, ?_⟩
    rw [(hLin n _ _ h1 ih.1).1, (hLin n _ _ (hF a) (hF a)).2 (c a), ih.2]

end Analytic

section Arith

theorem norm_coeff {l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) {V : Type} [AddCommGroup V] [Module ℂ V]
    (H : Sesq V) (Λb : AddSubgroup V) (hsd : IsSelfDual H Λb) (β : V → ℂ) (hβ : IsSemiChar H Λb β)
    (n' : ℕ) (hn' : ¬ l ∣ n') (ε : ℂ) (hε : ‖ι ε‖ ≤ 1) (s x : V) (N : ℕ) (hN : 0 < N)
    (hs : (N : ℂ) • s ∈ Λb) (hx : x ∈ Λb) :
    ‖ι (ε * ((Real.sqrt n' : ℝ) : ℂ)⁻¹ * β x
      * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)))‖ ≤ 1 := by
  have h1 : ‖ι (((Real.sqrt n' : ℝ) : ℂ)⁻¹)‖ = 1 := by
    rw [map_inv₀, norm_inv]
    have h2 : ‖ι ((Real.sqrt n' : ℝ) : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← map_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
        Complex.ofReal_natCast, map_natCast]
      exact Formalism.L2.Th1.E.Tor.norm_natCast l hn'
    rw [(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2, inv_one]
  have h2 : ‖ι (β x)‖ = 1 := by
    rcases hβ.1 x hx with h | h <;> simp [h]
  have h3 : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)))‖ = 1 := by
    have hs' : (N : ℂ) • s ∈ dualLat H Λb := by rw [hsd]; exact hs
    obtain ⟨m, hm⟩ := hs' x hx
    have hE : altE H ((N : ℂ) • s) x = N * altE H s x := by simp [altE]
    have hc : (N : ℂ) * (altE H s x : ℂ) = (m : ℂ) := by
      rw [hE] at hm
      exact_mod_cast hm
    have h4 : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)))‖ ^ (2 * N) = 1 := by
      rw [← norm_pow, ← map_pow, ← Complex.exp_nat_mul]
      have h5 : ((2 * N : ℕ) : ℂ) * (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ))
          = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hc
      rw [h5, Complex.exp_int_mul_two_pi_mul_I, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h4
  rw [map_mul, map_mul, map_mul, norm_mul, norm_mul, norm_mul, h1, h2, h3, mul_one, mul_one, mul_one]
  exact hε

theorem trans_mem (L : PeriodPair) {m : Type} (Λb : AddSubgroup (m → ℂ)) (s x : m → ℂ) (N : ℕ)
    (hs : (N : ℂ) • s ∈ Λb) (hx : x ∈ Λb) (w : m) :
    ((N * relIdx (stdLat L m) Λb : ℕ) : ℂ) * (s w + x w) ∈ L.lattice := by
  have h1 : (N : ℂ) • (s + x) ∈ Λb := by
    rw [smul_add]
    exact Λb.add_mem hs (by rw [Nat.cast_smul_eq_nsmul]; exact Λb.nsmul_mem hx N)
  have h2 : relIdx (stdLat L m) Λb • ((N : ℂ) • (s + x)) ∈ stdLat L m :=
    AddSubgroup.nsmul_relIndex_mem (stdLat L m) h1
  have h3 := (AddSubgroup.mem_pi _).1 h2 w (Set.mem_univ w)
  have h4 : ((N * relIdx (stdLat L m) Λb : ℕ) : ℂ) * (s w + x w)
      = (relIdx (stdLat L m) Λb • ((N : ℂ) • (s + x))) w := by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [h4]
  exact h3

theorem smul_img_mem {n : Type} [Fintype n] (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (t : n → ℂ) (c : ℂ) (h : c • t ∈ Λ) :
    c • g (fun w => t w.2) ∈ imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) :=
  ⟨c • fun w : Fin 4 × n => t w.2, fun _ => h, by simp⟩

end Arith

end FormalGroupLawNegation

open FormalGroupLawNegation

theorem quadraticSemicharacterIdentity_of_reformulated_of_taylorMv_of_repsExist_of_opUAnalytic (hA : quadraticSemicharacterIdentityReformulated₂) (hLin : TaylorMvLinear) (hComp : TaylorMvComp)
    (hProd : TaylorMvProd) (hT4 : TaylorMvTens4) (hR : RepsExist) (hAn : OpUAnalytic) : quadraticSemicharacterIdentity := by
  intro l _ L ι ω₀ lg linv ph hlp hph hTI n _ _ h Λ α β g hD hln ε hε θ hθ hten t N hN hlN hNt O _ τ γ B' hB
  classical
  obtain ⟨S, hS⟩ := (hR _ (stdLat L (Fin 4 × n))
    (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) hD.idx₁).1
  have hNt' := smul_img_mem Λ g t (N : ℂ) hNt

  have hF0 : AnalyticAt ℂ (opU (matH h) t θ) 0 := hAn _ (matH h) t θ hθ.1 0 (Set.mem_univ _)
  have hth : Differentiable ℂ (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) := (Formalism.L2.Th1.F.th0Basic L ω₀ hD.per hD.half).1
  let M : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
    LinearMap.toMatrix' (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
  let c : (Fin 4 × n → ℂ) → ℂ := fun x =>
    ε * ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
              (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ * β x
            * Complex.exp (-(Real.pi : ℂ) * Complex.I
                * (altE (stdH L (Fin 4 × n)) (g fun w => t w.2) x : ℂ))
  let f : (Fin 4 × n → ℂ) → Fin 4 × n → ℂ → ℂ := fun x w =>
    Formalism.L2.Th1.F.opU L (g (fun w => t w.2) w + x w) (Formalism.L2.Th1.F.th0 L (ω₀ / 2))
  have hf : ∀ x w, AnalyticAt ℂ (f x w) 0 := fun x w => analyticAt_opU L _ hth
  have hfun : (fun y => tens4 (opU (matH h) t θ) (M.mulVec y)) = fun y => ∑ x ∈ S, c x * prodFn (f x) y := by
    funext y
    rw [LinearMap.toMatrix'_mulVec]
    exact hA L ω₀ n h Λ α β g hD ε θ hten S hS t y
  have hT : linSubst M (tensor4 (taylorMv (opU (matH h) t θ))) =
      ∑ x ∈ S, MvPowerSeries.C (c x) * ∏ w, at1 w (Formalism.L2.Th1.F.taylor0 (f x w)) := by
    rw [← hT4 n _ hF0, ← hComp _ _ M _ (analyticAt_tens4 hF0), hfun,
      (taylorMv_sum hLin S c _ fun x => analyticAt_prodFn (hf x)).2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hProd _ _ (hf x)]
  have hM : ∀ (a : Fin 4) (i : n) (w : Fin 4 × n),
      ∑ j, B' i j * τ (γ (a, j) w) = (M.map (ι : ℂ →+* ℂ_[l])) (a, i) w := by
    intro a i w
    rw [hB a i w]
    rfl
  have hexp : ∀ X : PowerSeries ℂ_[l], (mvExp (-ph) : PowerSeries ℂ_[l]) * (mvExp ph * X) = X := by
    intro X
    rw [← mul_assoc]
    have h1 : (mvExp (-ph) : PowerSeries ℂ_[l]) * mvExp ph = 1 :=
      Formalism.L2.Th1.C.mvExp_neg (σ := Unit) (f := ph) hph
    rw [h1, one_mul]
  refine ⟨{x // x ∈ S}, inferInstance, fun x => ι (c x), fun x w => (mvExp ph : PowerSeries ℂ_[l]) *
      (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 (f x w))).subst lg, ?_, ?_, ?_⟩
  · intro x
    exact norm_coeff ι _ _ hD.selfDual β hD.betaSemi _ hln ε hε _ _ N hN hNt' (hS.1 x x.2)
  · intro x w
    refine hTI _ (N * relIdx (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) (Nat.mul_pos hN (Nat.pos_of_ne_zero hD.idx₁)) ?_
      (trans_mem L _ _ _ N hNt' (hS.1 x x.2) w)
    intro hd
    rcases (Nat.Prime.dvd_mul Fact.out).1 hd with h1 | h1
    · exact hlN h1
    · exact hln h1
  · unfold thetaU thetaProd
    rw [left_side hlp τ γ B' _ hM, ← map_tensor4, ← map_linSubst, hT, map_sumProd, right_side hlp.1]
    simp only [hexp]
    exact (Finset.sum_coe_sort S fun x => MvPowerSeries.C (ι (c x)) * ∏ w, at1 w
      ((PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 (f x w))).subst lg)).symm



end Formalism.L2.Th1.H
end
end
