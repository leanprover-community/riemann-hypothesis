import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqH

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GaugeR

def IsScaled {Y : Scheme.{0}} {M : LB Y} (u : Γ(Y, ⊤)ˣ) (t t' : LB.Gen M) : Prop :=
  ∀ j, t'.s j = res le_top u * t.s j

def pullUnit {Y Z : Scheme.{0}} (h : Z ⟶ Y) (u : Γ(Y, ⊤)ˣ) : Γ(Z, ⊤)ˣ :=
  pullU h ⊤ u

variable {X Y Z : Scheme.{0}} (L : LB X)

theorem ratio_of_gen (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t t' : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (ht' : t'.IsGen) : ∃ u, IsScaled u t t' := by
  exact gen_ratio (LB.LinComb L φ ε) (wchart_cover L hL φ) t' t ht' ht

theorem scaled_one {M : LB Y} (t : LB.Gen M) : IsScaled 1 t t := by
  intro j
  rw [map_one, one_mul]

theorem scaled_mul {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) {u v : Γ(Y, ⊤)ˣ} {t t' : LB.Gen (LB.LinComb L φ ε)}
    {s s' : LB.Gen (LB.LinComb L φ' ε')} (h1 : IsScaled u t t') (h2 : IsScaled v s s') :
    IsScaled (u * v) (LB.mulGen L φ ε φ' ε' t s) (LB.mulGen L φ ε φ' ε' t' s') := by
  have h1' : ∀ j, t'.s j = res le_top u * t.s j := h1
  have h2' : ∀ j, s'.s j = res le_top v * s.s j := h2
  intro j
  simp only [LB.mulGen]
  erw [h1' (j ∘ Sum.inl), h2' (j ∘ Sum.inr)]
  simp only [map_mul]
  erw [res_res, res_res]
  rw [mul_mul_mul_comm]
  rfl


theorem pullUnit_res (h : Z ⟶ Y) {V : Y.Opens} {W : Z.Opens} (hWV : W ≤ h ⁻¹ᵁ V) (u : Γ(Y, ⊤)ˣ) :
    res hWV (pullU h V (res (le_top : V ≤ ⊤) u)) = res le_top (pullUnit h u) := by
  rw [ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, res_res]
  rfl

theorem scaled_pull {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) {u : Γ(Y, ⊤)ˣ}
    {t t' : LB.Gen (LB.LinComb L φ ε)} (hs : IsScaled u t t') :
    IsScaled (pullUnit h u) (LB.pullGen L φ ε t h) (LB.pullGen L φ ε t' h) := by
  have hs' : ∀ j, t'.s j = res le_top u * t.s j := hs
  intro j
  simp only [LB.pullGen]
  erw [hs' j, map_mul, map_mul, pullUnit_res]

theorem corr_scaled (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t₁ t₁' : LB.Gen (LB.LinComb L φ ε))
    (t₂ t₂' : LB.Gen (LB.LinComb L φ' ε')) (U₁ U₂ : Γ(Y, ⊤)ˣ) (h₁ : IsScaled U₁ t₁ t₁')
    (h₂ : IsScaled U₂ t₂ t₂') (c : LB.Gen.Corr L φ ε φ' ε' t₁ t₂) (c' : LB.Gen.Corr L φ ε φ' ε' t₁' t₂') :
    U₁ = U₂ := by
  classical
  have h₁' : ∀ j, t₁'.s j = res le_top U₁ * t₁.s j := h₁
  have h₂' : ∀ j, t₂'.s j = res le_top U₂ * t₂.s j := h₂
  have key : ∀ {U V : Y.Opens} (hle : V ≤ U) (a b : Γ(Y, U)ˣ), res hle (a * b) = res hle a * res hle b :=
    fun hle a b => map_mul _ a b
  have hch : ∀ (ψ : Y ⟶ X) (y : Y), ∃ i, ψ y ∈ L.U i := by
    intro ψ y
    have hy := wchart_cover L hL (fun _ : Fin 1 => ψ) (show y ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨j 0, Set.mem_iInter.1 hj 0⟩
  apply Units.ext
  have hcov : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧
      (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (U₁ : Γ(Y, ⊤)) =
        (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (U₂ : Γ(Y, ⊤)) := by
    intro y
    choose ch hc using fun ψ => hch ψ y
    let j : K → L.ι := fun k => ch (φ k)
    let j' : K' → L.ι := fun k => ch (φ' k)
    have hj : LB.Coh L φ j := fun k1 k2 e => show ch (φ k1) = ch (φ k2) by rw [e]
    have hj' : LB.Coh L φ' j' := fun k1 k2 e => show ch (φ' k1) = ch (φ' k2) by rw [e]
    have hjj : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' e => show ch (φ k) = ch (φ' k') by rw [e]
    have hyW : y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' :=
      ⟨Set.mem_iInter.2 fun k => hc (φ k), Set.mem_iInter.2 fun k => hc (φ' k)⟩
    have E := c j j' hj hj' hjj
    have E' := c' j j' hj hj' hjj
    rw [h₁' j, h₂' j'] at E'
    erw [key, key, res_res, res_res, E] at E'
    have E2 := mul_right_cancel E'
    exact ⟨_, hyW, congrArg Units.val E2⟩
  choose W hyW hW using hcov
  exact TopCat.Sheaf.eq_of_locally_eq' Y.sheaf W ⊤ (fun y => homOfLE le_top)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyW y⟩) _ _ hW

theorem corr_scaled_left (hL : L.IsLB) (ψ : Y ⟶ X) (a : ℤ) {K' : Type} [Fintype K'] (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (τ τ' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a))
    (t₂ t₂' : LB.Gen (LB.LinComb L φ' ε')) (U : Γ(Y, ⊤)ˣ) (h₂ : IsScaled U t₂ t₂')
    (c : LB.Gen.Corr L _ _ _ _ τ t₂) (c' : LB.Gen.Corr L _ _ _ _ τ' t₂') : IsScaled U τ τ' := by
  let τ'' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a) :=
    ⟨fun j => res le_top U * τ.s j⟩
  have h₂' : ∀ j, t₂'.s j = res le_top U * t₂.s j := h₂
  have hc'' : LB.Gen.Corr L _ _ _ _ τ'' t₂' := by
    intro j j' hj hj' hm
    have := c j j' hj hj' hm
    show res _ (res le_top U * τ.s j) = res _ (t₂'.s j')
    rw [h₂' j']
    erw [map_mul, map_mul, this, res_res, res_res]
    rfl
  have he := GermFun.gen_eq_of_corr L hL ψ a φ' ε' τ'' τ' t₂' hc'' c'
  intro j
  rw [← he]

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPolynomial Formalism.L2.Pj

namespace GaugeR

variable {R ι : Type} [CommRing R]

theorem monomial_mem_orig_pow (e : ι →₀ ℕ) (a : R) : monomial e a ∈ orig R ι ^ e.degree := by
  rw [monomial_eq]
  apply Ideal.mul_mem_left
  unfold Finsupp.prod
  have hpow : orig R ι ^ e.degree = ∏ i ∈ e.support, orig R ι ^ e i := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hpow]
  exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (show (X i : MvPolynomial ι R) ∈ orig R ι from Ideal.subset_span (Set.mem_range_self i)) _)

theorem mem_orig_pow_of_coeff (n : ℕ) (p : MvPolynomial ι R) (h : ∀ e, e.degree < n → coeff e p = 0) :
    p ∈ orig R ι ^ n := by
  rw [p.as_sum]
  refine Ideal.sum_mem _ (fun e he => ?_)
  have hn : n ≤ e.degree := by
    by_contra hlt
    push_neg at hlt
    exact (mem_support_iff.mp he) (h e hlt)
  exact Ideal.pow_le_pow_right hn (monomial_mem_orig_pow e _)

variable [Fintype ι] [DecidableEq ι]

theorem psJet_eq_mk (m : ℕ) (f : MvPowerSeries ι R) (p : MvPolynomial ι R)
    (h : ∀ e, e.degree ≤ m → coeff e p = MvPowerSeries.coeff e f) :
    psJet m f = Ideal.Quotient.mk _ p := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of_coeff
  intro e he
  rw [coeff_sub, GermFun.coeff_psTrunc m f e (by omega), h e (by omega), sub_self]

theorem psJet_mul (m : ℕ) (f g : MvPowerSeries ι R) : psJet m (f * g) = psJet m f * psJet m g := by
  have key : psJet m (f * g) = Ideal.Quotient.mk _ (psTrunc m f * psTrunc m g) := by
    refine psJet_eq_mk m _ _ (fun e he => ?_)
    rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hd : x.1.degree + x.2.degree ≤ m := by
      rw [← map_add Finsupp.degree, hx']
      exact he
    rw [GermFun.coeff_psTrunc m f x.1 (by omega), GermFun.coeff_psTrunc m g x.2 (by omega)]
  rw [key, map_mul]
  rfl

theorem psJet_one (m : ℕ) : psJet m (1 : MvPowerSeries ι R) = 1 := by
  rw [psJet_eq_mk m 1 1 (fun e _ => by rw [MvPolynomial.coeff_one, MvPowerSeries.coeff_one]; exact if_congr eq_comm rfl rfl), map_one]

theorem psJet_pow (m : ℕ) (f : MvPowerSeries ι R) (k : ℕ) : psJet m (f ^ k) = psJet m f ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, psJet_one]
  | succ k ih => rw [pow_succ, pow_succ, psJet_mul, ih]

theorem aeval_scale_monomial (s : ι → R) (e : ι →₀ ℕ) (a : R) :
    aeval (fun i => C (s i) * X i) (monomial e a : MvPolynomial ι R) =
      monomial e (a * e.prod fun i k => s i ^ k) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
  rw [map_mul, map_finsuppProd, MvPolynomial.algebraMap_eq]
  ring

theorem coeff_aeval_scale (s : ι → R) (p : MvPolynomial ι R) (e : ι →₀ ℕ) :
    coeff e (aeval (fun i => C (s i) * X i) p) = (e.prod fun i k => s i ^ k) * coeff e p := by
  induction p using MvPolynomial.induction_on' with
  | monomial e' a =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      ring
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem jetMap_mk {ι' : Type} (m : ℕ) (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι')
    (p : MvPolynomial ι R) :
    jetMap φ hφ (Ideal.Quotient.mk (orig R ι ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

theorem jetSubstP_scale (m : ℕ) (s : ι → R) (f : MvPowerSeries ι R) :
    jetSubstP m (fun i => C (s i) * X i) (psJet m f) = psJet m (MvPowerSeries.rescale s f) := by
  unfold jetSubstP psJet
  rw [jetMap_mk]
  simp only [map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_zero, sub_zero]
  symm
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  rw [coeff_aeval_scale, GermFun.coeff_psTrunc m f e he, MvPowerSeries.coeff_rescale]

theorem jetTrunc_psJet (m : ℕ) (f : MvPowerSeries ι R) : jetTrunc (psJet (m + 1) f) = psJet m f := by
  show Ideal.Quotient.mk _ (psTrunc (m + 1) f) = psJet m f
  exact (psJet_eq_mk m f _ (fun e he => GermFun.coeff_psTrunc (m + 1) f e (by omega))).symm

theorem jetAug_psJet (m : ℕ) (f : MvPowerSeries ι R) :
    jetAug (psJet m f) = MvPowerSeries.constantCoeff f := by
  show (MvPolynomial.aeval fun _ => (0 : R)) (psTrunc m f) = _
  rw [show (fun _ : ι => (0 : R)) = 0 from rfl, MvPolynomial.aeval_zero, Algebra.algebraMap_self_apply,
]
  show MvPolynomial.coeff 0 (psTrunc m f) = _
  rw [GermFun.coeff_psTrunc m f 0 (by simp)]
  rfl

theorem exists_ps_of_compat (ρ : ∀ m, Jet R ι m) (h : ∀ m, jetTrunc (ρ (m + 1)) = ρ m) :
    ∃ r : MvPowerSeries ι R, ∀ m, psJet m r = ρ m := by
  classical
  choose P hP using fun m => Ideal.Quotient.mk_surjective (ρ m)
  have hstep : ∀ m, P (m + 1) - P m ∈ orig R ι ^ (m + 1) := by
    intro m
    rw [← Ideal.Quotient.eq]
    have h1 := h m
    rw [← hP (m + 1), ← hP m] at h1
    exact h1
  have hcoef : ∀ n k (e : ι →₀ ℕ), e.degree ≤ n → coeff e (P (n + k)) = coeff e (P n) := by
    intro n k e he
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← ih, ← sub_eq_zero, ← coeff_sub]
      exact GermFun.coeff_eq_zero_of_mem (hstep (n + k)) (by omega)
  refine ⟨fun e => coeff e (P e.degree), fun m => ?_⟩
  rw [← hP m]
  refine psJet_eq_mk m _ _ (fun e he => ?_)
  have h2 := hcoef e.degree (m - e.degree) e le_rfl
  rw [show e.degree + (m - e.degree) = m by omega] at h2
  rw [h2]
  rfl

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
