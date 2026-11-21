import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJUnramifiedCosets

section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa MeasureTheory Polynomial Spherical HeckeAlgebra
open scoped ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem hasSum_prod_pow_real (m : ℕ) : ∀ {b : Fin m → ℝ}, (∀ i, 0 ≤ b i) → (∀ i, b i < 1) →
    HasSum (fun l : Fin m → ℕ => ∏ i, b i ^ l i) (∏ i, (1 - b i)⁻¹) := by
  induction m with
  | zero =>
    intro b _ _
    have := hasSum_single (f := fun l : Fin 0 → ℕ => ∏ i, b i ^ l i) 0
      (fun b' hb' => absurd (Subsingleton.elim b' 0) hb')
    simpa using this
  | succ m ihm =>
    intro b h0 h1
    have ih : HasSum (fun l : Fin m → ℕ => ∏ i : Fin m, b i.succ ^ l i) (∏ i : Fin m, (1 - b i.succ)⁻¹) :=
      ihm (fun i => h0 _) (fun i => h1 _)
    have hg : HasSum (fun k : ℕ => b 0 ^ k) (1 - b 0)⁻¹ := hasSum_geometric_of_lt_one (h0 0) (h1 0)
    have hs : Summable fun x : ℕ × (Fin m → ℕ) => b 0 ^ x.1 * ∏ i : Fin m, b i.succ ^ x.2 i :=
      Summable.mul_of_nonneg (f := fun k : ℕ => b 0 ^ k)
        (g := fun l : Fin m → ℕ => ∏ i : Fin m, b i.succ ^ l i) hg.summable ih.summable
        (by intro k; exact pow_nonneg (h0 0) k)
        (by intro l; exact Finset.prod_nonneg fun i _ => pow_nonneg (h0 _) _)
    have hm := HasSum.mul hg ih hs
    have hfun : ((fun l : Fin (m + 1) → ℕ => ∏ i, b i ^ l i) ∘
        (Fin.consEquiv fun _ : Fin (m + 1) => ℕ)) =
        fun x : ℕ × (Fin m → ℕ) => b 0 ^ x.1 * ∏ i : Fin m, b i.succ ^ x.2 i := by
      funext x
      show ∏ i, b i ^ (Fin.cons x.1 x.2 : Fin (m + 1) → ℕ) i = _
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => ℕ).hasSum_iff, hfun, Fin.prod_univ_succ]
    exact hm

theorem hasSum_prod_pow (m : ℕ) : ∀ {b : Fin m → ℂ}, (∀ i, ‖b i‖ < 1) →
    HasSum (fun l : Fin m → ℕ => ∏ i, b i ^ l i) (∏ i, (1 - b i)⁻¹) := by
  induction m with
  | zero =>
    intro b _
    have := hasSum_single (f := fun l : Fin 0 → ℕ => ∏ i, b i ^ l i) 0
      (fun b' hb' => absurd (Subsingleton.elim b' 0) hb')
    simpa using this
  | succ m ihm =>
    intro b h1
    have ih : HasSum (fun l : Fin m → ℕ => ∏ i : Fin m, b i.succ ^ l i) (∏ i : Fin m, (1 - b i.succ)⁻¹) :=
      ihm (fun i => h1 _)
    have hg : HasSum (fun k : ℕ => b 0 ^ k) (1 - b 0)⁻¹ := hasSum_geometric_of_norm_lt_one (h1 0)
    have hn1 : Summable fun k : ℕ => ‖b 0 ^ k‖ := by
      simpa [norm_pow] using (summable_geometric_of_lt_one (norm_nonneg _) (h1 0))
    have hn2 : Summable fun l : Fin m → ℕ => ‖∏ i : Fin m, b i.succ ^ l i‖ := by
      simpa [norm_prod, norm_pow] using (hasSum_prod_pow_real m (b := fun i => ‖b i.succ‖)
        (fun i => norm_nonneg _) (fun i => h1 _)).summable
    have hs : Summable fun x : ℕ × (Fin m → ℕ) => b 0 ^ x.1 * ∏ i : Fin m, b i.succ ^ x.2 i :=
      summable_mul_of_summable_norm (f := fun k : ℕ => b 0 ^ k)
        (g := fun l : Fin m → ℕ => ∏ i : Fin m, b i.succ ^ l i) hn1 hn2
    have hm := HasSum.mul hg ih hs
    have hfun : ((fun l : Fin (m + 1) → ℕ => ∏ i, b i ^ l i) ∘
        (Fin.consEquiv fun _ : Fin (m + 1) => ℕ)) =
        fun x : ℕ × (Fin m → ℕ) => b 0 ^ x.1 * ∏ i : Fin m, b i.succ ^ x.2 i := by
      funext x
      show ∏ i, b i ^ (Fin.cons x.1 x.2 : Fin (m + 1) → ℕ) i = _
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => ℕ).hasSum_iff, hfun, Fin.prod_univ_succ]
    exact hm

theorem hasSum_sum_antidiagonalTuple {m : ℕ} {b : Fin m → ℂ} (h : ∀ i, ‖b i‖ < 1) :
    HasSum (fun k : ℕ => ∑ l ∈ Finset.Nat.antidiagonalTuple m k, ∏ i, b i ^ l i)
      (∏ i, (1 - b i)⁻¹) := by
  have H := hasSum_prod_pow m h
  rw [← (Finset.Nat.sigmaAntidiagonalTupleEquivTuple m).hasSum_iff] at H
  refine H.sigma fun k => ?_
  have h1 := hasSum_fintype
    (fun c : Finset.Nat.antidiagonalTuple m k => ∏ i, b i ^ (c : Fin m → ℕ) i)
  rw [Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple m k)
    (fun l : Fin m → ℕ => ∏ i, b i ^ l i)] at h1
  exact h1

theorem qs_pow_mul_sqrtQ (s : ℂ) (m : ℤ) (k : ℕ) :
    qs F (s + (m : ℂ) / 2) ^ k * sqrtQ F ^ (m * k) = qs F s ^ k := by
  have hq : (0 : ℝ) < (LocalField.residueCard F : ℝ) := by
    exact_mod_cast Nat.card_pos
  have key : qs F ((m : ℂ) / 2) * sqrtQ F ^ m = 1 := by
    have h1 : qs F ((m : ℂ) / 2) =
        (((LocalField.residueCard F : ℝ) ^ (-(m : ℝ) / 2) : ℝ) : ℂ) := by
      rw [qs, Complex.ofReal_cpow hq.le]
      push_cast
      ring_nf
    have h2 : sqrtQ F ^ m = (((LocalField.residueCard F : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) := by
      rw [sqrtQ, ← Complex.ofReal_zpow]
      congr 1
      rw [Real.coe_sqrt, NNReal.coe_natCast, Real.sqrt_eq_rpow, ← Real.rpow_intCast,
        ← Real.rpow_mul (Nat.cast_nonneg _), show (1 / 2 : ℝ) * m = m / 2 by ring]
      rfl
    rw [h1, h2, ← Complex.ofReal_mul, ← Real.rpow_add hq, neg_div, neg_add_cancel, Real.rpow_zero,
      Complex.ofReal_one]
  rw [qs_add, mul_pow, _root_.zpow_mul, zpow_natCast, mul_assoc, ← mul_pow, key, one_pow, mul_one]

variable (F n) in

def integralMatrixSet : Set (Matrix (Fin n) (Fin n) F) :=
  Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (𝒪[F] : Set F)

theorem mem_integralMatrixSet {X : Matrix (Fin n) (Fin n) F} :
    X ∈ integralMatrixSet F n ↔ ∀ i j, X i j ∈ 𝒪[F] :=
  ⟨fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _), fun h i _ j _ => h i j⟩

variable (F n) in

def integralIndicator : Matrix (Fin n) (Fin n) F → ℂ :=
  (integralMatrixSet F n).indicator 1

theorem isSchwartzBruhat_integralIndicator : IsSchwartzBruhat (integralIndicator F n) := by
  have hc : IsCompact (integralMatrixSet F n) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))
  have ho : IsOpen (integralMatrixSet F n) :=
    isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => Valuation.isOpen_integer
  refine ⟨?_, HasCompactSupport.intro hc fun X hX => Set.indicator_of_notMem hX _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro X
  by_cases hX : X ∈ integralMatrixSet F n
  · exact ⟨_, ho, hX, fun Y hY => by
      simp [integralIndicator, Set.indicator_of_mem hY, Set.indicator_of_mem hX]⟩
  · exact ⟨_, hc.isClosed.isOpen_compl, hX, fun Y hY => by
      simp [integralIndicator, Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]⟩

theorem ordDet_nonneg_of_integral {g : GL (Fin n) F} (hg : ∀ i j, g i j ∈ 𝒪[F]) : 0 ≤ ordDet g :=
  ord_nonneg_of_mem_integer (det_mem_integer hg) (det_ne_zero g)

section ZetaNonvanishing₂

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem integral_shell_integralIndicator (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    (f : GL (Fin n) F → ℂ) (s : ℂ) (m : ℕ) :
    ∫ g in {g : GL (Fin n) F | ordDet g = (m : ℤ)},
        integralIndicator F n (g : Matrix (Fin n) (Fin n) F) * f g * detPow g s ∂μ =
      qs F s ^ m * ∫ g, (integralHecke μ m : HeckeAlgebra μ) g * f g ∂μ := by
  rw [← integral_indicator (measurableSet_shell _), ← integral_const_mul]
  congr 1
  funext g
  rw [integralHecke_apply]
  by_cases hg : ordDet g = (m : ℤ)
  · rw [Set.indicator_of_mem (show g ∈ {g : GL (Fin n) F | ordDet g = (m : ℤ)} from hg),
      detPow_eq_qs_zpow, hg, zpow_natCast]
    by_cases hi : ∀ i j, g i j ∈ 𝒪[F]
    · rw [integralIndicator, Set.indicator_of_mem (mem_integralMatrixSet.2 hi),
        Set.indicator_of_mem (show g ∈ integralShell F n m from ⟨hi, hg⟩)]
      simp only [Pi.one_apply]
      ring
    · rw [integralIndicator, Set.indicator_of_notMem (fun h => hi (mem_integralMatrixSet.1 h)),
        Set.indicator_of_notMem (fun h => hi h.1)]
      simp
  · rw [Set.indicator_of_notMem (show g ∉ {g : GL (Fin n) F | ordDet g = (m : ℤ)} from hg),
      Set.indicator_of_notMem (fun h => hg h.2)]
    simp

theorem integral_shell_integralIndicator_of_neg (μ : Measure (GL (Fin n) F))
    (f : GL (Fin n) F → ℂ) (s : ℂ) {k : ℤ} (hk : k < 0) :
    ∫ g in {g : GL (Fin n) F | ordDet g = k},
        integralIndicator F n (g : Matrix (Fin n) (Fin n) F) * f g * detPow g s ∂μ = 0 := by
  rw [← integral_indicator (measurableSet_shell _)]
  have : ({g : GL (Fin n) F | ordDet g = k}.indicator fun g =>
      integralIndicator F n (g : Matrix (Fin n) (Fin n) F) * f g * detPow g s) = fun _ => 0 := by
    funext g
    by_cases hg : ordDet g = k
    · rw [Set.indicator_of_mem (show g ∈ {g : GL (Fin n) F | ordDet g = k} from hg), integralIndicator,
        Set.indicator_of_notMem, zero_mul, zero_mul]
      intro h
      have := ordDet_nonneg_of_integral (mem_integralMatrixSet.1 h)
      omega
    · exact Set.indicator_of_notMem (show g ∉ {g : GL (Fin n) F | ordDet g = k} from hg) _
  rw [this, integral_zero]

theorem integral_mul_matrixCoeff_of_isSatakeParameter {μ : Measure (GL (Fin n) F)}
    [μ.IsHaarMeasure] {z : Fin n → ℂˣ} (hz : IsSatakeParameter π μ z) {v₀ : V}
    (hv₀ : v₀ ∈ fixedVectors π (integralGL F n)) (ℓ₀ : Module.Dual ℂ V)
    (h : SphericalHecke μ (F := F) (n := n)) :
    ∫ g, (h : HeckeAlgebra μ) g * matrixCoeff π v₀ ℓ₀ g ∂μ =
      evalAt z (satakeTransform μ h) * ℓ₀ v₀ := by
  have hs : v₀ ∈ smoothVectors π :=
    mem_smoothVectors_of_mem_fixedVectors (isOpen_integralGL F n) hv₀
  have := dual_heckeAct (μ := μ) (ρ := π) (h : HeckeAlgebra μ).mem hs ℓ₀
  rw [hz h v₀ hv₀, map_smul, smul_eq_mul] at this
  exact this.symm

theorem qs_shift_pow_mul_sqrtQ (s : ℂ) (k : ℕ) :
    qs F (s + ((n : ℂ) - 1) / 2) ^ k * sqrtQ F ^ (((n : ℤ) - 1) * k) = qs F s ^ k := by
  have := qs_pow_mul_sqrtQ (F := F) s ((n : ℤ) - 1) k
  push_cast at this
  exact this

theorem zetaIntegral_sphericalCoeff [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {z : Fin n → ℂˣ}
    (hz : IsSatakeParameter π μ z) {v₀ : V} (hv₀ : v₀ ∈ fixedVectors π (integralGL F n))
    {ℓ₀ : Module.Dual ℂ V} (hℓ₀s : ℓ₀ ∈ smoothVectors (Representation.dual π)) (hℓ₀ : ℓ₀ v₀ = 1) :
    ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re → (∀ i, ‖(z i : ℂ) * qs F s‖ < 1) ∧
      zetaIntegral μ (integralIndicator F n) (matrixCoeff π v₀ ℓ₀) s =
        (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * ∏ i, (1 - (z i : ℂ) * qs F s)⁻¹ := by
  obtain ⟨s₁, hint⟩ := exists_integrable_zetaIntegral hπ μ
  set ε : ℝ := (1 + ∑ i, ‖(z i : ℂ)‖)⁻¹ with hεdef
  have hpos : 0 < 1 + ∑ i, ‖(z i : ℂ)‖ := by positivity
  have hε : 0 < ε := inv_pos.2 hpos
  obtain ⟨s₂, hs₂⟩ := exists_re_of_norm_qs_lt (F := F) hε
  refine ⟨max s₁ s₂, fun s hs => ?_⟩
  have hzs : ∀ i, ‖(z i : ℂ) * qs F s‖ < 1 := fun i => by
    rw [norm_mul]
    have h1 : ‖qs F s‖ < ε := hs₂ s ((le_max_right _ _).trans_lt hs)
    have h2 : ‖(z i : ℂ)‖ ≤ ∑ j, ‖(z j : ℂ)‖ :=
      Finset.single_le_sum (f := fun j => ‖(z j : ℂ)‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    calc ‖(z i : ℂ)‖ * ‖qs F s‖ ≤ (∑ j, ‖(z j : ℂ)‖) * ε :=
          mul_le_mul h2 h1.le (norm_nonneg _) (by positivity)
      _ < (1 + ∑ j, ‖(z j : ℂ)‖) * ε := mul_lt_mul_of_pos_right (by linarith) hε
      _ = 1 := by rw [hεdef, mul_inv_cancel₀ hpos.ne']
  refine ⟨hzs, ?_⟩
  have hI := hint _ isSchwartzBruhat_integralIndicator v₀ ℓ₀ hℓ₀s s ((le_max_left _ _).trans_lt hs)
  have hsum := hasSum_integral_shell μ hI
  rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff fun k hk => by
    have hk' : k < 0 := by
      by_contra hc
      exact hk ⟨k.toNat, Int.toNat_of_nonneg (not_lt.1 hc)⟩
    exact integral_shell_integralIndicator_of_neg μ _ _ hk'] at hsum
  set c : ℂ := (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)
  have hterm : ∀ m : ℕ, ((fun k : ℤ => ∫ g in {g : GL (Fin n) F | ordDet g = k},
      integralIndicator F n (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v₀ ℓ₀ g *
        detPow g (s + ((n : ℂ) - 1) / 2) ∂μ) ∘ Nat.cast) m =
      c * ∑ l ∈ Finset.Nat.antidiagonalTuple n m, ∏ i, ((z i : ℂ) * qs F s) ^ l i := by
    intro m
    simp only [Function.comp_apply]
    rw [integral_shell_integralIndicator, integral_mul_matrixCoeff_of_isSatakeParameter hz hv₀,
      hℓ₀, mul_one, evalAt_satakeTransform_integralHecke]
    have hprod : ∀ l ∈ Finset.Nat.antidiagonalTuple n m,
        ∏ i, ((z i : ℂ) * qs F s) ^ l i = qs F s ^ m * ∏ i, (z i : ℂ) ^ l i := by
      intro l hl
      rw [← Finset.Nat.mem_antidiagonalTuple.1 hl]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring
    rw [Finset.sum_congr rfl hprod, ← Finset.mul_sum, ← qs_shift_pow_mul_sqrtQ (n := n) s m]
    ring
  have hfun : ((fun k : ℤ => ∫ g in {g : GL (Fin n) F | ordDet g = k},
      integralIndicator F n (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v₀ ℓ₀ g *
        detPow g (s + ((n : ℂ) - 1) / 2) ∂μ) ∘ Nat.cast) = fun m : ℕ =>
      c * ∑ l ∈ Finset.Nat.antidiagonalTuple n m, ∏ i, ((z i : ℂ) * qs F s) ^ l i := funext hterm
  rw [hfun] at hsum
  rw [zetaIntegral]
  have hgen := (hasSum_sum_antidiagonalTuple hzs).mul_left c
  exact hsum.unique hgen

theorem natDegree_prod_one_sub {m : ℕ} (z : Fin m → ℂˣ) :
    (∏ i, (1 - C (z i : ℂ) * X)).natDegree = m := by
  rw [natDegree_prod _ _ fun i _ => ?_]
  · have : ∀ i, (1 - C (z i : ℂ) * X).natDegree = 1 := fun i => by
      have h1 : (C (z i : ℂ) * X).natDegree = 1 := natDegree_C_mul_X _ (Units.ne_zero _)
      rw [sub_eq_neg_add, natDegree_add_eq_left_of_natDegree_lt] <;> simp [natDegree_neg, h1]
    simp [this]
  · intro h
    have := congrArg (eval 0) h
    simp at this

theorem LPolynomial_eq_prod_of_isSatakeParameter [NeZero n] [π.IsIrreducible]
    (hπ : IsAdmissible π) (hK : fixedVectors π (integralGL F n) ≠ ⊥) (μ : Measure (GL (Fin n) F))
    [μ.IsHaarMeasure] {z : Fin n → ℂˣ} (hz : IsSatakeParameter π μ z) :
    LPolynomial π = ∏ i, (1 - C (z i : ℂ) * X) := by
  classical

  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  obtain ⟨f0, hf0⟩ : ∃ f0 : Module.Dual ℂ (fixedVectors π (integralGL F n)), f0 ⟨v₀, hv₀⟩ = 1 := by
    have hne : (⟨v₀, hv₀⟩ : fixedVectors π (integralGL F n)) ≠ 0 :=
      fun h => h0 (congrArg Subtype.val h)
    have hnot : ¬ ∀ g : Module.Dual ℂ (fixedVectors π (integralGL F n)), g ⟨v₀, hv₀⟩ = 0 :=
      fun h => hne ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
    obtain ⟨g, hg⟩ := not_forall.1 hnot
    exact ⟨(g ⟨v₀, hv₀⟩)⁻¹ • g, by simp [hg]⟩
  set ℓ₀ : Module.Dual ℂ V := f0 ∘ₗ fixedProj π hπ.1 hKc hKo with hℓdef
  have hℓK : ∀ k ∈ integralGL F n, ∀ x, ℓ₀ (π k x) = ℓ₀ x := fun k hk x => by
    simp only [ℓ₀, LinearMap.coe_comp, Function.comp_apply, fixedProj_apply_act hπ.1 hKc hKo hk]
  have hℓs : ℓ₀ ∈ smoothVectors (Representation.dual π) :=
    mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hℓK)
  have hℓv : ℓ₀ v₀ = 1 := by
    have : fixedProj π hπ.1 hKc hKo v₀ = ⟨v₀, hv₀⟩ :=
      Subtype.ext (fixedProj_apply_of_mem hπ.1 hKc hKo hv₀)
    simp only [ℓ₀, LinearMap.coe_comp, Function.comp_apply, this, hf0]

  set Q : ℂ[X] := ∏ i, (1 - C (z i : ℂ) * X) with hQdef
  set c : ℂ := (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) with hcdef
  have hc : c ≠ 0 := by
    have : 0 < μ.real (integralGL F n : Set (GL (Fin n) F)) :=
      ENNReal.toReal_pos (hKo.measure_ne_zero μ ⟨1, (integralGL F n).one_mem⟩)
        hKc.measure_lt_top.ne
    rw [hcdef]
    exact_mod_cast this.ne'
  obtain ⟨s₀, hZ⟩ := zetaIntegral_sphericalCoeff hπ μ hz hv₀ hℓs hℓv
  have hQeval : ∀ x : ℂ, Q.eval x = ∏ i, (1 - (z i : ℂ) * x) := fun x => by
    simp [hQdef, eval_prod]
  have hmem : algebraMap ℂ[X] (RatFunc ℂ) (C c) / algebraMap ℂ[X] (RatFunc ℂ) Q ∈ zetaSet π μ := by
    refine ⟨integralIndicator F n, v₀, ℓ₀, isSchwartzBruhat_integralIndicator, hℓs, s₀,
      fun s hs => ?_⟩
    obtain ⟨hzs, hZs⟩ := hZ s hs
    have hQs : Q.eval (qs F s) ≠ 0 := by
      rw [hQeval]
      refine Finset.prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 fun h => ?_
      have := hzs i
      rw [← h, norm_one] at this
      exact lt_irrefl _ this
    rw [hZs, eval_div_algebraMap _ _ hQs, eval_C, hQeval, Finset.prod_inv_distrib, div_eq_mul_inv]

  obtain ⟨hP0, hP⟩ := LPolynomial_spec hπ μ
  obtain ⟨L, hL, hRL⟩ := (hP _).1 (Submodule.subset_span hmem)
  have hQ0 : Q.eval 0 = 1 := by simp [hQeval]
  have hdvd : Q ∣ LPolynomial π := by
    refine dvd_of_inv_eq_laurent_div (P := LPolynomial π) (P' := Q) (by rw [hQ0]; exact one_ne_zero)
      (L := algebraMap ℂ[X] (RatFunc ℂ) (C c⁻¹) * L)
      (Subalgebra.mul_mem _ (algebraMap_mem_laurentSubalgebra _) hL) ?_
    rw [mul_div_assoc, ← hRL, ← mul_div_assoc, ← map_mul, ← C_mul, inv_mul_cancel₀ hc, C_1, map_one,
      one_div]

  have hPn := natDegree_LPolynomial_le (π := π) hπ
  have hQn : Q.natDegree = n := natDegree_prod_one_sub z
  have hPne : LPolynomial π ≠ 0 := fun h => by rw [h, eval_zero] at hP0; exact zero_ne_one hP0
  have hQne : Q ≠ 0 := fun h => by rw [h, eval_zero] at hQ0; exact zero_ne_one hQ0
  obtain ⟨A, hA⟩ := hdvd
  have hAne : A ≠ 0 := fun h => hPne (by rw [hA, h, mul_zero])
  have hAdeg : A.natDegree = 0 := by
    have := natDegree_mul hQne hAne
    rw [← hA] at this
    omega
  rw [eq_C_of_natDegree_eq_zero hAdeg] at hA
  have hA0 := congrArg (eval 0) hA
  rw [eval_mul, eval_C, hP0, hQ0, one_mul] at hA0
  rw [hA, ← hA0, C_1, mul_one]

theorem LFunction_eq_prod_of_isSatakeParameter [NeZero n] [π.IsIrreducible]
    (hπ : IsAdmissible π) (hK : fixedVectors π (integralGL F n) ≠ ⊥) (μ : Measure (GL (Fin n) F))
    [μ.IsHaarMeasure] {z : Fin n → ℂˣ} (hz : IsSatakeParameter π μ z) (s : ℂ) :
    LFunction π s = ∏ i, (1 - (z i : ℂ) * qs F s)⁻¹ := by
  rw [LFunction, LPolynomial_eq_prod_of_isSatakeParameter hπ hK μ hz, eval_prod,
    ← Finset.prod_inv_distrib]
  simp

end ZetaNonvanishing₂

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
open MeasureTheory Filter Set Topology Metric
open scoped ValuativeRel

namespace GroundTheory.Automorphic

noncomputable section

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Polynomial Spherical HeckeAlgebra

def homSum (m : ℕ) (b : Fin m → ℂ) (k : ℕ) : ℂ :=
  ∑ l ∈ Finset.Nat.antidiagonalTuple m k, ∏ i, b i ^ l i

theorem homSum_mul (m : ℕ) (b : Fin m → ℂ) (t : ℂ) (k : ℕ) :
    homSum m (fun i ↦ t * b i) k = t ^ k * homSum m b k := by
  unfold homSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [← Finset.Nat.mem_antidiagonalTuple.1 hl]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem norm_lt_one_of_summable {m : ℕ} {b : Fin m → ℂ} (h : Summable fun k ↦ ‖homSum m b k‖) (i : Fin m) :
    ‖b i‖ < 1 := by
  set P : ℂ → ℂ := fun t ↦ ∑' k, homSum m b k * t ^ k with hPdef
  set Q : ℂ → ℂ := fun t ↦ ∏ j, (1 - t * b j) with hQdef
  set R : ℂ → ℂ := fun t ↦ Q t * P t with hRdef
  have hterm : ∀ k, ∀ t ∈ closedBall (0 : ℂ) 1, ‖homSum m b k * t ^ k‖ ≤ ‖homSum m b k‖ := by
    intro k t ht
    rw [norm_mul, norm_pow]
    have ht1 : ‖t‖ ≤ 1 := by simpa using ht
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ht1)
  have hPd : DifferentiableOn ℂ P (ball 0 1) :=
    Complex.differentiableOn_tsum_of_summable_norm h
      (fun k ↦ ((differentiable_const _).mul (differentiable_pow k)).differentiableOn) isOpen_ball
      (fun k t ht ↦ hterm k t (ball_subset_closedBall ht))
  have hPc : ContinuousOn P (closedBall 0 1) :=
    continuousOn_tsum (fun k ↦ (continuous_const.mul (continuous_pow k)).continuousOn) h hterm
  have hQd : Differentiable ℂ Q := by
    rw [hQdef]
    fun_prop
  have hRa : AnalyticOnNhd ℂ R (ball 0 1) := (hQd.differentiableOn.mul hPd).analyticOnNhd isOpen_ball
  have hRc : ContinuousOn R (closedBall 0 1) := hQd.continuous.continuousOn.mul hPc

  set ε : ℝ := (1 + ∑ j, ‖b j‖)⁻¹ with hεdef
  have hpos : 0 < 1 + ∑ j, ‖b j‖ := by positivity
  have hε : 0 < ε := inv_pos.2 hpos
  have hnear : ∀ t : ℂ, ‖t‖ < ε → R t = 1 := by
    intro t ht
    have hsmall : ∀ j, ‖t * b j‖ < 1 := fun j ↦ by
      rw [norm_mul]
      have h2 : ‖b j‖ ≤ ∑ j, ‖b j‖ :=
        Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun j _ ↦ norm_nonneg _) (Finset.mem_univ j)
      calc ‖t‖ * ‖b j‖ ≤ ε * ∑ j, ‖b j‖ := mul_le_mul ht.le h2 (norm_nonneg _) hε.le
        _ < ε * (1 + ∑ j, ‖b j‖) := mul_lt_mul_of_pos_left (by linarith) hε
        _ = 1 := by rw [hεdef, inv_mul_cancel₀ hpos.ne']
    have hs := hasSum_sum_antidiagonalTuple hsmall
    have hP : P t = ∏ j, (1 - t * b j)⁻¹ := by
      rw [← hs.tsum_eq, hPdef]
      show ∑' k, homSum m b k * t ^ k = _
      congr 1
      funext k
      rw [← homSum, homSum_mul, mul_comm]
    have hne : ∀ j, 1 - t * b j ≠ 0 := fun j hj ↦ by
      have := hsmall j
      rw [← sub_eq_zero.1 hj, norm_one] at this
      exact lt_irrefl _ this
    simp only [hRdef, hQdef]
    rw [hP, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ ↦ mul_inv_cancel₀ (hne j)
  have hev : R =ᶠ[𝓝 0] fun _ ↦ (1 : ℂ) :=
    Filter.eventually_of_mem (ball_mem_nhds 0 hε) fun t ht ↦ hnear t (by simpa using ht)
  have hball : EqOn R (fun _ ↦ (1 : ℂ)) (ball 0 1) :=
    hRa.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const (convex_ball 0 1).isPreconnected
      (mem_ball_self one_pos) hev
  have hclosed : EqOn R (fun _ ↦ (1 : ℂ)) (closedBall 0 1) :=
    hball.of_subset_closure hRc continuousOn_const ball_subset_closedBall
      (by rw [closure_ball (0 : ℂ) one_ne_zero])
  by_contra hi
  push Not at hi
  have hb0 : b i ≠ 0 := fun h0 ↦ by rw [h0, norm_zero] at hi; linarith
  have hmem : (b i)⁻¹ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_inv]
    exact inv_le_one_of_one_le₀ hi
  have h1 := hclosed hmem
  have h0 : Q (b i)⁻¹ = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [inv_mul_cancel₀ hb0, sub_self])
  simp only [hRdef, h0, zero_mul] at h1
  exact zero_ne_one h1

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem zetaIntegral_sphericalCoeff_of_integrable (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {z : Fin n → ℂˣ} (hz : IsSatakeParameter π μ z) {v₀ : V}
    (hv₀ : v₀ ∈ fixedVectors π (integralGL F n)) {ℓ₀ : Module.Dual ℂ V} (hℓ₀ : ℓ₀ v₀ = 1) {s : ℂ}
    (hI : Integrable (fun g : GL (Fin n) F ↦ integralIndicator F n (g : Matrix (Fin n) (Fin n) F) *
      matrixCoeff π v₀ ℓ₀ g * detPow g (s + ((n : ℂ) - 1) / 2)) μ) :
    (∀ i, ‖(z i : ℂ) * qs F s‖ < 1) ∧
      zetaIntegral μ (integralIndicator F n) (matrixCoeff π v₀ ℓ₀) s =
        (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * ∏ i, (1 - (z i : ℂ) * qs F s)⁻¹ := by
  set H : GL (Fin n) F → ℂ := fun g : GL (Fin n) F ↦ integralIndicator F n (g : Matrix (Fin n) (Fin n) F) *
      matrixCoeff π v₀ ℓ₀ g * detPow g (s + ((n : ℂ) - 1) / 2) with hHdef
  set w : Fin n → ℂ := fun i ↦ (z i : ℂ) * qs F s with hwdef
  set c : ℂ := (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) with hcdef
  have hcpos : 0 < μ.real (integralGL F n : Set (GL (Fin n) F)) :=
    ENNReal.toReal_pos ((isOpen_integralGL F n).measure_pos μ ⟨1, (integralGL F n).one_mem⟩).ne'
      (isCompact_integralGL F n).measure_lt_top.ne
  have hterm : ∀ m : ℕ, ∫ g in {g : GL (Fin n) F | ordDet g = (m : ℤ)}, H g ∂μ = c * homSum n w m := by
    intro m
    rw [hHdef, integral_shell_integralIndicator, integral_mul_matrixCoeff_of_isSatakeParameter hz hv₀,
      hℓ₀, mul_one, evalAt_satakeTransform_integralHecke]
    have hprod : ∀ l ∈ Finset.Nat.antidiagonalTuple n m,
        ∏ i, ((z i : ℂ) * qs F s) ^ l i = qs F s ^ m * ∏ i, (z i : ℂ) ^ l i := by
      intro l hl
      rw [← Finset.Nat.mem_antidiagonalTuple.1 hl]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring
    rw [homSum, Finset.sum_congr rfl hprod, ← Finset.mul_sum, ← qs_shift_pow_mul_sqrtQ (n := n) s m]
    ring

  have hnorm : Summable fun m : ℕ ↦ ‖homSum n w m‖ := by
    have hIn : Integrable (fun g ↦ ((‖H g‖ : ℝ) : ℂ)) μ := hI.norm.ofReal
    have h1 := (hasSum_integral_shell μ hIn).summable
    have h2 : Summable fun k : ℤ ↦ ∫ g in {g : GL (Fin n) F | ordDet g = k}, ‖H g‖ ∂μ := by
      rw [← Complex.summable_ofReal]
      refine h1.congr fun k ↦ ?_
      exact integral_complex_ofReal
    have h3 := h2.comp_injective Nat.cast_injective
    refine Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_)
      (h3.mul_left (μ.real (integralGL F n : Set (GL (Fin n) F)))⁻¹)
    have hle := norm_integral_le_integral_norm (μ := μ.restrict {g : GL (Fin n) F | ordDet g = (m : ℤ)}) H
    rw [hterm m, norm_mul, hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos] at hle
    simp only [Function.comp_apply]
    rw [le_inv_mul_iff₀ hcpos]
    exact hle
  have hw := norm_lt_one_of_summable hnorm
  refine ⟨hw, ?_⟩
  have hsum := hasSum_integral_shell μ hI
  rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff fun k hk ↦ by
    have hk' : k < 0 := by
      by_contra hc
      exact hk ⟨k.toNat, Int.toNat_of_nonneg (not_lt.1 hc)⟩
    exact integral_shell_integralIndicator_of_neg μ _ _ hk'] at hsum
  have hfun : ((fun k : ℤ ↦ ∫ g in {g : GL (Fin n) F | ordDet g = k},
      integralIndicator F n (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v₀ ℓ₀ g *
        detPow g (s + ((n : ℂ) - 1) / 2) ∂μ) ∘ Nat.cast) = fun m : ℕ ↦ c * homSum n w m :=
    funext hterm
  rw [hfun] at hsum
  rw [zetaIntegral]
  have hgen := (hasSum_sum_antidiagonalTuple hw).mul_left c
  exact hsum.unique hgen

end GodementJacquet

end

end GroundTheory.Automorphic
end
