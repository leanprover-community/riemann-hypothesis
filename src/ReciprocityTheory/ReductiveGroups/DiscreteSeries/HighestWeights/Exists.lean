import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA

section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem hc_param_gap_ge_index (lam : Fin n → ℝ) (hlam : IsHCParam lam) (a b : Fin n) (hab : a ≤ b) :
    ((b : ℕ) : ℝ) - (a : ℕ) ≤ lam a - lam b := by

  have gap : ∀ i j : Fin n, i < j → lam j + 1 ≤ lam i := by
    intro i j hij
    obtain ⟨mi, hi⟩ := hlam.2 i
    obtain ⟨mj, hj⟩ := hlam.2 j
    have hlt : lam j < lam i := hlam.1 hij
    have h1 : (mj : ℝ) < mi := by linarith
    have h2 : mj < mi := by exact_mod_cast h1
    have h3 : (mj : ℝ) + 1 ≤ mi := by
      have := Int.add_one_le_of_lt h2
      exact_mod_cast this
    linarith
  have key : ∀ k : ℕ, ∀ c : Fin n, a ≤ c → (c : ℕ) = a + k → ((c : ℕ) : ℝ) - (a : ℕ) ≤ lam a - lam c := by
    intro k
    induction k with
    | zero =>
      intro c _ hc
      have : c = a := Fin.ext (by omega)
      subst this
      simp
    | succ k ih =>
      intro c hac hc
      have hc1 : (c : ℕ) - 1 < n := by omega
      let c' : Fin n := ⟨(c : ℕ) - 1, hc1⟩
      have hac' : a ≤ c' := Fin.le_def.mpr (by show (a : ℕ) ≤ (c : ℕ) - 1; omega)
      have hc' : (c' : ℕ) = a + k := by show (c : ℕ) - 1 = _; omega
      have h1 := ih c' hac' hc'
      have h2 := gap c' c (Fin.lt_def.mpr (by show (c : ℕ) - 1 < c; omega))
      have h3 : ((c : ℕ) : ℝ) = ((c' : ℕ) : ℝ) + 1 := by
        rw [show (c : ℕ) = (c' : ℕ) + 1 by show (c : ℕ) = (c : ℕ) - 1 + 1; omega]
        push_cast
        ring
      linarith
  have hab' := Fin.le_def.mp hab
  exact key ((b : ℕ) - a) b hab (by omega)

theorem lowK_card_gt (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => a < b ∧ ε b = ε a).card
      = n - 1 - a := by
  have key : ∀ s : Finset (Fin n), (s.filter (fun b => ε b ≠ ε a)).card +
      (s.filter (fun b => ¬ (ε b ≠ ε a))).card = s.card := by
    intro s
    first
    | exact Finset.card_filter_add_card_filter_not _
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
    | rw [← Finset.card_disjoint_union (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
  rw [← Fin.card_Ioi a, ← key (Finset.Ioi a)]
  congr 1 <;> congr 1 <;> ext b <;> simp

theorem lowK_card_lt (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => b < a ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b = ε a).card
      = a := by
  have key : ∀ s : Finset (Fin n), (s.filter (fun b => ε b ≠ ε a)).card +
      (s.filter (fun b => ¬ (ε b ≠ ε a))).card = s.card := by
    intro s
    first
    | exact Finset.card_filter_add_card_filter_not _
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
    | rw [← Finset.card_disjoint_union (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
  rw [← Fin.card_Iio a, ← key (Finset.Iio a)]
  congr 1 <;> congr 1 <;> ext b <;> simp

theorem lowest_k_type_formula (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK ε lam a = lam a + ((n : ℝ) - 1) / 2 - (a : ℕ)
      - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ)
      + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := by
  have hg := lowK_card_gt ε a
  have hl := lowK_card_lt ε a
  have ha := a.isLt
  simp only [lowK, rhoN, rhoC, Pi.add_apply, Pi.sub_apply]
  set A1 := (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
  set A2 := (univ.filter fun b => a < b ∧ ε b = ε a).card
  set A3 := (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
  set A4 := (univ.filter fun b => b < a ∧ ε b = ε a).card
  have e1 : ((A1 : ℕ) : ℝ) + A2 + 1 + (a : ℕ) = n := by
    exact_mod_cast (show A1 + A2 + 1 + (a : ℕ) = n by omega)
  have e2 : ((A3 : ℕ) : ℝ) + A4 = (a : ℕ) := by exact_mod_cast hl
  linarith

theorem lowK_int_dom (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsHCParam lam) :
    (∀ a, ∃ m : ℤ, lowK ε lam a = m) ∧ ∀ a b, a < b → ε a = ε b → lowK ε lam b ≤ lowK ε lam a := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · obtain ⟨m, hm⟩ := hlam.2 a
    refine ⟨m + (n : ℤ) - 1 - ((a : ℕ) : ℤ) - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ)
      + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
    rw [lowest_k_type_formula]
    push_cast
    linarith
  · have hs : ε b = ε a := he.symm
    have hab' : (a : ℕ) ≤ b := le_of_lt (Fin.lt_def.mp hab)

    have c1 : (univ.filter fun c => a < c ∧ ε c = ε a).card ≤
        (univ.filter fun c => b < c ∧ ε c = ε b).card + ((b : ℕ) - a) := by
      calc _ ≤ ((univ.filter fun c => b < c ∧ ε c = ε b) ∪ Finset.Ioc a b).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
              Finset.mem_Ioc] at hc ⊢
            rw [hs]
            by_cases hcb : b < c
            · exact Or.inl ⟨hcb, hc.2⟩
            · exact Or.inr ⟨hc.1, not_lt.mp hcb⟩
        _ ≤ _ := by
            rw [← Fin.card_Ioc]
            exact Finset.card_union_le _ _
    have c2 : (univ.filter fun c => c < b ∧ ε c = ε b).card ≤
        (univ.filter fun c => c < a ∧ ε c = ε a).card + ((b : ℕ) - a) := by
      calc _ ≤ ((univ.filter fun c => c < a ∧ ε c = ε a) ∪ Finset.Ico a b).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
              Finset.mem_Ico] at hc ⊢
            rw [← hs]
            by_cases hca : c < a
            · exact Or.inl ⟨hca, hc.2⟩
            · exact Or.inr ⟨not_lt.mp hca, hc.1⟩
        _ ≤ _ := by
            rw [← Fin.card_Ico]
            exact Finset.card_union_le _ _
    have gap := hc_param_gap_ge_index lam hlam a b hab.le
    have c1r : (((univ.filter fun c => a < c ∧ ε c = ε a).card : ℕ) : ℝ) ≤
        ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℕ) + (((b : ℕ) : ℝ) - (a : ℕ)) := by
      have := c1
      rw [← Nat.cast_le (α := ℝ)] at this
      push_cast [Nat.cast_sub hab'] at this
      linarith
    have hcard₃ : (((univ.filter fun c => c < b ∧ ε c = ε b).card : ℕ) : ℝ) ≤
        ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℕ) + (((b : ℕ) : ℝ) - (a : ℕ)) := by
      have := c2
      rw [← Nat.cast_le (α := ℝ)] at this
      push_cast [Nat.cast_sub hab'] at this
      linarith
    rw [lowest_k_type_formula, lowest_k_type_formula]
    linarith

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma twist_det_star_mul {ε : Fin n → Bool} (k : KG ε) : star (toMK k).det * (toMK k).det = 1 := by
  obtain ⟨hu, -⟩ := k.2
  calc star (toMK k).det * (toMK k).det = (star (toMK k)).det * (toMK k).det := by
        rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
    _ = (star (toMK k) * toMK k).det := (Matrix.det_mul _ _).symm
    _ = 1 := by
        rw [show star (toMK k) * toMK k = 1 from Unitary.star_mul_self_of_mem hu, Matrix.det_one]

lemma twist_det_ne {ε : Fin n → Bool} (k : KG ε) : (toMK k).det ≠ 0 := by
  intro h
  have h1 := twist_det_star_mul k
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

lemma twist_toMK_inj {ε : Fin n → Bool} {k k' : KG ε} (h : toMK k = toMK k') : k = k' :=
  Subtype.ext (Subtype.ext (Units.ext h))

private theorem hasDerivAt_exp_smul_apply_zero (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : ∀ t : ℝ, ((t : ℂ) • X) = t • X := fun t => Complex.coe_smul t X
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h1
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [hc]
  exact h2

lemma twist_hasDerivAt_det_exp (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det) X.trace 0 := by
  refine InhabA.hasDerivAt_det_of_one (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X ?_
    (fun i j => hasDerivAt_exp_smul_apply_zero X i j)
  simp

lemma twist_smul_mem_unitary {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] {s : ℂ}
    (hs : star s * s = 1) {A : V →L[ℂ] V} (hA : A ∈ unitary (V →L[ℂ] V)) :
    s • A ∈ unitary (V →L[ℂ] V) := by
  exact Unitary.smul_mem_of_mem (Unitary.mem_iff.2 ⟨hs, by rw [mul_comm]; exact hs⟩) hA

lemma twist_zpow_star {ε : Fin n → Bool} (k : KG ε) (c : ℤ) :
    star ((toMK k).det ^ c) * (toMK k).det ^ c = 1 := by
  rw [star_zpow₀, ← _root_.mul_zpow, twist_det_star_mul, _root_.one_zpow]

theorem kType_twist {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) :
    Nonempty (KType ε (fun a => Λ a + (c : ℝ))) := by
  letI := T.instNACG
  letI := T.instIPS
  letI := T.instFD
  letI := T.instCS
  let d : KG ε → ℂ := fun k => (toMK k).det ^ c
  have hd : ∀ k, star (d k) * d k = 1 := fun k => twist_zpow_star k c
  have hdne : ∀ k, d k ≠ 0 := fun k => zpow_ne_zero c (twist_det_ne k)
  have hdmul : ∀ k k', d (k * k') = d k * d k' := by
    intro k k'
    show (toMK (k * k')).det ^ c = (toMK k).det ^ c * (toMK k').det ^ c
    rw [show toMK (k * k') = toMK k * toMK k' from rfl, Matrix.det_mul, _root_.mul_zpow]
  have hd1 : d 1 = 1 := by
    show (toMK (1 : KG ε)).det ^ c = 1
    rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.det_one, _root_.one_zpow]
  let τ' : KG ε →* unitary (T.V →L[ℂ] T.V) :=
    { toFun := fun k => ⟨d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V),
        twist_smul_mem_unitary (hd k) (T.τ k).2⟩
      map_one' := by
        apply Subtype.ext
        show d 1 • ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
        rw [hd1, one_smul, map_one, OneMemClass.coe_one]
      map_mul' := fun k k' => by
        apply Subtype.ext
        show d (k * k') • ((T.τ (k * k') : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) =
          (d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) *
            (d k' • ((T.τ k' : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
        rw [hdmul, map_mul, Submonoid.coe_mul, smul_mul_smul_comm] }
  have hcontd : Continuous d := by
    have h1 : Continuous fun k : KG ε => (toMK k).det :=
      Continuous.matrix_det (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))
    exact h1.zpow₀ c (fun k => Or.inl (twist_det_ne k))
  let dτ' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (T.V →L[ℂ] T.V) :=
    T.dτ + (c : ℂ) • (Matrix.traceLinearMap (Fin n) ℂ ℂ).smulRight (1 : T.V →L[ℂ] T.V)
  have hdτ : ∀ X, dτ' X = T.dτ X + ((c : ℂ) * X.trace) • (1 : T.V →L[ℂ] T.V) := by
    intro X
    simp only [dτ', LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Matrix.traceLinearMap_apply, smul_smul]
  refine ⟨⟨T.V, τ', ?_, ?_, dτ', ?_, T.w, T.w_norm, ?_, ?_⟩⟩
  · show Continuous (fun k => (⟨d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V),
        twist_smul_mem_unitary (hd k) (T.τ k).2⟩ : unitary (T.V →L[ℂ] T.V)))
    exact Continuous.subtype_mk (hcontd.smul (continuous_subtype_val.comp T.cont)) _
  · intro W hW
    refine T.irred W (fun k v hv => ?_)
    have h : (d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) v ∈ W := hW k v hv
    have e : ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v =
        (d k)⁻¹ • ((d k • ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) v) := by
      rw [ContinuousLinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (hdne k), one_smul]
    rw [e]
    exact W.smul_mem _ h
  · intro X hX γ hγ
    have hg := T.hasDeriv X hX γ hγ
    have hγ0 : γ 0 = 1 := by
      apply twist_toMK_inj
      rw [hγ 0, show (((0 : ℝ) : ℂ) • X) = 0 by simp, NormedSpace.exp_zero]
      rfl
    have hf0 : HasDerivAt (fun t : ℝ => (toMK (γ t)).det) X.trace 0 := by
      refine (twist_hasDerivAt_det_exp X).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => ?_))
      simp only [hγ t]
    have hdet0 : (toMK (γ 0)).det = 1 := by
      rw [hγ0]
      exact Matrix.det_one
    have hf : HasDerivAt (fun t : ℝ => d (γ t)) ((c : ℂ) * X.trace) 0 := by
      have hz := hasDerivAt_zpow c ((toMK (γ 0)).det) (Or.inl (twist_det_ne _))
      have hc := hz.comp (0 : ℝ) hf0
      rw [hdet0, _root_.one_zpow, mul_one] at hc
      exact hc
    have hτ0 : ((T.τ (γ 0) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1 := by
      rw [hγ0, map_one, OneMemClass.coe_one]
    have hd0 : d (γ 0) = 1 := by
      show (toMK (γ 0)).det ^ c = 1
      rw [hdet0, _root_.one_zpow]
    have hsm := hf.smul hg
    simp only [hτ0, hd0, one_smul] at hsm
    rw [← hdτ] at hsm
    exact hsm
  · intro a
    rw [hdτ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      T.w_wt a, Matrix.trace_single_eq_same, mul_one]
    push_cast
    rw [add_smul]
  · intro a b hab he
    rw [hdτ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      T.w_hw a b hab he, Matrix.trace_single_eq_of_ne _ _ _ hab.ne, mul_zero, zero_smul, add_zero]

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem kType_exists_of_dom (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : ∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) : Nonempty (KType ε Λ) := by
  choose m hm using hint
  set C : ℤ := ∑ a, |m a| with hC
  have hle : ∀ a, -C ≤ m a := by
    intro a
    have h1 : |m a| ≤ C :=
      Finset.single_le_sum (f := fun a => |m a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    have h2 := neg_abs_le (m a)
    linarith
  have hm' : NonnegDom ε (fun a => m a + C) := by
    refine ⟨fun a b hab he => ?_, fun a => by linarith [hle a]⟩
    have h1 := hdom a b hab he
    rw [hm a, hm b] at h1
    have h2 : m b ≤ m a := by exact_mod_cast h1
    show m b + C ≤ m a + C
    linarith
  obtain ⟨T⟩ := model_exists ε hm'
  obtain ⟨T'⟩ := kType_twist T (-C)
  have e : (fun a => (((m a + C : ℤ)) : ℝ) + ((-C : ℤ) : ℝ)) = Λ := by
    funext a
    rw [hm a]
    push_cast
    ring
  rw [← e]
  exact ⟨T'⟩

theorem kType_exists (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsHCParam lam) :
    Nonempty (KType ε (lowK ε lam)) := kType_exists_of_dom ε _ (lowK_int_dom ε lam hlam).1 (lowK_int_dom ε lam hlam).2

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
