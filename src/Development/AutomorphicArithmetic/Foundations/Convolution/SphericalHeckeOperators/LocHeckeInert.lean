import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SandId
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SatAvg
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ElemMatch
import GroundTheory.LocalFields.UnramifiedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

section SlopeTestRemainingChoices

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem cv_assoc {a b c : G → ℂ} (ha : a ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hb : b ∈ locallyConstantCompactSupport G ℂ ℂ) (hc : c ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ (groupConv μ a b) c = groupConv μ a (groupConv μ b c) :=
  congrArg (fun x : HeckeAlgebra μ => (x : G → ℂ))
    (mul_assoc (HeckeAlgebra.mk μ a ha) (HeckeAlgebra.mk μ b hb) (HeckeAlgebra.mk μ c hc))

private theorem cv_smul_left (c : ℂ) (a b : G → ℂ) : groupConv μ (c • a) b = c • groupConv μ a b := by
  funext x
  simp only [groupConv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

private theorem cv_smul_right (c : ℂ) (a b : G → ℂ) : groupConv μ a (c • b) = c • groupConv μ a b := by
  funext x
  simp only [groupConv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

private theorem cv_sum_right {ι : Type*} (S : Finset ι) {a : G → ℂ} {b : ι → G → ℂ}
    (ha : a ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hb : ∀ i ∈ S, b i ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ a (∑ i ∈ S, b i) = ∑ i ∈ S, groupConv μ a (b i) := by
  funext x
  simp only [groupConv, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum _ fun i hi => integrable_mul_of_mem ha
    ((hb i hi).1.continuous.comp (continuous_inv.mul continuous_const))

private theorem cv_sum_left {ι : Type*} (S : Finset ι) {a : G → ℂ} {b : ι → G → ℂ}
    (ha : a ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hb : ∀ i ∈ S, b i ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ (∑ i ∈ S, b i) a = ∑ i ∈ S, groupConv μ (b i) a := by
  funext x
  simp only [groupConv, Finset.sum_apply, Finset.sum_mul]
  exact integral_finsetSum _ fun i hi => integrable_mul_of_mem (hb i hi)
    (ha.1.continuous.comp (continuous_inv.mul continuous_const))

end SlopeTestRemainingChoices

section Aux2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem oneK_mem : oneK F n ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  indicator_mem_locallyConstantCompactSupport (isCompact_integralGL F n) (isOpen_integralGL F n) 1

variable [MeasurableSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F))

private theorem thP_monomial (a : Fin n → ℤ) : thP μ (monomial a) = th μ a := by
  unfold thP
  rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul]

private theorem dom_monomial {a : Fin n → ℤ} (ha : Antitone a) : Dom (monomial a) := by
  intro b hb
  rw [AddMonoidAlgebra.coeff_single] at hb
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]
  exact ha

end Aux2

section Aux3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F))

private theorem theta_sum₂ {ι : Type*} (S : Finset ι) (c : ι → ℂ) (y : ι → LaurentRing n) :
    thP μ (∑ i ∈ S, c i • y i) = ∑ i ∈ S, c i • thP μ (y i) := by
  have h : ∀ r : LaurentRing n, thP μ r = Finsupp.linearCombination ℂ (th μ) r.coeff := fun r => rfl
  simp only [h, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_smul, map_sum, map_smul]

variable [BorelSpace (GL (Fin n) F)] [μ.IsHaarMeasure]

private theorem oneK_eq (hK : μ (integralGL F n : Set (GL (Fin n) F)) = 1) :
    oneK F n = (HeckeAlgebra.idem μ (isCompact_integralGL F n) (isOpen_integralGL F n) : HeckeAlgebra μ) := by
  funext x
  rw [HeckeAlgebra.idem_apply, Measure.real, hK]
  simp [oneK, Set.indicator]

private theorem oneK_mul (hK : μ (integralGL F n : Set (GL (Fin n) F)) = 1) :
    groupConv μ (oneK F n) (oneK F n) = oneK F n := by
  rw [oneK_eq μ hK]
  exact congrArg (fun x : HeckeAlgebra μ => (x : GL (Fin n) F → ℂ))
    (HeckeAlgebra.isIdempotentElem_idem (μ := μ) (isCompact_integralGL F n) (isOpen_integralGL F n)).eq

end Aux3

theorem UpperTheory.ConvolutionTheory.H.core :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure], μ (integralGL F n : Set (GL (Fin n) F)) = 1 →
      ∃ ν : Fin n → ℤ, ∀ r : LaurentRing n, Dom r → ∀ h : SphericalHecke μ (F := F) (n := n),
        satakeTransform μ h = symSum (monomial ν * dPol n ((qF F : ℂ))⁻¹ * r) →
        (thP μ (monomial ν * dPol n ((qF F : ℂ))⁻¹ * r) - fun x => (h : HeckeAlgebra μ) x) ∈ comm μ := by
  intro F _ _ _ _ n _ _ μ _ hK
  set t : ℂ := ((qF F : ℂ))⁻¹
  obtain ⟨ν₁, ν₂, h₁, h₂, hid⟩ := sandId F n μ hK
  refine ⟨ν₁ + ν₂, fun r hr h hh => ?_⟩
  have hν₁ : Antitone ν₁ := fun i j hij => by
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · have := h₁ i j hij
      omega
  have g₁ := gapDom n ν₁ h₁
  have g₂ := gapDom n ν₂ h₂
  have g₃ := gapDom n _ (g₂.2.2 ν₁ hν₁)
  have hth : ∀ a : Fin n → ℤ, Antitone a → th μ a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
    fun a ha => by
      have := thPMul F n μ _ _ (dom_monomial ha) (dom_monomial ha)
      rw [thP_monomial] at this
      exact this.2.1
  have hr' := (thPMul F n μ _ _ hr hr).2.1
  have hv : ∑ S ∈ (pairs n).powerset, sgS S • monomial (eL S + eR S) = dPol n 1 :=
    eq_of_forall_evalAt fun z => by
      have := vandSum n z 1 1
      simp only [Equiv.Perm.coe_one, Function.comp_id, if_true] at this
      rw [← this, map_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [map_smul, evalAt_single, one_mul, monomialChar_add, smul_eq_mul]
  have hD1 : Dom (monomial (ν₁ + ν₂) * r * dPol n 1) := by
    rw [mul_right_comm]
    exact (thPMul F n μ _ _ (g₃.2.1 1) hr).1
  have hsat := satAvg F n μ hK (monomial (ν₁ + ν₂) * r) hD1 h (by rw [hh, mul_right_comm])
  let C : Finset (Fin n × Fin n) → LaurentRing n := fun S => monomial (ν₂ + eR S) * (r * monomial (ν₁ + eL S))
  have hA : ∀ S ∈ (pairs n).powerset, Dom (r * monomial (ν₁ + eL S)) := fun S hS =>
    (thPMul F n μ _ _ hr (dom_monomial (g₁.1 S hS).1)).1
  have hC : ∀ S ∈ (pairs n).powerset, thP μ (C S) ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := fun S hS =>
    have := (thPMul F n μ _ _ (dom_monomial (g₂.1 S hS).2) (hA S hS)).1
    (thPMul F n μ _ _ this this).2.1
  have hCs : monomial (ν₁ + ν₂) * r * dPol n 1 = ∑ S ∈ (pairs n).powerset, sgS S • C S := by
    rw [← hv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [C, monomial_add, mul_smul_comm]
    congr 1
    ring
  have e1 : thP μ (monomial (ν₁ + ν₂) * dPol n t * r) = vPoly n t • ∑ S ∈ (pairs n).powerset,
      sgS S • groupConv μ (groupConv μ (thP μ (r * monomial (ν₁ + eL S))) (oneK F n)) (th μ (ν₂ + eR S)) := by
    rw [mul_comm _ r, ← (thPMul F n μ _ _ hr (g₃.2.1 t)).2.2.2, ← hid, cv_smul_right]
    congr 1
    unfold sand
    rw [cv_sum_right μ _ hr' fun S hS => Submodule.smul_mem _ _ (groupConv_mem μ (hth _ (g₁.1 S hS).1)
      (groupConv_mem μ oneK_mem (hth _ (g₂.1 S hS).2)))]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [cv_smul_right, ← cv_assoc μ hr' (hth _ (g₁.1 S hS).1) (groupConv_mem μ oneK_mem (hth _ (g₂.1 S hS).2)),
      ← (thPMul F n μ _ _ hr (dom_monomial (g₁.1 S hS).1)).2.2.2, thP_monomial,
      cv_assoc μ (groupConv_mem μ hr' (hth _ (g₁.1 S hS).1)) oneK_mem (hth _ (g₂.1 S hS).2)]
  rw [e1, ← hsat, hCs, theta_sum₂, cv_sum_left μ _ oneK_mem fun S hS => Submodule.smul_mem _ _ (hC S hS),
    cv_sum_right μ _ oneK_mem fun S hS => groupConv_mem μ (Submodule.smul_mem _ _ (hC S hS)) oneK_mem,
    ← smul_sub, ← Finset.sum_sub_distrib]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun S hS => ?_)
  rw [cv_smul_left, cv_smul_right, ← smul_sub]
  refine Submodule.smul_mem _ _ ?_
  have hAm := (thPMul F n μ _ _ (hA S hS) (hA S hS)).2.1
  have hAK := groupConv_mem μ hAm (oneK_mem (F := F) (n := n))
  have hCK := groupConv_mem μ (hC S hS) (oneK_mem (F := F) (n := n))
  have m1 : groupConv μ (th μ (ν₂ + eR S)) (groupConv μ (thP μ (r * monomial (ν₁ + eL S))) (oneK F n)) -
      groupConv μ (groupConv μ (thP μ (r * monomial (ν₁ + eL S))) (oneK F n)) (th μ (ν₂ + eR S)) ∈ comm μ := by
    rw [th, cv_smul_left, cv_smul_right, ← smul_sub]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, Or.inr ⟨_, (g₂.1 S hS).2, rfl⟩, hAK, rfl⟩)
  have m2 : groupConv μ (oneK F n) (groupConv μ (thP μ (C S)) (oneK F n)) -
      groupConv μ (groupConv μ (thP μ (C S)) (oneK F n)) (oneK F n) ∈ comm μ :=
    Submodule.subset_span ⟨_, _, Or.inl rfl, hCK, rfl⟩
  rw [cv_assoc μ (hC S hS) oneK_mem oneK_mem, oneK_mul μ hK] at m2
  rw [← cv_assoc μ (hth _ (g₂.1 S hS).2) hAm oneK_mem, ← thP_monomial μ (ν₂ + eR S),
    (thPMul F n μ _ _ (dom_monomial (g₂.1 S hS).2) (hA S hS)).2.2.2, thP_monomial] at m1
  have := Submodule.neg_mem _ (Submodule.add_mem _ m1 m2)
  convert this using 1
  simp only [C]
  abel
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

namespace UpperTheory.ConvolutionTheory.H.NonVanishingCharacter

variable {n : ℕ}

private def phi : (Fin n → ℕ) →+ (Fin n → ℤ) where
  toFun b i := ∑ k, if i ≤ k then (b k : ℤ) else 0
  map_zero' := by
    funext i
    simp
  map_add' b c := by
    funext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp

private lemma phi_apply (b : Fin n → ℕ) (i : Fin n) :
    phi b i = ∑ k, if i ≤ k then (b k : ℤ) else 0 := rfl

private lemma phi_nonneg (b : Fin n → ℕ) (i : Fin n) : 0 ≤ phi b i := by
  rw [phi_apply]
  refine Finset.sum_nonneg fun k _ => ?_
  split_ifs <;> simp

private lemma phi_anti (b : Fin n → ℕ) {i j : Fin n} (hij : i ≤ j) : phi b j ≤ phi b i := by
  rw [phi_apply, phi_apply]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h1 : j ≤ k
  · rw [if_pos h1, if_pos (hij.trans h1)]
  · rw [if_neg h1]
    split_ifs <;> simp

private def chi (w : Fin n → ℂˣ) : Multiplicative (Fin n → ℕ) →* ℂ where
  toFun b := monomialChar (phi (Multiplicative.toAdd b)) w
  map_one' := by simp
  map_mul' b c := by simp [map_add, monomialChar_add]

private lemma chi_apply (w : Fin n → ℂˣ) (b : Fin n → ℕ) :
    chi w (Multiplicative.ofAdd b) = monomialChar (phi b) w := rfl

private lemma chi_single (w : Fin n → ℂˣ) (k : Fin n) :
    chi w (Multiplicative.ofAdd (Pi.single k 1)) = ∏ i ∈ Finset.Iic k, (w i : ℂ) := by
  have hphi : ∀ i, phi (Pi.single k 1 : Fin n → ℕ) i = if i ≤ k then 1 else 0 := by
    intro i
    rw [phi_apply, Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [Pi.single_eq_of_ne hl]
    · simp
  rw [chi_apply, monomialChar_apply]
  have hI : Finset.Iic k = Finset.univ.filter (· ≤ k) := by
    ext
    simp
  rw [hI, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hphi]
  split_ifs <;> simp

private lemma chi_injective {w w' : Fin n → ℂˣ} (h : chi w = chi w') : w = w' := by
  have hp : ∀ k, ∏ i ∈ Finset.Iic k, (w i : ℂ) = ∏ i ∈ Finset.Iic k, (w' i : ℂ) := fun k => by
    rw [← chi_single, ← chi_single, h]
  funext k
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    have hI : Finset.Iic k = insert k (Finset.Iio k) := by
      ext
      simp [le_iff_eq_or_lt]
    have h1 := hp k
    rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp)] at h1
    have e : ∏ i ∈ Finset.Iio k, (w i : ℂ) = ∏ i ∈ Finset.Iio k, (w' i : ℂ) :=
      Finset.prod_congr rfl fun i hi => by rw [ih i (Finset.mem_Iio.1 hi)]
    rw [e] at h1
    have ne : ∏ i ∈ Finset.Iio k, (w' i : ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => (w' i).ne_zero
    exact Units.ext (mul_right_cancel₀ ne h1)

private lemma evalAt_varL (w : Fin n → ℂˣ) (i : Fin n) : evalAt w (varL i) = (w i : ℂ) := by
  rw [evalAt_single, one_mul, monomialChar_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private lemma evalAt_dPol (w : Fin n → ℂˣ) (t : ℂ) :
    evalAt w (dPol n t) = ∏ p ∈ pairs n, ((w p.1 : ℂ) - t * (w p.2 : ℂ)) := by
  rw [dPol, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, map_smul, evalAt_varL, evalAt_varL, smul_eq_mul]

private lemma evalAt_dPol_ne {t : ℂ} (ht : ‖t‖ < 1) (w : Fin n → ℂˣ)
    (hw : ∀ i j, i ≤ j → ‖(w j : ℂ)‖ ≤ ‖(w i : ℂ)‖) : evalAt w (dPol n t) ≠ 0 := by
  rw [evalAt_dPol, Finset.prod_ne_zero_iff]
  intro p hp h0
  have hij : p.1 < p.2 := (Finset.mem_filter.1 hp).2
  have e : (w p.1 : ℂ) = t * (w p.2 : ℂ) := sub_eq_zero.1 h0
  have h1 := hw _ _ hij.le
  have hpos : 0 < ‖(w p.2 : ℂ)‖ := norm_pos_iff.2 (w p.2).ne_zero
  rw [e, norm_mul] at h1
  nlinarith

private lemma evalAt_term (z : Fin n → ℂˣ) (a : Fin n → ℤ) (t : ℂ) :
    evalAt z (symSum (monomial a * dPol n t)) =
      ∑ σ : Equiv.Perm (Fin n), monomialChar a (z ∘ σ) * evalAt (z ∘ σ) (dPol n t) := by
  rw [symSum, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [evalAt_permAct, map_mul, evalAt_single, one_mul]

end UpperTheory.ConvolutionTheory.H.NonVanishingCharacter

open UpperTheory.ConvolutionTheory.H.NonVanishingCharacter in
theorem UpperTheory.ConvolutionTheory.H.nonVan :
    ∀ (n : ℕ) (t : ℂ), ‖t‖ < 1 → ∀ (z : Fin n → ℂˣ) (m : ℕ),
      ∃ a : Fin n → ℤ, Gap m a ∧ (∀ i, 0 ≤ a i) ∧ evalAt z (symSum (monomial a * dPol n t)) ≠ 0 := by
  classical
  intro n t ht z m
  by_contra hcon
  push_neg at hcon
  let s : Fin n → ℤ := fun i => (m : ℤ) * ((n : ℤ) - ((i : ℕ) : ℤ))
  have hs0 : ∀ i, 0 ≤ s i := fun i => by
    have : ((i : ℕ) : ℤ) ≤ n := by exact_mod_cast i.2.le
    exact mul_nonneg (by positivity) (by linarith)
  have hsgap : ∀ i j : Fin n, i < j → s j + m ≤ s i := fun i j hij => by
    have h1 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
    have hm : (0 : ℤ) ≤ m := by positivity
    simp only [s]
    nlinarith
  let W : Equiv.Perm (Fin n) → ℂ := fun σ => monomialChar s (z ∘ σ) * evalAt (z ∘ σ) (dPol n t)
  let Ψ : Equiv.Perm (Fin n) → (Multiplicative (Fin n → ℕ) →* ℂ) := fun σ => chi (z ∘ σ)
  have hsum : ∀ b, ∑ σ, W σ * Ψ σ b = 0 := by
    intro b
    have h0 := hcon (s + phi (Multiplicative.toAdd b))
      (fun i j hij => by
        have := hsgap i j hij
        have := phi_anti (Multiplicative.toAdd b) hij.le
        simp only [Pi.add_apply]
        linarith)
      (fun i => add_nonneg (hs0 i) (phi_nonneg _ i))
    rw [evalAt_term] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [monomialChar_add]
    simp only [W, Ψ]
    change _ * monomialChar (phi (Multiplicative.toAdd b)) (z ∘ σ) = _
    ring
  have hli := linearIndependent_monoidHom (Multiplicative (Fin n → ℕ)) ℂ
  rw [linearIndependent_iff'] at hli
  let g : (Multiplicative (Fin n → ℕ) →* ℂ) → ℂ := fun χ => ∑ σ with Ψ σ = χ, W σ
  have hg : ∑ χ ∈ Finset.univ.image Ψ, g χ • (χ : Multiplicative (Fin n → ℕ) → ℂ) = 0 := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, Finset.sum_mul]
    rw [← hsum b]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Ψ) (t := Finset.univ.image Ψ)
      (fun σ _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))]
    exact Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun σ hσ => by
      rw [(Finset.mem_filter.1 hσ).2]
  let σ₀ : Equiv.Perm (Fin n) := Tuple.sort (fun i => -‖(z i : ℂ)‖)
  have hw : ∀ i j, i ≤ j → ‖((z ∘ σ₀) j : ℂ)‖ ≤ ‖((z ∘ σ₀) i : ℂ)‖ := fun i j hij =>
    neg_le_neg_iff.1 (Tuple.monotone_sort (fun i => -‖(z i : ℂ)‖) hij)
  have hW : W σ₀ ≠ 0 := by
    refine mul_ne_zero ?_ (evalAt_dPol_ne ht _ hw)
    rw [monomialChar_apply, Finset.prod_ne_zero_iff]
    exact fun i _ => Units.ne_zero _
  have hgz : g (Ψ σ₀) = 0 := hli _ g hg (Ψ σ₀) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hfib : g (Ψ σ₀) = ((Finset.univ.filter fun σ => Ψ σ = Ψ σ₀).card : ℂ) * W σ₀ := by
    simp only [g]
    rw [Finset.sum_congr rfl (g := fun _ => W σ₀), Finset.sum_const, nsmul_eq_mul]
    intro σ hσ
    have he : z ∘ σ = z ∘ σ₀ := chi_injective (Finset.mem_filter.1 hσ).2
    simp only [W, he]
  have hc : (Finset.univ.filter fun σ => Ψ σ = Ψ σ₀).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ σ₀, rfl⟩)
  rw [hfib] at hgz
  exact (mul_ne_zero (Nat.cast_ne_zero.2 hc) hW) hgz
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem UpperTheory.ConvolutionTheory.H.mem_supp_mono {n : ℕ} {a c : Fin n → ℤ} {q : LaurentRing n}
    (h : c ∈ (monomial a * q).coeff.support) : -a + c ∈ q.coeff.support := by
  rw [Finsupp.mem_support_iff] at h ⊢
  have e : (monomial a * q).coeff c = 1 * q.coeff (-a + c) :=
    AddMonoidAlgebra.coeff_single_mul_apply q 1 a c
  rw [e, one_mul] at h
  exact h

private theorem UpperTheory.ConvolutionTheory.H.gap_strict {n : ℕ} (B : Finset (Fin n → ℤ)) :
    ∃ m : ℕ, ∀ a : Fin n → ℤ, Gap m a → ∀ b ∈ B, StrictAnti (a + b) := by
  classical
  set M : ℕ := ∑ b ∈ B, ∑ i, (b i).natAbs with hM
  have hb : ∀ b ∈ B, ∀ i, (b i).natAbs ≤ M := fun b hb i =>
    (Finset.single_le_sum (f := fun i => (b i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun b : Fin n → ℤ => ∑ i, (b i).natAbs)
        (fun _ _ => Nat.zero_le _) hb)
  refine ⟨2 * M + 1, fun a ha b hbB i j hij => ?_⟩
  have h1 := ha i j hij
  have h2 := hb b hbB i
  have h3 := hb b hbB j
  simp only [Pi.add_apply]
  push_cast at h1
  omega

private theorem UpperTheory.ConvolutionTheory.H.Gap.mono {n : ℕ} {m m' : ℕ} (h : m ≤ m') {a : Fin n → ℤ}
    (ha : Gap m' a) : Gap m a := fun i j hij => by
  have := ha i j hij
  have h' : (m : ℤ) ≤ m' := by exact_mod_cast h
  omega

private theorem UpperTheory.ConvolutionTheory.H.Gap.scale {n : ℕ} {m l : ℕ} (hl : 1 ≤ l) {a : Fin n → ℤ}
    (ha : Gap m a) : Gap m ((l : ℤ) • a) := fun i j hij => by
  have h := ha i j hij
  have h' : (1 : ℤ) ≤ l := by exact_mod_cast hl
  have hm : (0 : ℤ) ≤ m := by positivity
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith

private theorem UpperTheory.ConvolutionTheory.H.bc_monomial {n : ℕ} (l : ℕ) (a : Fin n → ℤ) :
    bc l (monomial a) = monomial ((l : ℤ) • a) := by
  simp only [bc, AddMonoidAlgebra.mapDomainAlgHom_apply, monomial, AddMonoidAlgebra.mapDomain_single]
  rfl

private theorem UpperTheory.ConvolutionTheory.H.monomial_pow {n : ℕ} (l : ℕ) (a : Fin n → ℤ) :
    monomial ((l : ℤ) • a) = monomial a ^ l := by
  induction l with
  | zero => simp [monomial, AddMonoidAlgebra.one_def]
  | succ k ih =>
    rw [pow_succ, ← ih, ← monomial_add]
    congr 1
    push_cast
    rw [add_smul, one_smul]

private noncomputable def UpperTheory.ConvolutionTheory.H.cof (n l : ℕ) (t : ℂ) : LaurentRing n :=
  ∏ p ∈ pairs n, ∑ k ∈ Finset.range l, varL p.1 ^ k * (t • varL p.2) ^ (l - 1 - k)

private theorem UpperTheory.ConvolutionTheory.H.bc_dPol (n l : ℕ) (t : ℂ) :
    bc l (dPol n (t ^ l)) = dPol n t * cof n l t := by
  simp only [dPol, cof, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, map_smul, mul_comm, geom_sum₂_mul, smul_pow]
  simp only [varL, bc_monomial, monomial_pow]

theorem UpperTheory.ConvolutionTheory.H.depth :
    ∀ (n l : ℕ), 1 ≤ l → ∀ (t : ℂ) (P : Finset (LaurentRing n)) (ν ν' : Fin n → ℤ), ∃ m : ℕ, ∀ a : Fin n → ℤ, Gap m a → ∀ p ∈ P,
      SDom (monomial a * dPol n (t ^ l) * p) ∧
      (∃ r, Dom r ∧ monomial a * dPol n (t ^ l) * p = monomial ν * dPol n (t ^ l) * r) ∧
      ∃ r', Dom r' ∧ bc l (monomial a * dPol n (t ^ l) * p) = monomial ν' * dPol n t * r' := by
  classical
  intro n l hl t P ν ν'
  obtain ⟨m₁, h₁⟩ := gap_strict (P.biUnion fun p => (dPol n (t ^ l) * p).coeff.support)
  obtain ⟨m₂, h₂⟩ := gap_strict (P.biUnion fun p => p.coeff.support.image (· - ν))
  obtain ⟨m₃, h₃⟩ := gap_strict
    (P.biUnion fun p => (cof n l t * bc l p).coeff.support.image (· - ν'))
  refine ⟨m₁ + m₂ + m₃, fun a ha p hp => ⟨?_, ⟨monomial (a - ν) * p, ?_, ?_⟩,
    ⟨monomial ((l : ℤ) • a - ν') * (cof n l t * bc l p), ?_, ?_⟩⟩⟩
  · intro c hc
    rw [mul_assoc] at hc
    have hb := mem_supp_mono hc
    have := h₁ a (Gap.mono (by omega) ha) (-a + c)
      (Finset.mem_biUnion.2 ⟨p, hp, hb⟩)
    simpa using this
  · intro c hc
    have hb := mem_supp_mono hc
    have := h₂ a (Gap.mono (by omega) ha) (-(a - ν) + c - ν)
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)
    have e : a + (-(a - ν) + c - ν) = c := by abel
    rw [e] at this
    exact this.antitone
  · have e : monomial a = monomial ν * monomial (a - ν) := by
      rw [← monomial_add]; congr 1; abel
    rw [e]; ring
  · intro c hc
    have hb := mem_supp_mono hc
    have := h₃ ((l : ℤ) • a) (Gap.scale hl (Gap.mono (by omega) ha))
      (-((l : ℤ) • a - ν') + c - ν')
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)
    have e : (l : ℤ) • a + (-((l : ℤ) • a - ν') + c - ν') = c := by abel
    rw [e] at this
    exact this.antitone
  · have e : monomial ((l : ℤ) • a) = monomial ν' * monomial ((l : ℤ) • a - ν') := by
      rw [← monomial_add]; congr 1; abel
    rw [map_mul, map_mul, bc_monomial, bc_dPol, e]; ring
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

theorem UpperTheory.ConvolutionTheory.H.symAlg :
    ∀ (n l : ℕ) (y : LaurentRing n), symSum y ∈ symmetricLaurent n ∧ bc l (symSum y) = symSum (bc l y) ∧
      (∀ p ∈ symmetricLaurent n, symSum (y * p) = symSum y * p) ∧ (y ∈ symmetricLaurent n → bc l y ∈ symmetricLaurent n) ∧
      ∀ z : Fin n → ℂˣ, evalAt z (bc l y) = evalAt (z ^ l) y := by
  intro n l y
  have hb : ∀ (a : Fin n → ℤ) (c : ℂ), bc l (AddMonoidAlgebra.single a c : LaurentRing n) = AddMonoidAlgebra.single ((l : ℤ) • a) c := by
    intro a c
    simp [bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]
  have hc : ∀ (σ : Equiv.Perm (Fin n)) (y : LaurentRing n), bc l (permAct σ y) = permAct σ (bc l y) := fun σ y => by
    have : (bc l).comp (permAct σ) = (permAct σ).comp (bc (n := n) l) :=
      AddMonoidAlgebra.algHom_ext (fun a => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, permAct_single, hb, hb, permAct_single]; rfl) (Subsingleton.elim _ _)
    exact AlgHom.congr_fun this y
  refine ⟨fun τ => ?_, ?_, fun p hp => ?_, fun hy σ => ?_, fun z => ?_⟩
  · rw [symSum, map_sum]
    simp only [permAct_permAct]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl
  · rw [symSum, symSum, map_sum]
    exact Finset.sum_congr rfl fun σ _ => hc σ y
  · rw [symSum, symSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by rw [map_mul, hp σ]
  · rw [← hc, hy σ]
  · have : (evalAt z).comp (bc l) = evalAt (z ^ l) :=
      AddMonoidAlgebra.algHom_ext (fun a => by
        rw [AlgHom.comp_apply, hb, evalAt_single, evalAt_single, monomialChar_apply, monomialChar_apply]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, zpow_mul, zpow_natCast, Pi.pow_apply]) (Subsingleton.elim _ _)
    exact AlgHom.congr_fun this y
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem lin_zero {X : Type*} (L : Submodule ℂ (X → ℂ)) (Λ : (X → ℂ) → ℂ)
    (hlin : ∀ x ∈ L, ∀ y ∈ L, ∀ c : ℂ, Λ (c • x + y) = c * Λ x + Λ y) : Λ 0 = 0 := by
  have h := hlin 0 L.zero_mem 0 L.zero_mem 1
  simp only [smul_zero, add_zero, one_mul] at h
  simpa using h

private theorem lin_sum {X ι : Type*} (L : Submodule ℂ (X → ℂ)) (Λ : (X → ℂ) → ℂ)
    (hlin : ∀ x ∈ L, ∀ y ∈ L, ∀ c : ℂ, Λ (c • x + y) = c * Λ x + Λ y)
    (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ i ∈ s, f i ∈ L) :
    Λ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * Λ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lin_zero L Λ hlin
  | insert i s hi ih =>
    have hf' : ∀ j ∈ s, f j ∈ L := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hlin _ (hf i (Finset.mem_insert_self i s)) _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hf' j hj)),
      ih hf']

private theorem lin_eq_of_sub {X : Type*} (L C : Submodule ℂ (X → ℂ)) (Λ : (X → ℂ) → ℂ)
    (hlin : ∀ x ∈ L, ∀ y ∈ L, ∀ c : ℂ, Λ (c • x + y) = c * Λ x + Λ y)
    (hC : ∀ x ∈ C, Λ x = 0) {u v : X → ℂ} (hu : u ∈ L) (hv : v ∈ L) (huv : u - v ∈ C) : Λ u = Λ v := by
  have h := hlin (u - v) (L.sub_mem hu hv) v hv 1
  rw [one_smul, sub_add_cancel, hC _ huv, one_mul, zero_add] at h
  exact h

private theorem th_mem (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) {a : Fin n → ℤ} (ha : Antitone a) :
    th μ a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  Submodule.smul_mem _ _ (dcoShape F n a ha).2.2.1

private theorem dom_add {n : ℕ} {r s : LaurentRing n} (hr : Dom r) (hs : Dom s) : Dom (r + s) := by
  classical
  intro a ha
  rw [AddMonoidAlgebra.coeff_add] at ha
  rcases Finset.mem_union.1 (Finsupp.support_add ha) with h | h
  · exact hr a h
  · exact hs a h

private theorem dom_smul {n : ℕ} {r : LaurentRing n} (c : ℂ) (hr : Dom r) : Dom (c • r) := by
  classical
  intro a ha
  rw [AddMonoidAlgebra.coeff_smul] at ha
  exact hr a (Finsupp.support_smul ha)

private theorem sdom_add {n : ℕ} {r s : LaurentRing n} (hr : SDom r) (hs : SDom s) : SDom (r + s) := by
  classical
  intro a ha
  rw [AddMonoidAlgebra.coeff_add] at ha
  rcases Finset.mem_union.1 (Finsupp.support_add ha) with h | h
  · exact hr a h
  · exact hs a h

private theorem sdom_smul {n : ℕ} {r : LaurentRing n} (c : ℂ) (hr : SDom r) : SDom (c • r) := by
  classical
  intro a ha
  rw [AddMonoidAlgebra.coeff_smul] at ha
  exact hr a (Finsupp.support_smul ha)

private theorem clause_span {n l : ℕ} (Y M M' : LaurentRing n) (P : Finset (LaurentRing n))
    (h : ∀ p ∈ P, SDom (Y * p) ∧ (∃ r, Dom r ∧ Y * p = M * r) ∧ ∃ r', Dom r' ∧ bc l (Y * p) = M' * r')
    (p : LaurentRing n) (hp : p ∈ Submodule.span ℂ (P : Set (LaurentRing n))) :
    SDom (Y * p) ∧ (∃ r, Dom r ∧ Y * p = M * r) ∧ ∃ r', Dom r' ∧ bc l (Y * p) = M' * r' := by
  induction hp using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    refine ⟨?_, ⟨0, ?_, by simp⟩, 0, ?_, by simp⟩
    · intro a ha; simp at ha
    · intro a ha; simp at ha
    · intro a ha; simp at ha
  | add x y _ _ hx hy =>
    obtain ⟨h1, ⟨r, hr, e⟩, r', hr', e'⟩ := hx
    obtain ⟨g1, ⟨s, hs, f⟩, s', hs', f'⟩ := hy
    refine ⟨by rw [mul_add]; exact sdom_add h1 g1, ⟨r + s, dom_add hr hs, by rw [mul_add, mul_add, e, f]⟩,
      r' + s', dom_add hr' hs', by rw [mul_add, map_add, mul_add, e', f']⟩
  | smul c x _ hx =>
    obtain ⟨h1, ⟨r, hr, e⟩, r', hr', e'⟩ := hx
    refine ⟨by rw [mul_smul_comm]; exact sdom_smul c h1, ⟨c • r, dom_smul c hr, by rw [mul_smul_comm, mul_smul_comm, e]⟩,
      c • r', dom_smul c hr', by rw [mul_smul_comm, map_smul, mul_smul_comm, e']⟩

private theorem thP_bc {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) (l : ℕ) (y : LaurentRing n) :
    thP μ (bc l y) = ∑ a ∈ y.coeff.support, y.coeff a • th μ ((l : ℤ) • a) := by
  have hc : (bc l y).coeff = Finsupp.mapDomain (fun m : Fin n → ℤ => (l : ℤ) • m) y.coeff := rfl
  unfold thP
  rw [hc, Finsupp.sum_mapDomain_index (h := fun a c => c • th μ a) (fun a => zero_smul _ _) (fun a c d => add_smul _ _ _)]
  rfl

private theorem range_Y {n : ℕ} (t : ℂ) (a : Fin n → ℤ) (ha : ∀ i, 0 ≤ a i) :
    symSum (monomial a * dPol n t) ∈ (polyEmb n).range := by
  have h1 : (monomial a : LaurentRing n) ∈ (polyEmb n).range := by
    refine mem_range_polyEmb fun b hb i => ?_
    rw [AddMonoidAlgebra.coeff_single] at hb
    have : b = a := by simpa using Finsupp.support_single_subset hb
    rw [this]
    exact ha i
  have hv : ∀ i : Fin n, (varL i : LaurentRing n) ∈ (polyEmb n).range := fun i =>
    AlgHom.mem_range _ |>.2 ⟨MvPolynomial.X i, polyEmb_X i⟩
  have h2 : dPol n t ∈ (polyEmb n).range :=
    Subalgebra.prod_mem _ fun p _ => Subalgebra.sub_mem _ (hv _) (Subalgebra.smul_mem _ (hv _) _)
  obtain ⟨Q, hQ⟩ := AlgHom.mem_range _ |>.1 (Subalgebra.mul_mem _ h1 h2)
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [← hQ]
  exact AlgHom.mem_range _ |>.2 ⟨MvPolynomial.rename σ Q, polyEmb_rename σ Q⟩

theorem UpperTheory.ConvolutionTheory.H.deepAbs :
    ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n l : ℕ), 1 ≤ l → (qF E : ℂ) = (qF k : ℂ) ^ l →
      ∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) [μE.IsHaarMeasure] [μk.IsHaarMeasure],
      μE (integralGL E n : Set (GL (Fin n) E)) = 1 → μk (integralGL k n : Set (GL (Fin n) k)) = 1 →
      ∀ P : Finset (LaurentRing n), (∀ p ∈ P, p ∈ symmetricLaurent n) → ∀ z : Fin n → ℂˣ,
      ∃ g ∈ symmetricLaurent n, g ∈ (polyEmb n).range ∧ evalAt z g ≠ 0 ∧ ∀ p ∈ Submodule.span ℂ (P : Set (LaurentRing n)),
        ∀ (h : SphericalHecke μE (F := E) (n := n)) (f : SphericalHecke μk (F := k) (n := n)),
          satakeTransform μE h = g * p → satakeTransform μk f = bc l (g * p) →
          ∀ (ΛE : (GL (Fin n) E → ℂ) → ℂ) (Λk : (GL (Fin n) k → ℂ) → ℂ),
          (∀ x ∈ locallyConstantCompactSupport (GL (Fin n) E) ℂ ℂ, ∀ y ∈ locallyConstantCompactSupport (GL (Fin n) E) ℂ ℂ, ∀ c : ℂ,
          ΛE (c • x + y) = c * ΛE x + ΛE y) → (∀ x ∈ comm μE, ΛE x = 0) →
          (∀ x ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ y ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ c : ℂ,
          Λk (c • x + y) = c * Λk x + Λk y) → (∀ x ∈ comm μk, Λk x = 0) →
          (∀ a : Fin n → ℤ, StrictAnti a → ΛE (th μE a) = Λk (th μk ((l : ℤ) • a))) →
          ΛE (fun x => (h : HeckeAlgebra μE) x) = Λk fun x => (f : HeckeAlgebra μk) x := by
  intro k E _ _ _ _ _ _ _ _ n l hl hq _ _ _ _ μE μk _ _ hE hk P hP z
  classical
  obtain ⟨ν, hν⟩ := core E n μE hE
  obtain ⟨ν', hν'⟩ := core k n μk hk
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t = ((qF k : ℂ))⁻¹ := ⟨_, rfl⟩
  have hte : ((qF E : ℂ))⁻¹ = t ^ l := by rw [hq, ht, inv_pow]
  rw [hte] at hν
  rw [← ht] at hν'
  obtain ⟨m, hm⟩ := depth n l hl t P ν ν'
  have hnorm : ‖t ^ l‖ < 1 := by
    rw [← hte, norm_inv, Complex.norm_natCast]
    have h1 : 1 < qF E := Finite.one_lt_card
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast h1)
  obtain ⟨a, hgap, ha0, hne⟩ := nonVan n (t ^ l) hnorm z m
  refine ⟨symSum (monomial a * dPol n (t ^ l)), (symAlg n l _).1, range_Y _ a ha0, hne, ?_⟩
  intro p hp h f hSh hSf ΛE Λk hlE hzE hlk hzk hth
  obtain ⟨hSD, ⟨r, hr, hyr⟩, r', hr', hyr'⟩ := clause_span (l := l) (monomial a * dPol n (t ^ l)) (monomial ν * dPol n (t ^ l))
    (monomial ν' * dPol n t) P (fun p hp => hm a hgap p hp) p hp
  have hps : p ∈ symmetricLaurent n := by
    have : Submodule.span ℂ (P : Set (LaurentRing n)) ≤ Subalgebra.toSubmodule (symmetricLaurent n) :=
      Submodule.span_le.2 fun x hx => hP x hx
    exact this hp
  obtain ⟨-, hb, hmul, -, -⟩ := symAlg n l (monomial a * dPol n (t ^ l))
  have hSy : symSum (monomial a * dPol n (t ^ l) * p) = symSum (monomial a * dPol n (t ^ l)) * p := hmul p hps
  obtain ⟨-, hb', -, -, -⟩ := symAlg n l (monomial a * dPol n (t ^ l) * p)
  set y := monomial a * dPol n (t ^ l) * p with hy
  have hcE := hν r hr h (by rw [hSh, ← hSy, hyr])
  have hck := hν' r' hr' f (by rw [hSf, ← hSy, hb', hyr'])
  rw [← hyr] at hcE
  rw [← hyr'] at hck
  have hanti : ∀ b ∈ y.coeff.support, Antitone b := fun b hb => (hSD b hb).antitone
  have hantl : ∀ b ∈ y.coeff.support, Antitone ((l : ℤ) • b) := fun b hb i j hij => by
    have := hanti b hb hij
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hmE : thP μE y ∈ locallyConstantCompactSupport (GL (Fin n) E) ℂ ℂ :=
    Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (th_mem E μE (hanti b hb))
  have hmk : thP μk (bc l y) ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ := by
    rw [thP_bc]
    exact Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (th_mem k μk (hantl b hb))
  rw [← lin_eq_of_sub _ (comm μE) ΛE hlE hzE hmE (HeckeAlgebra.mem _) hcE,
    ← lin_eq_of_sub _ (comm μk) Λk hlk hzk hmk (HeckeAlgebra.mem _) hck, thP_bc]
  unfold thP Finsupp.sum
  rw [lin_sum _ ΛE hlE _ _ _ fun b hb => th_mem E μE (hanti b hb),
    lin_sum _ Λk hlk _ _ _ fun b hb => th_mem k μk (hantl b hb)]
  exact Finset.sum_congr rfl fun b hb => by rw [hth b (hSD b hb)]
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open ValuativeRel in
private theorem iw_eq (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F = (iwahori F n : Set (GL (Fin n) F)) := by
  ext g
  constructor
  · rintro ⟨⟨u, rfl⟩, hl⟩
    refine ⟨u, ?_, rfl⟩
    change residueReduction F n u ∈ borel n _
    rw [mem_borel_iff]
    intro i j hij
    rw [residueReduction_apply]
    exact (residue_eq_zero_iff_valuation_lt_one F (u i j)).mpr (hl i j hij)
  · intro hg
    exact ⟨iwahori_le_integralGL F n hg, ((mem_iwahori_iff F n).1 hg).2.1⟩

open ValuativeRel in
private theorem unif (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    PositivityTheory.Rg.Tf.Loc.IsUniformiser ((uniformizerUnit F : Fˣ) : F) := by
  refine ⟨valuation_uniformizer_lt_one F, Units.ne_zero _, fun x hx => ?_⟩
  let y : 𝒪[F] := ⟨x, (Valuation.mem_integer_iff _ _).mpr hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (residue_eq_zero_iff_valuation_lt_one F y).mpr hx
  have h1 := (mem_maximalIdeal_pow_iff F (m := 1) (y := y)).1 (by rwa [pow_one])
  simpa using h1

open ValuativeRel in
private theorem diag_mem (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    (t : Fin n → Fˣ) (ht : ∀ i, valuation F ((t i : Fˣ) : F) = 1) : diagGL F n t ∈ iwahori F n := by
  have he : ∀ i j, ((diagGL F n t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      Matrix.diagonal (fun i => ((t i : Fˣ) : F)) i j := fun i j => rfl
  refine (mem_iwahori_iff F n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [he]
    by_cases h : i = j
    · subst h
      simp [ht]
    · simp [Matrix.diagonal_apply_ne _ h]
  · rw [he, Matrix.diagonal_apply_ne _ hij.ne']
    simp
  · rw [he]
    simp [ht]

theorem UpperTheory.ConvolutionTheory.H.defBridge :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ),
      PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) F = integralGL F n ∧
      PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F = (iwahori F n : Set (GL (Fin n) F)) ∧
      (∃ ϖ : Fˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : F)) ∧
      ∀ ϖ : Fˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : F) → ∀ a : Fin n → ℤ,
        PositivityTheory.Rg.Tf.Loc.iwahoriFn F (PositivityTheory.Rg.Tf.Loc.diagPow ϖ a) = uFn F a := by
  intro F _ _ _ _ n
  have hI := iw_eq F n
  refine ⟨rfl, hI, ⟨uniformizerUnit F, unif F⟩, fun ϖ hϖ a => ?_⟩
  have h0 := unif F
  have hv : ValuativeRel.valuation F (ϖ : F) = ValuativeRel.valuation F ((uniformizerUnit F : Fˣ) : F) :=
    le_antisymm (h0.2.2 _ hϖ.1) (hϖ.2.2 _ h0.1)
  set u : Fˣ := ϖ * (uniformizerUnit F)⁻¹ with hu
  have hu1 : ValuativeRel.valuation F (u : F) = 1 := by
    have hne : ValuativeRel.valuation F ((uniformizerUnit F : Fˣ) : F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
    rw [hu, Units.val_mul, map_mul, hv, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ hne]
  have hd : diagGL F n (fun i => u ^ a i) ∈ iwahori F n := by
    refine diag_mem F n _ fun i => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu1, one_zpow]
  have hfac : PositivityTheory.Rg.Tf.Loc.diagPow ϖ a = torusPow F n a * diagGL F n (fun i => u ^ a i) := by
    have : PositivityTheory.Rg.Tf.Loc.diagPow ϖ a = diagGL F n (fun i => ϖ ^ a i) := Units.ext rfl
    rw [this, torusPow, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, hu, ← mul_zpow]
    simp
  unfold PositivityTheory.Rg.Tf.Loc.iwahoriFn uFn dco
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, hI, SetLike.mem_coe, hfac]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, _ * y, mul_mem hd hy, by simp only [mul_assoc]⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, (diagGL F n (fun i => u ^ a i))⁻¹ * y, mul_mem (inv_mem hd) hy, by simp only [mul_assoc, mul_inv_cancel_left]⟩
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open ValuativeRel in
theorem UpperTheory.ConvolutionTheory.H.unrQ :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k E →
      qF E = qF k ^ Module.finrank k E ∧
      ∀ ϖ : kˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : k) → PositivityTheory.Rg.Tf.Loc.IsUniformiser (algebraMap k E (ϖ : k)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨π, hπ1, hπ2⟩
  have hlt : ∀ a : k, valuation E (algebraMap k E a) < 1 ↔ valuation k a < 1 := fun a =>
    Valuation.HasExtension.val_map_lt_one_iff (valuation k) (valuation E) a
  have hπk : valuation k π < 1 := (hlt π).1 hπ1
  refine ⟨?_, fun ϖ ⟨h1, h2, h3⟩ => ⟨(hlt _).2 h1, (map_ne_zero _).2 h2, fun x hx => (hπ2 x hx).trans ?_⟩⟩
  · have hmem : ∀ {F : Type} [Field F] [ValuativeRel F] (x : 𝒪[F]),
        x ∈ IsLocalRing.maximalIdeal 𝒪[F] ↔ valuation F (x : F) < 1 := fun x =>
      Valuation.mem_maximalIdeal_iff _ _
    let p : 𝒪[k] := ⟨π, hπk.le⟩
    have hle : IsLocalRing.maximalIdeal 𝒪[E] ≤
        (IsLocalRing.maximalIdeal 𝒪[k]).map (algebraMap 𝒪[k] 𝒪[E]) := by
      intro x hx
      have hd : algebraMap 𝒪[k] 𝒪[E] p ∣ x :=
        (Valuation.integer.integers (valuation E)).le_iff_dvd.1 (hπ2 x ((hmem x).1 hx))
      obtain ⟨c, rfl⟩ := hd
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hmem p).2 hπk))
    rw [GroundTheory.LocalField.map_maximalIdeal] at hle
    have he : GroundTheory.LocalField.ramificationIndex k E = 1 := by
      have hpos := GroundTheory.LocalField.ramificationIndex_pos k E
      by_contra hne
      have h2 : 2 ≤ GroundTheory.LocalField.ramificationIndex k E := by omega
      have h3 := hle.trans (Ideal.pow_le_pow_right h2)
      have h4 := Ideal.pow_succ_lt_pow (GroundTheory.LocalField.maximalIdeal_ne_bot E) 1
      rw [pow_one] at h4
      exact not_le_of_gt h4 h3
    have hf := (GroundTheory.LocalField.isUnramified_iff_finrank_residueField k E).1 ⟨he⟩
    rw [← hf]
    exact Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := 𝓀[E])
  · exact (Valuation.HasExtension.val_map_le_iff (valuation k) (valuation E) _ _).2 (h3 π hπk)
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem quot_smul {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H)
    (c : ℂ) (F : G → ℂ) :
    PositivityTheory.Rg.Tf.Loc.quotIntegral μ H ν (fun g => c * F g) = c * PositivityTheory.Rg.Tf.Loc.quotIntegral μ H ν F := by
  unfold PositivityTheory.Rg.Tf.Loc.quotIntegral
  split_ifs with h
  · rw [← integral_const_mul]
    simp only [mul_assoc]
  · simp

private theorem match_smul {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} [TopologicalSpace k] [TopologicalSpace E]
    [MeasurableSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)]
    {σ : E ≃ₐ[k] E} {μE : Measure (GL (Fin n) E)} {μk : Measure (GL (Fin n) k)} {φ : GL (Fin n) E → ℂ} {f : GL (Fin n) k → ℂ}
    (h : UpperTheory.ConvolutionTheory.Loc.Match σ μE μk φ f) (c : ℂ) : UpperTheory.ConvolutionTheory.Loc.Match σ μE μk (c • φ) (c • f) := by
  refine ⟨fun δ γ x μδ μγ h1 h2 h3 h4 h5 => ?_, fun γ μγ h1 h2 h3 => ?_⟩
  · have := h.1 δ γ x μδ μγ h1 h2 h3 h4 h5
    unfold PositivityTheory.Rg.Tf.Loc.twOrbIntegralC PositivityTheory.Rg.Tf.Loc.orbIntegralC at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [quot_smul, quot_smul, this]
  · have := h.2 γ μγ h1 h2 h3
    unfold PositivityTheory.Rg.Tf.Loc.orbIntegralC at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [quot_smul, this, mul_zero]

private theorem half_eq {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {l : ℕ} (hq : qF E = qF k ^ l)
    {n : ℕ} (a : Fin n → ℤ) : halfModulus k ((l : ℤ) • a) = halfModulus E a := by
  have hs : sqrtQ E = sqrtQ k ^ l := by
    have h1 : NNReal.sqrt (qF E : NNReal) = NNReal.sqrt (qF k : NNReal) ^ l := by
      rw [NNReal.sqrt_eq_iff_eq_sq, ← pow_mul, mul_comm, pow_mul, NNReal.sq_sqrt, hq, Nat.cast_pow]
    rw [sqrtQ, sqrtQ, h1, NNReal.coe_pow, Complex.ofReal_pow]
  have hr : rhoPair ((l : ℤ) • a) = (l : ℤ) * rhoPair a := by
    simp only [rhoPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [halfModulus_eq, halfModulus_eq, hs, hr, ← zpow_natCast, ← zpow_mul, mul_neg]

private theorem incl_diagPow {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} (ϖ : kˣ) (a : Fin n → ℤ) :
    (PositivityTheory.Rg.Tf.Loc.incl (PositivityTheory.Rg.Tf.Loc.diagPow ϖ a) : GL (Fin n) E) =
      PositivityTheory.Rg.Tf.Loc.diagPow (Units.map (algebraMap k E : k →* E) ϖ) a := by
  ext i j
  change algebraMap k E (Matrix.diagonal (fun i => ((ϖ ^ a i : kˣ) : k)) i j) =
    Matrix.diagonal (fun i => (((Units.map (algebraMap k E : k →* E) ϖ) ^ a i : Eˣ) : E)) i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem UpperTheory.ConvolutionTheory.H.thMatch :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k E →
      ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) [μE.IsHaarMeasure] [μk.IsHaarMeasure],
      ∀ a : Fin n → ℤ, StrictAnti a → UpperTheory.ConvolutionTheory.Loc.Match σ μE μk (th μE a) (th μk ((Module.finrank k E : ℤ) • a)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ hu σ hσ n _ _ _ _ μE μk hE hk a ha
  obtain ⟨-, hIk, ⟨ϖ, hϖ⟩, hfk⟩ := defBridge k n
  obtain ⟨-, hIE, -, hfE⟩ := defBridge E n
  obtain ⟨hq, hun⟩ := unrQ k E hu
  have h := UpperTheory.ConvolutionTheory.Loc.elemMatch k E hu σ hσ n μE μk hE hk ϖ hϖ a ha
  rw [incl_diagPow, hfE _ (hun ϖ hϖ), hfk ϖ hϖ, hIk, hIE] at h
  have hne : μE.real (iwahori E n : Set (GL (Fin n) E)) ≠ 0 := by
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨((isOpen_iwahori E n).measure_pos μE ⟨1, one_mem _⟩).ne', (isCompact_iwahori E n).measure_lt_top.ne⟩
  have hne' : (μE.real (iwahori E n : Set (GL (Fin n) E)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hne
  have h2 := match_smul h (halfModulus E a / (μE.real (iwahori E n : Set (GL (Fin n) E)) : ℂ))
  rw [smul_smul] at h2
  unfold th
  rw [half_eq hq]
  convert h2 using 2
  · rw [← measureReal_def, ← measureReal_def, Complex.ofReal_div]
    field_simp
  · rfl
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

section

variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] {n : ℕ}

private theorem val_sig (σ : E ≃ₐ[k] E) (x : E) :
    ValuativeRel.valuation E (σ x) = ValuativeRel.valuation E x :=
  GroundTheory.LocalField.valuation_algEquiv_apply k E σ x

private theorem sig_apply (σ : E ≃ₐ[k] E) (g : GL (Fin n) E) (i j : Fin n) :
    ((PositivityTheory.Rg.Tf.Loc.sigmaGL σ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      σ ((g : Matrix (Fin n) (Fin n) E) i j) := rfl

private theorem sig_symm (σ : E ≃ₐ[k] E) (g : GL (Fin n) E) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ.symm (PositivityTheory.Rg.Tf.Loc.sigmaGL σ g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sig_apply, sig_apply, AlgEquiv.symm_apply_apply]

private theorem sig_mem_K (σ : E ≃ₐ[k] E) {g : GL (Fin n) E} (hg : g ∈ integralGL E n) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ integralGL E n := by
  rw [mem_integralGL_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [sig_apply, Valuation.mem_integer_iff, val_sig]
    exact hg.1 i j
  · rw [← map_inv, sig_apply, Valuation.mem_integer_iff, val_sig]
    exact hg.2 i j

private theorem sig_mem_I (σ : E ≃ₐ[k] E) {g : GL (Fin n) E} (hg : g ∈ iwahori E n) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ iwahori E n := by
  rw [mem_iwahori_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩
  · rw [sig_apply, val_sig]
    exact hg.1 i j
  · rw [sig_apply, val_sig]
    exact hg.2.1 i j h
  · rw [sig_apply, val_sig]
    exact hg.2.2 i

private theorem diag_mem_I {d : Fin n → Eˣ} (hd : ∀ i, ValuativeRel.valuation E (d i : E) = 1) :
    diagGL E n d ∈ iwahori E n := by
  rw [mem_iwahori_iff]
  refine ⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩
  · rw [coe_diagGL]
    by_cases e : i = j
    · subst e
      rw [Matrix.diagonal_apply_eq, hd]
    · rw [Matrix.diagonal_apply_ne _ e, map_zero]
      exact zero_le'
  · rw [coe_diagGL, Matrix.diagonal_apply_ne _ h.ne', map_zero]
    exact zero_lt_one
  · rw [coe_diagGL, Matrix.diagonal_apply_eq, hd]

private theorem sig_torusPow (σ : E ≃ₐ[k] E) (a : Fin n → ℤ) :
    ∃ u ∈ iwahori E n, PositivityTheory.Rg.Tf.Loc.sigmaGL σ (torusPow E n a) = torusPow E n a * u := by
  have h0 : (GLnLocal.uniformizer E : E) ≠ 0 := (uniformizerUnit E).ne_zero
  have hs : σ (GLnLocal.uniformizer E : E) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff σ σ.injective]
  let v : Eˣ := Units.mk0 (σ (GLnLocal.uniformizer E : E) / (GLnLocal.uniformizer E : E)) (div_ne_zero hs h0)
  have hv : ValuativeRel.valuation E (v : E) = 1 := by
    rw [Units.val_mk0, map_div₀, val_sig, div_self]
    exact (Valuation.ne_zero_iff _).2 h0
  refine ⟨diagGL E n fun i => v ^ a i, diag_mem_I fun i => ?_, ?_⟩
  · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hv, one_zpow]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [sig_apply, Units.val_mul, coe_torusPow, coe_diagGL, Matrix.diagonal_mul_diagonal]
    by_cases e : i = j
    · subst e
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, Units.val_zpow_eq_zpow_val,
        Units.val_mk0, div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ h0)]
    · rw [Matrix.diagonal_apply_ne _ e, Matrix.diagonal_apply_ne _ e, map_zero]

private theorem sig_mem_dco (σ : E ≃ₐ[k] E) (a : Fin n → ℤ) {g : GL (Fin n) E} (h : g ∈ dco E a) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ dco E a := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  obtain ⟨u, hu, e⟩ := sig_torusPow σ a
  refine ⟨PositivityTheory.Rg.Tf.Loc.sigmaGL σ x, sig_mem_I σ hx, u * PositivityTheory.Rg.Tf.Loc.sigmaGL σ y,
    mul_mem hu (sig_mem_I σ hy), ?_⟩
  rw [map_mul, map_mul, e]
  simp only [mul_assoc]

end

theorem UpperTheory.ConvolutionTheory.H.sigInv :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) (n : ℕ) (x : GL (Fin n) E),
      oneK E n (PositivityTheory.Rg.Tf.Loc.sigmaGL σ x) = oneK E n x ∧ ∀ a : Fin n → ℤ, uFn E a (PositivityTheory.Rg.Tf.Loc.sigmaGL σ x) = uFn E a x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ n x
  have hK : PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ integralGL E n ↔ x ∈ integralGL E n :=
    ⟨fun h => by simpa only [sig_symm] using sig_mem_K σ.symm h, sig_mem_K σ⟩
  have hD : ∀ a : Fin n → ℤ, PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ dco E a ↔ x ∈ dco E a := fun a =>
    ⟨fun h => by simpa only [sig_symm] using sig_mem_dco σ.symm a h, sig_mem_dco σ a⟩
  refine ⟨?_, fun a => ?_⟩
  · unfold oneK
    by_cases h : x ∈ integralGL E n
    · rw [Set.indicator_of_mem (SetLike.mem_coe.2 (hK.2 h)), Set.indicator_of_mem (SetLike.mem_coe.2 h)]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hK.1 h')), Set.indicator_of_notMem h]
  · unfold uFn
    by_cases h : x ∈ dco E a
    · rw [Set.indicator_of_mem ((hD a).2 h), Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h ((hD a).1 h')), Set.indicator_of_notMem h]
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem lin_of {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (Λ : (G → ℂ) → ℂ)
    (hs : ∀ (c : ℂ) (φ : G → ℂ), Λ (c • φ) = c * Λ φ)
    (ha : ∀ φ ψ : G → ℂ, Continuous φ → HasCompactSupport φ → Continuous ψ → HasCompactSupport ψ →
      Λ (φ + ψ) = Λ φ + Λ ψ) :
    ∀ x ∈ locallyConstantCompactSupport G ℂ ℂ, ∀ y ∈ locallyConstantCompactSupport G ℂ ℂ, ∀ c : ℂ,
      Λ (c • x + y) = c * Λ x + Λ y := by
  intro x hx y hy c
  have hcx := Submodule.smul_mem (locallyConstantCompactSupport G ℂ ℂ) c hx
  rw [ha _ _ hcx.1.continuous hcx.2 hy.1.continuous hy.2, hs]

private theorem comm_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    (Λ : (GL (Fin n) F → ℂ) → ℂ)
    (hs : ∀ (c : ℂ) (φ : GL (Fin n) F → ℂ), Λ (c • φ) = c * Λ φ)
    (ha : ∀ φ ψ : GL (Fin n) F → ℂ, Continuous φ → HasCompactSupport φ → Continuous ψ → HasCompactSupport ψ →
      Λ (φ + ψ) = Λ φ + Λ ψ)
    (hc : ∀ a b : GL (Fin n) F → ℂ, (a = oneK F n ∨ ∃ l, Antitone l ∧ a = uFn F l) →
      a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ → b ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ →
      Λ (groupConv μ a b) = Λ (groupConv μ b a)) :
    ∀ x ∈ comm μ, Λ x = 0 := by
  obtain ⟨i1, i2, i3, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop F n
  have key : ∀ x ∈ comm μ, Continuous x ∧ HasCompactSupport x ∧ Λ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, ha', hb, rfl⟩ := hx
      have ham : a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := by
        rcases ha' with rfl | ⟨l, hl, rfl⟩
        · exact indicator_mem_locallyConstantCompactSupport (GLnLocal.isCompact_integralGL F n)
            (GLnLocal.isOpen_integralGL F n) (1 : ℂ)
        · exact (UpperTheory.ConvolutionTheory.H.dcoShape F n l hl).2.2.1
      obtain ⟨c1, c2⟩ : Continuous (groupConv μ a b) ∧ HasCompactSupport (groupConv μ a b) :=
        UpperTheory.V.Z.Tf.Orb.convTest _ μ inferInstance a b ham.1.continuous ham.2 hb.1.continuous hb.2
      obtain ⟨d1, d2⟩ : Continuous (groupConv μ b a) ∧ HasCompactSupport (groupConv μ b a) :=
        UpperTheory.V.Z.Tf.Orb.convTest _ μ inferInstance b a hb.1.continuous hb.2 ham.1.continuous ham.2
      have e : groupConv μ a b - groupConv μ b a = groupConv μ a b + (-1 : ℂ) • groupConv μ b a := by
        rw [neg_one_smul, sub_eq_add_neg]
      have hneg : Continuous ((-1 : ℂ) • groupConv μ b a) := d1.const_smul _
      have hnegc : HasCompactSupport ((-1 : ℂ) • groupConv μ b a) :=
        HasCompactSupport.mono d2 (Function.support_const_smul_subset _ _)
      refine ⟨?_, ?_, ?_⟩
      · rw [e]; exact Continuous.add c1 hneg
      · rw [e]; exact HasCompactSupport.add c2 hnegc
      · rw [e, ha _ _ c1 c2 hneg hnegc, hs, hc a b ha' ham hb]
        ring
    | zero =>
      refine ⟨continuous_const, HasCompactSupport.zero, ?_⟩
      have := hs 0 0
      simpa using this
    | add x y _ _ hx hy =>
      exact ⟨hx.1.add hy.1, hx.2.1.add hy.2.1, by rw [ha _ _ hx.1 hx.2.1 hy.1 hy.2.1, hx.2.2, hy.2.2, add_zero]⟩
    | smul c x _ hx =>
      exact ⟨hx.1.const_smul c, HasCompactSupport.mono hx.2.1 (Function.support_const_smul_subset _ _),
        by rw [hs, hx.2.2, mul_zero]⟩
  exact fun x hx => (key x hx).2.2

private theorem reg_of_norm {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} (σ : E ≃ₐ[k] E)
    {δ x : GL (Fin n) E} {γ : GL (Fin n) k} (hr : PositivityTheory.Rg.Tf.Loc.IsTwRegSemisimple σ δ)
    (hN : PositivityTheory.Rg.Tf.Loc.normGL σ δ = x * PositivityTheory.Rg.Tf.Loc.incl γ * x⁻¹) :
    PositivityTheory.Rg.Tf.Loc.IsRegSemisimple γ := by
  unfold PositivityTheory.Rg.Tf.Loc.IsTwRegSemisimple at hr
  unfold PositivityTheory.Rg.Tf.Loc.IsRegSemisimple
  rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at hr
  have h : ((PositivityTheory.Rg.Tf.Loc.incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((γ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
  rw [h, Matrix.charpoly_map] at hr
  exact (Polynomial.separable_map _).1 hr

theorem UpperTheory.ConvolutionTheory.H.deepHecke :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k E →
      ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) [μE.IsHaarMeasure] [μk.IsHaarMeasure],
      μE (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 → μk (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1 →
      ∀ P : Finset (LaurentRing n), (∀ p ∈ P, p ∈ symmetricLaurent n) → ∀ z : Fin n → ℂˣ,
      ∃ g ∈ symmetricLaurent n, g ∈ (polyEmb n).range ∧ evalAt z g ≠ 0 ∧ ∀ p ∈ Submodule.span ℂ (P : Set (LaurentRing n)),
        ∀ (h : SphericalHecke μE (F := E) (n := n)) (f : SphericalHecke μk (F := k) (n := n)),
          satakeTransform μE h = g * p → satakeTransform μk f = bc (Module.finrank k E) (g * p) →
          UpperTheory.ConvolutionTheory.Loc.Match σ μE μk (fun x => (h : HeckeAlgebra μE) x) fun x => (f : HeckeAlgebra μk) x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ hu σ hσ n _ _ _ _ μE μk hE hk h1 h2 P hP z
  obtain ⟨hq, -⟩ := UpperTheory.ConvolutionTheory.H.unrQ k E hu
  rw [(UpperTheory.ConvolutionTheory.H.defBridge E n).1] at h1
  rw [(UpperTheory.ConvolutionTheory.H.defBridge k n).1] at h2
  have hq' : (qF E : ℂ) = (qF k : ℂ) ^ Module.finrank k E := by rw [hq]; push_cast; rfl
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ := UpperTheory.ConvolutionTheory.H.deepAbs k E n (Module.finrank k E) Module.finrank_pos hq' μE μk h1 h2 P hP z
  have hcE : ∀ (δ : GL (Fin n) E) (μδ : Measure (PositivityTheory.Rg.Tf.Loc.twCent (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) δ)),
      PositivityTheory.Rg.Tf.Loc.IsTwRegSemisimple σ δ → μδ.IsHaarMeasure →
      ∀ x ∈ comm μE, PositivityTheory.Rg.Tf.Loc.twOrbIntegralC (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) μE δ μδ x = 0 := by
    intro δ μδ hr hm
    obtain ⟨ls, la⟩ := UpperTheory.V.Z.Tf.Orb.twOrbLin_holds k E σ hσ n μE inferInstance δ hr μδ hm
    have tc := UpperTheory.V.Z.Tf.Orb.twOrbComm_holds k E σ hσ n μE inferInstance δ hr μδ hm
    refine comm_zero μE _ ls la fun a b ha' ham hb => ?_
    refine tc a b ham.1.continuous ham.2 hb.1.continuous hb.2 fun x => ?_
    rcases ha' with rfl | ⟨l, hl, rfl⟩
    · exact (UpperTheory.ConvolutionTheory.H.sigInv k E σ n x).1
    · exact (UpperTheory.ConvolutionTheory.H.sigInv k E σ n x).2 l
  have hck : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
      PositivityTheory.Rg.Tf.Loc.IsRegSemisimple γ → μγ.IsHaarMeasure →
      ∀ x ∈ comm μk, PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ x = 0 := by
    intro γ μγ hr hm
    obtain ⟨ls, la⟩ := UpperTheory.V.Z.Tf.Orb.orbLin_holds k n μk inferInstance γ hr μγ hm
    have oc := UpperTheory.V.Z.Tf.Orb.orbComm_holds k n μk inferInstance γ hr μγ hm
    exact comm_zero μk _ ls la fun a b _ ham hb => oc a b ham.1.continuous ham.2 hb.1.continuous hb.2
  have hlk : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
      PositivityTheory.Rg.Tf.Loc.IsRegSemisimple γ → μγ.IsHaarMeasure →
      ∀ x ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ y ∈ locallyConstantCompactSupport (GL (Fin n) k) ℂ ℂ, ∀ c : ℂ,
        PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ (c • x + y) =
          c * PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ x + PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ y := by
    intro γ μγ hr hm
    obtain ⟨ls, la⟩ := UpperTheory.V.Z.Tf.Orb.orbLin_holds k n μk inferInstance γ hr μγ hm
    exact lin_of _ ls la
  refine ⟨g, hg1, hg2, hg3, fun p hp h f hh hf => ⟨?_, ?_⟩⟩
  · intro δ γ x μδ μγ hr hN hδ hγ hm
    have hrγ := reg_of_norm σ hr hN
    obtain ⟨ls, la⟩ := UpperTheory.V.Z.Tf.Orb.twOrbLin_holds k E σ hσ n μE inferInstance δ hr μδ hδ
    exact hg4 p hp h f hh hf (PositivityTheory.Rg.Tf.Loc.twOrbIntegralC (PositivityTheory.Rg.Tf.Loc.sigmaGL σ) μE δ μδ)
      (PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ) (lin_of _ ls la) (hcE δ μδ hr hδ) (hlk γ μγ hrγ hγ) (hck γ μγ hrγ hγ)
      fun a ha => (UpperTheory.ConvolutionTheory.H.thMatch k E hu σ hσ n μE μk a ha).1 δ γ x μδ μγ hr hN hδ hγ hm
  · intro γ μγ hr hnot hγ
    exact (hg4 p hp h f hh hf (fun _ => 0) (PositivityTheory.Rg.Tf.Loc.orbIntegralC μk γ μγ)
      (fun _ _ _ _ _ => by simp) (fun _ _ => rfl) (hlk γ μγ hr hγ) (hck γ μγ hr hγ)
      fun a ha => ((UpperTheory.ConvolutionTheory.H.thMatch k E hu σ hσ n μE μk a ha).2 γ μγ hr hnot hγ).symm).symm
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

private theorem evalAt_polynomialEmbed {n : ℕ} (z : Fin n → ℂˣ) (Q : MvPolynomial (Fin n) ℂ) :
    evalAt z (polyEmb n Q) = MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) Q := by
  have h : (evalAt z).comp (polyEmb n) = MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, polyEmb_X, evalAt_single, MvPolynomial.aeval_X, one_mul,
      monomialChar_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact AlgHom.congr_fun h Q

private theorem baseChange_polynomialEmbed {n : ℕ} (l : ℕ) (Q : MvPolynomial (Fin n) ℂ) :
    bc l (polyEmb n Q) = polyEmb n (MvPolynomial.expand l Q) := by
  have h : (bc l).comp (polyEmb n) = (polyEmb n).comp (MvPolynomial.expand l) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.expand_X, map_pow, polyEmb_X,
      AddMonoidAlgebra.single_pow, one_pow]
    simp [bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]
  exact AlgHom.congr_fun h Q

private theorem aeval_elemSymm_power {n : ℕ} (l : ℕ) (i : Fin n) :
    MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) (powE l i) =
      MvPolynomial.expand l (MvPolynomial.esymm (Fin n) ℂ (i + 1)) := by
  have h := (MvPolynomial.esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
    ⟨MvPolynomial.expand l (MvPolynomial.esymm (Fin n) ℂ (i + 1)), fun w => by
      rw [MvPolynomial.rename_expand, MvPolynomial.esymm_isSymmetric]⟩
  have h2 := congrArg Subtype.val h
  rw [← MvPolynomial.esymmAlgHom_apply]
  exact h2

private theorem aeval_aeval_elemSymm_power {n : ℕ} (l : ℕ) (γ : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))
        (MvPolynomial.aeval (powE l) γ) =
      MvPolynomial.expand l
        (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) := by
  have h : (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))).comp
        (MvPolynomial.aeval (powE l)) =
      (MvPolynomial.expand l).comp
        (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      aeval_elemSymm_power]
  exact AlgHom.congr_fun h γ

private theorem polynomialEmbed_symmetric_mem {n : ℕ} (γ : MvPolynomial (Fin n) ℂ) :
    polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) ∈
      symmetricLaurent n := by
  intro σ
  have h := (MvPolynomial.esymmAlgHom (Fin n) ℂ n γ).2
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.mem_symmetricSubalgebra] at h
  rw [← polyEmb_rename, h σ]

theorem UpperTheory.ConvolutionTheory.H.polyAlg :
    ∀ n : ℕ,
      (∀ g ∈ symmetricLaurent n, g ∈ (polyEmb n).range → ∃ γ : MvPolynomial (Fin n) ℂ, polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) = g) ∧
      (∀ (γ : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂˣ), evalAt z (polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ)) =
        MvPolynomial.eval (fun i : Fin n => (Finset.univ.val.map fun j => (z j : ℂ)).esymm (i + 1)) γ) ∧
      (∀ (l : ℕ) (γ : MvPolynomial (Fin n) ℂ), bc l (polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ)) = polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) (MvPolynomial.aeval (powE l) γ))) ∧
      ∀ D : ℕ, ∃ P : Finset (LaurentRing n), (∀ y ∈ P, y ∈ symmetricLaurent n) ∧
        ∀ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D → polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) ∈ Submodule.span ℂ (P : Set (LaurentRing n)) := by
  intro n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro g hg ⟨Q, rfl⟩
    have hQ : Q ∈ MvPolynomial.symmetricSubalgebra (Fin n) ℂ := by
      rw [MvPolynomial.mem_symmetricSubalgebra]
      intro σ
      apply polyEmb_injective
      rw [polyEmb_rename]
      exact hg σ
    obtain ⟨γ, hγ⟩ := MvPolynomial.esymmAlgHom_surjective ℂ (σ := Fin n) (n := n)
      (Fintype.card_fin n).le ⟨Q, hQ⟩
    refine ⟨γ, ?_⟩
    rw [← MvPolynomial.esymmAlgHom_apply, hγ]
    rfl
  · intro γ z
    rw [evalAt_polynomialEmbed]
    have h : (MvPolynomial.aeval (fun j : Fin n => (z j : ℂ))).comp
          (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))) =
        MvPolynomial.aeval (fun i : Fin n => (Finset.univ.val.map fun j => (z j : ℂ)).esymm (i + 1)) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        MvPolynomial.aeval_esymm_eq_multiset_esymm]
    have h2 := AlgHom.congr_fun h γ
    rw [AlgHom.comp_apply] at h2
    rw [h2, MvPolynomial.aeval_eq_eval]
  · intro l γ
    rw [baseChange_polynomialEmbed, aeval_aeval_elemSymm_power]
  · intro D
    classical
    let f : (Fin n → Fin (D + 1)) → LaurentRing n := fun c =>
      polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (c i : ℕ)) (1 : ℂ)))
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · intro y hy
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
      exact polynomialEmbed_symmetric_mem _
    · intro p hp
      rw [p.as_sum, map_sum, map_sum]
      refine Submodule.sum_mem _ fun s hs => ?_
      have hle : ∀ i, s i < D + 1 := fun i => by
        have h1 : s.degree ≤ p.totalDegree := MvPolynomial.le_totalDegree hs
        have h2 : s i ≤ s.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hm : MvPolynomial.monomial s (MvPolynomial.coeff s p) =
          MvPolynomial.coeff s p • MvPolynomial.monomial s (1 : ℂ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hm, map_smul, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨fun i => ⟨s i, hle i⟩, Finset.mem_univ _, ?_⟩)
      have hs' : (Finsupp.equivFunOnFinite.symm fun i => s i) = s := by
        ext i
        rfl
      simp only [f, hs']
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

theorem UpperTheory.ConvolutionTheory.H.sphIndep :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K) (p : MvPolynomial (Fin n) ℂ) (h : GL (Fin n) (w.adicCompletion K) → ℂ),
      GM.IsSph w p h → ∀ [MeasurableSpace (GL (Fin n) (w.adicCompletion K))] [BorelSpace (GL (Fin n) (w.adicCompletion K))]
        (m : Measure (GL (Fin n) (w.adicCompletion K))) [m.IsHaarMeasure], m (GLnLocal.integralGL (w.adicCompletion K) n) = 1 →
        ∃ H : SphericalHecke m (F := w.adicCompletion K) (n := n), (∀ x, (H : HeckeAlgebra m) x = h x) ∧ satakeTransform m H = polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) := by
  intro K _ _ n w p h hs inst instB m instH hm
  obtain ⟨i', b', m', h', hm', H, hH⟩ := hs
  have e : i' = inst := (@BorelSpace.measurable_eq _ _ i' b').trans (@BorelSpace.measurable_eq _ _ inst instB).symm
  subst e
  have hmm : m' = m := by
    have h1 := Measure.isMulLeftInvariant_eq_smul m' m
    have h2 := congrArg (fun μ : Measure (GL (Fin n) (w.adicCompletion K)) => μ (GLnLocal.integralGL (w.adicCompletion K) n)) h1
    simp only [Measure.smul_apply, hm, hm'] at h2
    have h3 : Measure.haarScalarFactor m' m = 1 := by
      simpa [ENNReal.smul_def] using h2.symm
    rw [h1, h3, one_smul]
  subst hmm
  exact ⟨H, hH⟩
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

private theorem haar_eq {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (m m' : Measure G) [m.IsHaarMeasure] [m'.IsHaarMeasure]
    {A : Set G} (hm : m A = 1) (hm' : m' A = 1) : m' = m := by
  have h1 := Measure.isMulLeftInvariant_eq_smul m' m
  have h2 := congrArg (fun μ : Measure G => μ A) h1
  simp only [Measure.smul_apply, hm, hm'] at h2
  have h3 : Measure.haarScalarFactor m' m = 1 := by
    simpa [ENNReal.smul_def] using h2.symm
  rw [h1, h3, one_smul]

private theorem haar_ex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by
    simpa [ho.interior_eq] using (⟨1, K.one_mem⟩ : (K : Set G).Nonempty)⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self⟩

private theorem exists_point {n : ℕ} (t : Multiset ℂ) (ht : t.card = n) (h0 : 0 ∉ t) :
    ∃ z : Fin n → ℂˣ, (Finset.univ.val.map fun j => (z j : ℂ)) = t := by
  induction t using Quotient.inductionOn with
  | h l =>
    have hl : l.length = n := ht
    subst hl
    refine ⟨fun j => Units.mk0 (l.get j) fun e => h0 (e ▸ List.get_mem l j), ?_⟩
    simp only [Units.val_mk0, Fin.univ_val_map, List.ofFn_get]
    rfl

open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb in
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin) in
theorem UpperTheory.ConvolutionTheory.H.locHeckeInert :
    UpperTheory.ConvolutionTheory.GM.LocHeckeInert := by
  intro F E _ _ _ _ _ _ σ hσ hp n _ v hu hsp w t ht h0 D
  obtain ⟨w', hw'⟩ := placeUniq_holds F E hp v hsp
  have hw : ∀ x : PlacesOver E v, x = w := fun x => (hw' x).trans (hw' w).symm
  obtain ⟨i1, i2, i3, i4, s, hs, hr, h1, h2, h3⟩ := placeData_holds F E σ hσ v w hw
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  letI mv : MeasurableSpace (GL (Fin n) (v.adicCompletion F)) := borel _
  haveI bv : BorelSpace (GL (Fin n) (v.adicCompletion F)) := ⟨rfl⟩
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨μE, hμE, vE⟩ := haar_ex _ (unitSB_holds (w.1.adicCompletion E) n).2.1 (unitSB_holds (w.1.adicCompletion E) n).1
  obtain ⟨μF, hμF, vF⟩ := haar_ex _ (unitSB_holds (v.adicCompletion F) n).2.1 (unitSB_holds (v.adicCompletion F) n).1
  obtain ⟨z, hz⟩ := exists_point t ht h0
  obtain ⟨a1, a2, a3, a4⟩ := polyAlg n
  obtain ⟨P, hP, hPD⟩ := a4 D
  obtain ⟨g, hg, hg', hgz, H⟩ := @deepHecke _ _ _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 (h3 (hu w)) s hs n _ _ _ _ μE μF hμE hμF
    vE vF P hP z
  obtain ⟨γ, rfl⟩ := a1 g hg hg'
  refine ⟨γ, by rwa [a2, hz] at hgz, fun p hpD h f hh hf => ?_⟩
  intro _ _ mv' bv' mE mF hE hF wE wF
  have e : mv' = mv := @BorelSpace.measurable_eq _ _ mv' bv'
  subst e
  obtain ⟨hH, hPl⟩ := @placeOfLocal_holds F E _ _ _ _ _ _ σ hσ v w hw i1 i2 i3 i4 s hs hr h1 h2 n _ _ _ _ mE mF hE hF _ _
  have hc : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have eE := haar_eq μE (mE.map (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w))) vE
    (by rw [Measure.map_apply hc.measurable (unitSB_holds _ n).1.measurableSet, ← placeInt_holds.2 F E v w hw n, wE])
  have eF := haar_eq μF mF vF (by rw [placeInt_holds.1 F v n, wF])
  obtain ⟨HE, hE1, hE2⟩ := sphIndep E n w.1 _ h hh μE (by rw [← placeInt_holds.1 E w.1 n, vE])
  obtain ⟨HF, hF1, hF2⟩ := sphIndep F n v _ f hf μF (by rw [← placeInt_holds.1 F v n, vF])
  have hm := H _ (hPD p hpD) HE HF (by rw [hE2, map_mul, map_mul]) (by rw [hF2, hr, ← a3, map_mul, map_mul])
  have e1 : (fun x => (HE : HeckeAlgebra μE) x) = h := funext hE1
  have e2 : (fun x => (HF : HeckeAlgebra μF) x) = f := funext hF1
  have m1 := (HE : HeckeAlgebra μE).mem
  have m2 := (HF : HeckeAlgebra μF).mem
  rw [e1, e2, ← eE, ← eF] at hm
  rw [show ((HE : HeckeAlgebra μE) : _ → ℂ) = h from e1] at m1
  rw [show ((HF : HeckeAlgebra μF) : _ → ℂ) = f from e2] at m2
  exact hPl h m1 f m2 hm
end
