import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.EigAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.OpBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.ProdNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientIff

section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

theorem UpperTheory.V.Z.Int.rootBound :
    UpperTheory.V.Z.Int.RootBound := by
  intro l _ ι S c hc h b hb
  by_contra hlt
  have hlt' : c < ‖ι.symm b‖ := not_le.mp hlt
  have hroot : Polynomial.eval b (S.map fun t => Polynomial.X - Polynomial.C t).prod = 0 := by
    rw [Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨Polynomial.X - Polynomial.C b, Multiset.mem_map.mpr ⟨b, hb, rfl⟩, by simp⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, Polynomial.eval_finset_sum, Finset.sum_range_succ'] at hroot
  have hn : 0 < S.card := Multiset.card_pos_iff_exists_mem.mpr ⟨b, hb⟩
  have h0 : S.esymm 0 = 1 := by simp [Multiset.esymm]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, pow_zero, one_mul, Nat.sub_zero, h0] at hroot
  have hK := congrArg ι.symm hroot
  simp only [map_add, map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at hK
  have heq : ‖ι.symm b‖ ^ S.card = ‖∑ j ∈ Finset.range S.card, (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1)))‖ := by
    rw [eq_neg_of_add_eq_zero_left hK, norm_neg, norm_pow]
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hn.ne')
    (fun j => (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1))))
  have hi' : i + 1 ≤ S.card := Finset.mem_range.mp hi
  have hj := h (i + 1) (by omega) hi'
  have hj' : ‖ι.symm (S.esymm (i + 1))‖ ≤ c ^ (i + 1) := hj
  have hpos : 0 < ‖ι.symm b‖ := lt_of_le_of_lt hc hlt'
  have hcp : c ^ (i + 1) < ‖ι.symm b‖ ^ (i + 1) := pow_lt_pow_left₀ hlt' hc (by omega)
  have hterm : ‖(-1 : PadicAlgCl l) ^ (i + 1) * (ι.symm (S.esymm (i + 1)) * ι.symm b ^ (S.card - (i + 1)))‖
      < ‖ι.symm b‖ ^ S.card := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow]
    calc ‖ι.symm (S.esymm (i + 1))‖ * ‖ι.symm b‖ ^ (S.card - (i + 1))
        < ‖ι.symm b‖ ^ (i + 1) * ‖ι.symm b‖ ^ (S.card - (i + 1)) :=
          mul_lt_mul_of_pos_right (lt_of_le_of_lt hj' hcp) (pow_pos hpos _)
      _ = ‖ι.symm b‖ ^ S.card := by rw [← pow_add]; congr 1; omega
  exact absurd (heq.le.trans hle) (not_le.mpr hterm)
end

section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section Nu

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private theorem nu_mul' (x y : ℂ) : nu ι (x * y) = nu ι x * nu ι y := by
  simp [nu, map_mul, norm_mul]

private theorem nu_pow' (x : ℂ) (k : ℕ) : nu ι (x ^ k) = nu ι x ^ k := by
  simp [nu, map_pow, norm_pow]

private theorem nu_zero' : nu ι 0 = 0 := by
  simp [nu]

private theorem nu_nonneg' (x : ℂ) : 0 ≤ nu ι x := norm_nonneg _

private theorem roots_le {q : ℂ} (hq : nu ι q ≤ 1) {c : ℝ} (hc : 0 ≤ c) (S : Multiset ℂ)
    (h : ∀ j, 1 ≤ j → j ≤ S.card → ∃ a : ℂ, q ^ j.choose 2 * a = S.esymm j ∧ nu ι a ≤ c ^ j) :
    ∀ b ∈ S, nu ι b ≤ c := by
  refine rootBound l ι S c hc fun j h1 h2 => ?_
  obtain ⟨a, ha, hb⟩ := h j h1 h2
  rw [← ha, nu_mul', nu_pow']
  calc nu ι q ^ j.choose 2 * nu ι a ≤ 1 * nu ι a :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (nu_nonneg' ι q) hq) (nu_nonneg' ι a)
    _ ≤ c ^ j := by rwa [one_mul]

end Nu

private theorem weight_bounds {n : ℕ} (hn : 1 ≤ n) (lam : DomWeight n) {lo hi : ℤ}
    (h : Within n (infOfWeight lam) lo hi) (i : Fin n) :
    lo + ((n : ℤ) - 1) ≤ lam.w i ∧ lam.w i ≤ hi := by
  have key : ∀ k : Fin n, lo + ((k : ℕ) : ℤ) ≤ lam.w k ∧ lam.w k ≤ hi + ((k : ℕ) : ℤ) := by
    intro k
    obtain ⟨m, hm, h1, h2⟩ := h ((lam.w k : ℂ) + (((n : ℂ) - 1) / 2 - (k : ℕ)))
      (Multiset.mem_map.2 ⟨k, Finset.mem_univ_val k, rfl⟩)
    have e1 : ((lam.w k - ((k : ℕ) : ℤ) : ℤ) : ℂ) = (m : ℂ) := by
      push_cast
      linear_combination hm
    have e2 : lam.w k - ((k : ℕ) : ℤ) = m := by exact_mod_cast e1
    omega
  have h0 := (key ⟨0, by omega⟩).2
  have h1 := (key ⟨n - 1, by omega⟩).1
  have a0 : lam.w i ≤ lam.w ⟨0, by omega⟩ := lam.anti (Fin.mk_le_of_le_val (Nat.zero_le _))
  have a1 : lam.w ⟨n - 1, by omega⟩ ≤ lam.w i := lam.anti (Fin.le_def.2 (by simp; omega))
  simp only at h0 h1
  omega

private theorem algSat_as_map (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem sq_factor (N n : ℕ) (hn : 1 ≤ n) :
    ((((N : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ 2 = (N : ℂ) ^ (n - 1) := by
  have h : ((N : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ 2 = (N : ℝ) ^ (n - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N), ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub hn]
    push_cast
    ring
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h

theorem coreU : CoreU := by
  intro l _ ι E _ _ _ n hn σ hσ lam hlam w hw τ B hc hB lo hi hW b hb
  obtain ⟨hun, hcard, hE⟩ := eigAll E n σ hσ w hw τ B hc hB
  obtain ⟨hv, hprod⟩ := prodNorm l ι E w
  have hvne : ∀ t ∈ Ov ι w, nu ι (t (unif w : E)) ≠ 0 := fun t ht => (hv t ht).1.ne'
  have hq1 : nu ι (normV w : ℂ) ≤ 1 := by
    rw [← hprod]
    exact Finset.prod_le_one (fun t ht => (hv t ht).1.le) fun t ht => (hv t ht).2.le
  have hq0 : 0 < nu ι (normV w : ℂ) := by
    rw [← hprod]
    exact Finset.prod_pos fun t ht => (hv t ht).1
  have hqne : (normV w : ℂ) ≠ 0 := by
    intro h0
    rw [h0, nu_zero'] at hq0
    exact lt_irrefl _ hq0
  have hlh : ∀ t i, lo t + ((n : ℤ) - 1) ≤ (lam t).w i ∧ (lam t).w i ≤ hi t :=
    fun t i => weight_bounds hn (lam t) (hW t) i
  have hop := opBound l ι E n hn σ hσ lam hlam w hw hun (fun t => lo t + ((n : ℤ) - 1)) hi hlh
  have hPhi : 0 ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-hi t) :=
    Finset.prod_nonneg fun t ht => zpow_nonneg (hv t ht).1.le _
  have hPlo : 0 ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (lo t + ((n : ℤ) - 1)) :=
    Finset.prod_nonneg fun t ht => zpow_nonneg (hv t ht).1.le _

  have hroot : ∀ x ∈ algSat n (normV w) B, nu ι x ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-hi t) := by
    refine roots_le ι hq1 hPhi _ fun j _ hj => ?_
    have hjn : j ≤ n := by simpa [algSat, hcard] using hj
    obtain ⟨s, s', hs, hs', he⟩ := hE j hjn
    refine ⟨((normV w : ℂ) ^ j.choose 2)⁻¹ * (algSat n (normV w) B).esymm j,
      mul_inv_cancel_left₀ (pow_ne_zero _ hqne) _, ?_⟩
    refine (hop j s _ fun f hf hsph => ?_).1 hs
    rw [mul_smul, ← (he f hf hsph).1, inv_smul_smul₀ (pow_ne_zero _ hqne)]

  have hinv : ∀ x ∈ algSat n (normV w) (B.map (·⁻¹)),
      nu ι x ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (lo t + ((n : ℤ) - 1)) := by
    refine roots_le ι hq1 hPlo _ fun j _ hj => ?_
    have hjn : j ≤ n := by simpa [algSat, hcard] using hj
    obtain ⟨s, s', hs, hs', he⟩ := hE j hjn
    refine ⟨((normV w : ℂ) ^ j.choose 2)⁻¹ * (algSat n (normV w) (B.map (·⁻¹))).esymm j,
      mul_inv_cancel_left₀ (pow_ne_zero _ hqne) _, ?_⟩
    refine (hop j s' _ fun f hf hsph => ?_).2 hs'
    rw [mul_smul, ← (he f hf hsph).2, inv_smul_smul₀ (pow_ne_zero _ hqne)]
  constructor
  · have h1 := hroot b hb
    have h2 : (∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-hi t)) *
        ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ hi t = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun t ht => ?_
      rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hvne t ht))]
    have h3 : 0 ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ hi t :=
      Finset.prod_nonneg fun t ht => zpow_nonneg (hv t ht).1.le _
    show nu ι b * ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ hi t ≤ 1
    rw [← h2]
    exact mul_le_mul_of_nonneg_right h1 h3
  · have hb2 : b ∈ B.map (fun α : ℂˣ => ((((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) * (α : ℂ)) := by
      rwa [algSat_as_map] at hb
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hb2
    set r : ℂ := (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
    have hr2 : r ^ 2 = (normV w : ℂ) ^ (n - 1) := sq_factor (normV w) n hn
    have hrne : r ≠ 0 := by
      intro h0
      rw [h0] at hr2
      exact pow_ne_zero _ hqne (by simpa using hr2.symm)
    have hαne : (α : ℂ) ≠ 0 := α.ne_zero
    have hmem : r * ((α⁻¹ : ℂˣ) : ℂ) ∈ algSat n (normV w) (B.map (·⁻¹)) :=
      by
      rw [algSat_as_map]
      exact Multiset.mem_map.2 ⟨α⁻¹, Multiset.mem_map.2 ⟨α, hα, rfl⟩, rfl⟩
    have h1 := hinv _ hmem
    have hb' : (r * (α : ℂ))⁻¹ * (normV w : ℂ) ^ (n - 1) = r * ((α⁻¹ : ℂˣ) : ℂ) := by
      rw [← hr2, Units.val_inv_eq_inv_val]
      field_simp
    rw [← hb', nu_mul', nu_pow'] at h1
    have hsplit : ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (lo t + ((n : ℤ) - 1)) =
        (∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ lo t) * nu ι (normV w : ℂ) ^ (n - 1) := by
      rw [← hprod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun t ht => ?_
      have : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
      rw [zpow_add₀ (hvne t ht), this, zpow_natCast]
    rw [hsplit] at h1
    have h2 := le_of_mul_le_mul_right h1 (pow_pos hq0 _)
    have h3 : (∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ lo t) *
        ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-lo t) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun t ht => ?_
      rw [_root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (hvne t ht))]
    have h4 : 0 ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-lo t) :=
      Finset.prod_nonneg fun t ht => zpow_nonneg (hv t ht).1.le _
    show nu ι (r * (α : ℂ))⁻¹ * ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-lo t) ≤ 1
    rw [← h3]
    exact mul_le_mul_of_nonneg_right h2 h4

end UpperTheory.V.Z.Int
end

section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

theorem UpperTheory.V.Z.Int.slopeCsd :
    GlobalTheory.Cong.DescOffT → UpperTheory.V.Z.Int.SlopeOn .csd := by
  intro hD l _ ι E _ _ _ l' n hl' hn π χ hs w hw B hB
  obtain ⟨h1, h2, h3, rfl⟩ := hs
  obtain ⟨T, -, -, U, hU⟩ := hD E l' n hl' hn π ⟨h1, h2, h3, rfl⟩ ∅
  choose lam hlam using GlobalTheory.CompanionTheory.WeightExist.weightEx E n U hU.aut
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E n π w
  have hS := UpperTheory.V.Z.Int.coreU l ι E n hn U hU.aut lam hlam w hw σ B (hU.split w hw σ hσ)
    ((GlobalTheory.CompanionTheory.OnePart.hasSat_iff hσ B).1 hB)
  have e : (CG.mk π).infChar = fun φ => infOfWeight (lam φ) := funext fun φ => hU.inf φ _ (hlam φ)
  rw [e]
  exact hS
end
