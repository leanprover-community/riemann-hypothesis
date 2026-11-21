import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.SdNormHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitShear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical

section Count

theorem sum_uidx (r : ℕ) (g : Fin (r + 1) × Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, g q.1 = ∑ i : Fin (r + 1), ∑ j : Fin (r + 1), if i < j then g (i, j) else 0 := by
  rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) (fun p => g p)).symm

theorem card_Ioi' (r : ℕ) (i : Fin (r + 1)) :
    ((Finset.univ.filter fun j : Fin (r + 1) => i < j).card : ℝ) = (r : ℝ) - (i : ℕ) := by
  have h : (Finset.univ.filter fun j : Fin (r + 1) => i < j) = Finset.Ioi i := by ext j; simp
  rw [h, Fin.card_Ioi]
  have := i.is_le
  rw [show r + 1 - 1 - (i : ℕ) = r - (i : ℕ) by omega, Nat.cast_sub this]

theorem card_Iio' (r : ℕ) (j : Fin (r + 1)) :
    ((Finset.univ.filter fun i : Fin (r + 1) => i < j).card : ℝ) = ((j : ℕ) : ℝ) := by
  have h : (Finset.univ.filter fun i : Fin (r + 1) => i < j) = Finset.Iio j := by ext i; simp
  rw [h, Fin.card_Iio]

theorem card_le' (r : ℕ) (i : Fin (r + 1)) :
    ((Finset.univ.filter fun l : Fin r => (i : ℕ) ≤ (l : ℕ)).card : ℝ) = (r : ℝ) - (i : ℕ) := by
  have h : (Finset.univ.filter fun l : Fin r => (i : ℕ) ≤ (l : ℕ)).map Fin.valEmbedding =
      Finset.Ico (i : ℕ) r := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨hl, l.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨n, h2⟩, h1, rfl⟩
  rw [← Finset.card_map, h, Nat.card_Ico, Nat.cast_sub i.is_le]

theorem sum_fst (r : ℕ) (f : Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, f q.1.1 = ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * f i := by
  rw [sum_uidx r (fun p => f p.1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, card_Ioi']

theorem sum_snd (r : ℕ) (f : Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, f q.1.2 = ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * f j := by
  rw [sum_uidx r (fun p => f p.2), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, card_Iio']

theorem sum_jac (r : ℕ) (a : Fin (r + 1) → ℝ) :
    ∑ l : Fin r, ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), a i =
      ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_le']

theorem gauss (r : ℕ) : 2 * ∑ i : Fin (r + 1), ((i : ℕ) : ℝ) = (r : ℝ) * (r + 1) := by
  have h := Finset.sum_range_id_mul_two (r + 1)
  rw [Fin.sum_univ_eq_sum_range (fun n => (n : ℝ)) (r + 1)]
  have h2 : ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) * 2 = ((r + 1) * (r + 1 - 1) : ℕ) := by
    exact_mod_cast h
  push_cast at h2
  linarith

theorem sum_l_succ (r : ℕ) : ∑ l : Fin r, (((l : ℕ) : ℝ) + 1) = ∑ i : Fin (r + 1), ((i : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun n => (n : ℝ) + 1) r,
    Fin.sum_univ_eq_sum_range (fun n => (n : ℝ)) (r + 1), Finset.sum_range_succ']
  push_cast
  simp

end Count

section Real

open Real

variable (r : ℕ)

theorem exp_product_square_inv (a : Fin (r + 1) → ℝ) :
    ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((exp (a i) * exp (a j)) ^ 2)⁻¹ =
      exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  simp only [Finset.sum_neg_distrib, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem eJ (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ l : Fin r, (((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
        exp (a i) ^ 2) * (exp γ)⁻¹ ^ ((l : ℕ) + 1)) ^ 2) ^ 2 =
      exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1)) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_jac]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring_nf
  try simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [show ∑ x : Fin r, ((x : ℕ) : ℝ) * γ * 4 = ∑ x : Fin r, γ * ((x : ℕ) : ℝ) * 4 from
    Finset.sum_congr rfl (fun _ _ => by ring)]
  ring

theorem eU (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ q : UIdx r, (exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) =
      exp (2 * γ * (Fintype.card (UIdx r) : ℝ) + 4 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_sum]
  congr 1
  rw [← sum_fst r a, ← sum_snd r a]
  simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem eL (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ l : Fin (r + 1), (exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) =
      exp (3 * ((r : ℝ) + 1) * γ - 4 * ∑ l, a l) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem card_uidx : 2 * (Fintype.card (UIdx r) : ℝ) = (r : ℝ) * (r + 1) := by
  have h := sum_fst r (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [h, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := gauss r
  push_cast
  linarith

end Real

section Final

open Real

theorem arith_real (r : ℕ) (A : Fin (r + 1) → ℝ) (hA : ∀ i, 0 < A i) (G m : ℝ) (hG : 0 < G) :
    m ^ ((r + 1) * (r + 1)) * G ^ (3 * ((r + 1) * (r + 1))) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((A i * A j) ^ 2)⁻¹) *
        ∏ l : Fin r, (((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
          A i ^ 2) * G⁻¹ ^ ((l : ℕ) + 1)) ^ 2) ^ 2 =
      (∏ q : UIdx r, (m ^ 2 * G ^ 2 * (A q.1.1 / A q.1.2) ^ 4)) *
        ∏ l : Fin (r + 1), (m * G ^ 3 * (A l ^ 4)⁻¹) := by
  obtain ⟨γ, rfl⟩ : ∃ γ, G = exp γ := ⟨log G, (exp_log hG).symm⟩
  obtain ⟨a, rfl⟩ : ∃ a : Fin (r + 1) → ℝ, A = fun i => exp (a i) :=
    ⟨fun i => log (A i), funext fun i => (exp_log (hA i)).symm⟩
  have hU : ∏ q : UIdx r, (m ^ 2 * exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) =
      (m ^ 2) ^ Fintype.card (UIdx r) * ∏ q : UIdx r, (exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) := by
    rw [Finset.prod_congr rfl (fun q _ => mul_assoc _ _ _), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hL : ∏ l : Fin (r + 1), (m * exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) =
      m ^ (r + 1) * ∏ l : Fin (r + 1), (exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) := by
    rw [Finset.prod_congr rfl (fun q _ => mul_assoc _ _ _), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  simp only at hU hL ⊢
  rw [hU, hL, exp_product_square_inv, eJ, eU, eL]
  have hK := card_uidx r
  have hN : 2 * Fintype.card (UIdx r) + (r + 1) = (r + 1) * (r + 1) := by
    have : ((2 * Fintype.card (UIdx r) + (r + 1) : ℕ) : ℝ) = (((r + 1) * (r + 1) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hm : (m ^ 2) ^ Fintype.card (UIdx r) * m ^ (r + 1) = m ^ ((r + 1) * (r + 1)) := by
    rw [← pow_mul, ← pow_add, hN]
  have hS := gauss r
  have hS' := sum_l_succ r
  have h1 : ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i + ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j =
      (r : ℝ) * ∑ i, a i := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hE : exp γ ^ (3 * ((r + 1) * (r + 1))) *
      exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) *
      exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i - 4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1)) =
      exp (2 * γ * (Fintype.card (UIdx r) : ℝ) + 4 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j) *
      exp (3 * ((r : ℝ) + 1) * γ - 4 * ∑ l, a l) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    linear_combination (-4 * γ) * hS' + (-2 * γ) * hS + (-γ) * hK + 4 * h1
  rw [← hm]
  calc (m ^ 2) ^ Fintype.card (UIdx r) * m ^ (r + 1) * exp γ ^ (3 * ((r + 1) * (r + 1))) *
        exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) *
        exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i - 4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1))
      = (m ^ 2) ^ Fintype.card (UIdx r) * m ^ (r + 1) * (exp γ ^ (3 * ((r + 1) * (r + 1))) *
        exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) *
        exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i - 4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1))) := by
        ring
    _ = _ := by rw [hE]; ring

end Final

section AbsProd

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def absVHom : Fv F v →* ℝ where
  toFun := absV v
  map_one' := absV_one v
  map_mul' := absV_mul v

theorem absV_prod {ι : Type} (s : Finset ι) (f : ι → Fv F v) :
    absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) :=
  map_prod (absVHom v) f s

theorem quadraticDifferenceArith : Arith (F := F) v := by
  intro typed g r m ht hg
  unfold jacS
  simp only [if_pos ht, absV_mul, absV_prod, absV_pow, absV_inv]
  exact arith_real r _ (fun i => absV_pos v (alp_ne_zero v r i)) _ m
    (absV_pos v (natCast_ne_zero v hg))

end AbsProd

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))


end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

def shearU (ι : Type) :
    ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) ≃ₜ+ ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' x y := Prod.ext rfl (by
    show x.1 + y.1 - (x.2 + y.2) = (x.1 - x.2) + (y.1 - y.2)
    abel)
  continuous_toFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)


end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem unit_forall {P : Unit → Prop} : (∀ i, P i) ↔ P () := ⟨fun h => h (), fun h _ => h⟩

theorem parabolic_volume : VolPP σ v := by
  intro g r T T' m hS hg hT μ hμ hm l
  obtain ⟨D⟩ := exists_SD hS
  have hp0 : ∀ s t, D.p 0 (D.pt s t) = s := fun s t => (D.p_pt s t).1
  have hp1 : ∀ s t, D.p 1 (D.pt s t) = t := fun s t => (D.p_pt s t).2
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  have hsh : ∀ X : Set (Unit → Fv F v ⊗[F] E), μ ((D.shear id) ⁻¹' X) = μ X :=
    haar_shear μ (D.shear id) (Obox (E := E) v Unit) (obox_compact Unit) (obox_open Unit)
      (obox_nonempty Unit) (D.shear_box id)
  by_cases hl : (l : ℕ) < r
  · have ha : alp v r l ^ 2 ≠ 0 := pow_ne_zero _ (alp_ne_zero v r l)
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' (Set.univ.pi fun _ : Unit =>
          {c | D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈
            OEv (E := E) v}) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_pos hl, unit_forall]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul, D.shear_first_coordinate, D.shear_second_coordinate]
      simp only [map_add, (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        refine ⟨⟨?_, h2⟩, h3, ?_⟩
        · have e1 : alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 0 (c ()) =
              (g : Fv F v) * (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()))) -
                alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 1 (c ()) := by
            field_simp <;> ring
          rw [e1]
          exact sub_mem (mul_mem hgO h3) h2
        · rwa [add_comm (D.p 1 (c ()))]
    have hu : ∀ _ : Unit, IsUnit (D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹)) :=
      fun _ => D.isUnit_pt (mul_ne_zero ha (pow_ne_zero _ (inv_ne_zero hg0))) (mul_ne_zero ha (inv_ne_zero hg0))
    rw [hset, hsh, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt]
    rw [absV_mul, absV_mul, absV_mul, absV_pow, absV_pow, absV_inv]
    have hA := absV_pos v (alp_ne_zero v r l)
    have hG := absV_pos v hg0
    field_simp
  · have hlr : alp v r l = 1 := by unfold alp; rw [if_neg hl]
    obtain ⟨k, hk⟩ := hT
    have hk' : ((T : Fv F v) - (T' : Fv F v)) = (g : Fv F v) * (k : Fv F v) := by
      have := congrArg (Int.cast : ℤ → Fv F v) hk
      push_cast at this
      exact this
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' ((fun w => w + fun _ : Unit => D.pt ((T : Fv F v) + T') (T : Fv F v)) ⁻¹'
          (Set.univ.pi fun _ : Unit =>
            {c | D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹ * c ∈ OEv (E := E) v})) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_neg hl, unit_forall, Pi.add_apply]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul]
      simp only [map_add, D.shear_first_coordinate, D.shear_second_coordinate, hp0, hp1, map_natCast, (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        refine ⟨?_, h2⟩
        have e1 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') := by ring
        rw [e1]; exact h3
      · rintro ⟨h3, h2⟩
        have e0 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
        refine ⟨⟨?_, h2⟩, by rw [e0]; exact h3, ?_⟩
        · have e1 : (g : Fv F v)⁻¹ * (D.p 0 (c ()) + T) =
              (g : Fv F v) * (((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T'))) -
                (g : Fv F v)⁻¹ * (D.p 1 (c ()) + T) + (g : Fv F v)⁻¹ * ((T : Fv F v) - T') := by
            field_simp <;> ring
          have e2 : (g : Fv F v)⁻¹ * ((T : Fv F v) - T') = (k : Fv F v) := by
            rw [hk']; field_simp
          rw [e1, e2]
          exact add_mem (sub_mem (mul_mem hgO h3) h2) (intCast_mem _ k)
        · have e2 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 1 (c ()) + D.p 0 (c ()) + T + T') =
              ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
          rw [e2]; exact h3
    have hu : ∀ _ : Unit, IsUnit (D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹) :=
      fun _ => D.isUnit_pt (pow_ne_zero _ (inv_ne_zero hg0)) (inv_ne_zero hg0)
    rw [hset, hsh, measure_preimage_add_right, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt, hlr, absV_one]
    rw [absV_mul, absV_pow, absV_inv]
    have hG := absV_pos v hg0
    field_simp

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain


end PI.UnitaryGroupMassFormula.LocJacTyp
end
end
