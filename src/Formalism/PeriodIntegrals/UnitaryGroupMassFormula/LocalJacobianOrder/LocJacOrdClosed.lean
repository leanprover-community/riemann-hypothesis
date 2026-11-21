import Mathlib
import Formalism.PeriodIntegrals.LocJacOrd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.SdNormHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale

section
noncomputable section

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def Obox (ι : Type) : Set (ι → Fv F v ⊗[F] E) := Set.univ.pi fun _ => OEv (E := E) v

def SdNormO : Prop :=
  (∀ (ι : Type) [Fintype ι] [Nonempty ι], sdE (E := E) ψ v ι = 0) ∨
  ∃ m : ℝ, 0 < m ∧ ∀ (ι : Type) [Fintype ι], (sdE (E := E) ψ v ι).IsAddHaarMeasure ∧
    (sdE (E := E) ψ v ι (Obox (E := E) v ι)).toReal = m ^ Fintype.card ι

def VolZZO : Prop :=
  ∀ (r : ℕ) (m : ℝ), Module.finrank F E = 2 →
    ∀ μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ ((r + 1) * (r + 1)) →
      (μ (ZZOrd (E := E) v r)).toReal =
        m ^ ((r + 1) * (r + 1)) *
          ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹

def VolUO : Prop :=
  ∀ (r : ℕ) (m : ℝ), Module.finrank F E = 2 →
    ∀ μ : Measure (UIdx r → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ Fintype.card (UIdx r) →
      ((μ.prod μ) (localVolumeOrdinary (E := E) v r)).toReal =
        ∏ q : UIdx r, (m ^ 2 * (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)

def VolPO : Prop :=
  ∀ (r : ℕ) (m : ℝ), Module.finrank F E = 2 →
    ∀ μ : Measure (Unit → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v Unit)).toReal = m →
      ∀ l : Fin (r + 1),
        (μ ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPOrd (E := E) v r l)).toReal =
          m * (absV v (alp v r l) ^ 4)⁻¹

def ArithO : Prop :=
  ∀ (typed : Prop) (g r : ℕ) (m : ℝ), ¬ typed →
    m ^ ((r + 1) * (r + 1)) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹) *
        jacS v typed g r =
      (∏ q : UIdx r, (m ^ 2 * (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)) *
        ∏ l : Fin (r + 1), (m * (absV v (alp v r l) ^ 4)⁻¹)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))


end PI.LocJacOrd.W
end
end

section
noncomputable section

namespace PI.LocJacOrd.W.Ar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical

section AbsV

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem absNorm_ne_zero : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast h

theorem absV_mul (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  by_cases hx : x = 0
  · simp [absV, hx]
  by_cases hy : y = 0
  · simp [absV, hy]
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  have hu : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, WithZero.coe_mul, map_mul]
  simp only [absV, dif_neg hx', dif_neg hy', dif_neg hxy', hu, toAdd_mul,
    zpow_add₀ (absNorm_ne_zero v)]

theorem absV_zero : absV v (0 : Fv F v) = 0 := by simp [absV]

theorem absV_one : absV v (1 : Fv F v) = 1 := by
  have h1 : Valued.v (1 : Fv F v) ≠ 0 := by simp
  have hu : WithZero.unzero h1 = 1 := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, map_one, WithZero.coe_one]
  simp only [absV, dif_neg h1, hu, toAdd_one, zpow_zero]

def absVHom : Fv F v →*₀ ℝ where
  toFun := absV v
  map_zero' := absV_zero v
  map_one' := absV_one v
  map_mul' := absV_mul v



theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem alp_ne_zero (r : ℕ) (i : Fin (r + 1)) : alp v r i ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

end AbsV

section Real

theorem jac_count (r : ℕ) (b : Fin (r + 1) → ℝ) :
    ∏ l : Fin r, ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), b i =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then b p.1 else 1) := by
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_succ]
  have h0 : ¬ i < (0 : Fin (r + 1)) := by simp
  rw [if_neg h0, one_mul]
  refine Finset.prod_congr rfl fun l _ => ?_
  have : (i < l.succ) ↔ ((i : ℕ) ≤ (l : ℕ)) := by
    rw [Fin.lt_def, Fin.val_succ]; omega
  simp only [this]

theorem arith_real (r : ℕ) (m : ℝ) (a : Fin (r + 1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    m ^ ((r + 1) * (r + 1)) * (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((a i * a j) ^ 2)⁻¹) *
        ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
          a i ^ 2) ^ 2) ^ 2 =
      (∏ q : UIdx r, (m ^ 2 * (a q.1.1 / a q.1.2) ^ 4)) * ∏ l : Fin (r + 1), (m * (a l ^ 4)⁻¹) := by
  have hm : m ^ ((r + 1) * (r + 1)) = ∏ _p : Fin (r + 1) × Fin (r + 1), m := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have hP : ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((a i * a j) ^ 2)⁻¹ =
      ∏ p : Fin (r + 1) × Fin (r + 1), ((a p.1 * a p.2) ^ 2)⁻¹ :=
    (Fintype.prod_prod_type (fun p : Fin (r + 1) × Fin (r + 1) => ((a p.1 * a p.2) ^ 2)⁻¹)).symm
  have hJ : ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
      a i ^ 2) ^ 2) ^ 2 =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then a p.1 ^ 8 else 1) := by
    rw [← jac_count r (fun i => a i ^ 8)]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← Finset.prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  have hU : ∏ q : UIdx r, (m ^ 2 * (a q.1.1 / a q.1.2) ^ 4) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m ^ 2 * (a p.1 / a p.2) ^ 4 else 1) := by
    rw [← Finset.prod_filter]
    exact (Finset.prod_subtype _ (fun p : Fin (r + 1) × Fin (r + 1) => by simp)
      (fun p : Fin (r + 1) × Fin (r + 1) => m ^ 2 * (a p.1 / a p.2) ^ 4)).symm
  have hD : ∏ l : Fin (r + 1), (m * (a l ^ 4)⁻¹) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 = p.2 then m * (a p.1 ^ 4)⁻¹ else 1) := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_ite_eq]
    simp
  have hL : ∏ p : Fin (r + 1) × Fin (r + 1), (if p.2 < p.1 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1) := by
    refine Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun p => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm (a p.2)]
  have hsplit : ∏ p : Fin (r + 1) × Fin (r + 1), (m * ((a p.1 * a p.2) ^ 2)⁻¹) =
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.2 < p.1 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 = p.2 then m * (a p.1 ^ 4)⁻¹ else 1)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · rw [if_neg (by simp [h]), if_neg (by simp [h]), if_pos h, h]
      ring
    · simp [h, h.ne', not_lt.2 h.le]
  have key : (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m * ((a p.1 * a p.2) ^ 2)⁻¹ else 1)) *
      (∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then a p.1 ^ 8 else 1)) =
      ∏ p : Fin (r + 1) × Fin (r + 1), (if p.1 < p.2 then m ^ 2 * (a p.1 / a p.2) ^ 4 else 1) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    split_ifs with h
    · have h1 := ha p.1
      have h2 := ha p.2
      field_simp
    · simp
  rw [hm, hP, ← Finset.prod_mul_distrib, hsplit, hL, hJ, hU, hD, ← key]
  ring

end Real

end PI.LocJacOrd.W.Ar

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd


end PI.LocJacOrd.W
end
end

section
noncomputable section

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical

def BoxScale : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (ι : Type) [Fintype ι], Module.finrank F E = 2 →
    ∀ (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure] (x : ι → Fv F v), (∀ i, x i ≠ 0) →
      (μ (Set.univ.pi fun i => {c | sc (E := E) v (x i) * c ∈ OEv (E := E) v})).toReal =
        (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (x i) ^ 2)⁻¹

def AbsMul : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
    (∀ x y : Fv F v, absV v (x * y) = absV v x * absV v y) ∧ absV v 1 = 1 ∧
      ∀ x : Fv F v, x ≠ 0 → 0 < absV v x

section Top

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem secondCountable_Fv : SecondCountableTopology (Fv F v) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
  exact UniformSpace.secondCountable_of_separable (Fv F v)

theorem locallyCompact_Fv : LocallyCompactSpace (Fv F v) :=
  (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))

end Top


section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem alp_ne_zero (r : ℕ) (a : Fin (r + 1)) : alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

theorem absV_inv (hA : AbsMul) (x : Fv F v) (hx : x ≠ 0) : absV v x⁻¹ = (absV v x)⁻¹ := by
  obtain ⟨hm, h1, hp⟩ := hA v
  have : absV v x⁻¹ * absV v x = 1 := by rw [← hm, inv_mul_cancel₀ hx, h1]
  exact eq_inv_of_mul_eq_one_left this

theorem absV_pow (hA : AbsMul) (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  obtain ⟨hm, h1, hp⟩ := hA v
  induction n with
  | zero => simp [h1]
  | succ n ih => rw [pow_succ, hm, ih, pow_succ]




end

end PI.LocJacOrd.W
end
end

section
noncomputable section

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd


end PI.LocJacOrd.W
end
end

section
noncomputable section

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain



end PI.LocJacOrd.W
end
end
