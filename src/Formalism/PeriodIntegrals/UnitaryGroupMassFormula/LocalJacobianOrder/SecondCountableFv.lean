import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianOrder.AbsVNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop

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
