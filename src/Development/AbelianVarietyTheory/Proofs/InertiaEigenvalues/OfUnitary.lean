import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOneUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot

section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.UnitaryTwist

def normRpow (r : ℝ) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 z.ne_zero) r).ne')
  map_one' := by ext; simp
  map_mul' z w := by
    ext
    simp [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

theorem normRpow_val (r : ℝ) (z : ℂˣ) : ((normRpow r z : ℂˣ) : ℂ) = ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ) := rfl

theorem continuous_normRpow (r : ℝ) : Continuous (normRpow r) := by
  have hn : Continuous fun z : ℂˣ => ‖(z : ℂ)‖ := Units.continuous_val.norm
  have hp : Continuous fun z : ℂˣ => ‖(z : ℂ)‖ ^ r :=
    hn.rpow_const fun z => Or.inl (norm_pos_iff.2 z.ne_zero).ne'
  have hc : Continuous fun z : ℂˣ => ((‖(z : ℂ)‖ ^ r : ℝ) : ℂ) := Complex.continuous_ofReal.comp hp
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  have : (fun z : ℂˣ => (((normRpow r z)⁻¹ : ℂˣ) : ℂ)) = fun z : ℂˣ => (((‖(z : ℂ)‖ ^ r : ℝ) : ℂ))⁻¹ := by
    funext z; rw [Units.val_inv_eq_inv_val, normRpow_val]
  rw [this]
  exact hc.inv₀ fun z => Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 z.ne_zero) r).ne'

def normTwist {E : Type} [Field E] [NumberField E] (ω : HChar E) (r : ℝ) : HChar E :=
  ⟨(normRpow r).comp ω.1, (continuous_normRpow r).comp ω.2.1, fun k => by
    rw [MonoidHom.comp_apply, ω.2.2 k, map_one]⟩


end GlobalTheory.UnitaryTwist
end
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory



end GlobalTheory
end

section
open GlobalTheory.Published

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspMultOne


end GlobalTheory.CuspMultOne

end
end
