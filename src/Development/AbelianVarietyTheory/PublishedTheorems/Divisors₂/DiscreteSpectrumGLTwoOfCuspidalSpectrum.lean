module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterPrescribedCentre

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.DiscChar

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {ω χ : HChar E}
  {V : Submodule ℂ (Sm E a)}

abbrev expId (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : ℝ) : Neutral.B1.Ideles E :=
  infId E (expU fun _ : InfinitePlace E => (t : ℂ))

theorem isSqInt_of_bounded {f : GA E a → ℂ} (h : ∀ t g, f (splitCentre E a t * g) = f g) {C : ℝ}
    (hC : ∀ g, ‖f g‖ ≤ C) : IsSqInt f := by
  have hd := isFundamentalDomain_stdDom (latticeGL E a) (Measure.haar : Measure (GA E a))
  have hf := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a Measure.haar
  refine ⟨h, Measure.haar, _, inferInstance, hd, ?_⟩
  refine (lintegral_mono (g := fun _ => ENNReal.ofReal C ^ 2) fun g => ?_).trans_lt ?_
  · exact pow_le_pow_left' ((ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hC g))) 2
  · rw [setLIntegral_const, ← quotMeasure_univ hd]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)

section Local

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.DiscChar

namespace GlobalTheory.Published

open GlobalTheory.DiscChar

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

end GlobalTheory.Published

end
