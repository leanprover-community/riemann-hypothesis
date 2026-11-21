import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Hypotheses4N
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LineOfNotIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Sd

section Real

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))







end Real



section Local

variable {l : ℕ} [Fact l.Prime]

private theorem norm_of_cong {a : (Qbar l)ˣ} (h : Cong a 1) : ‖(a : Qbar l)‖ = 1 := by
  have := IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := (a : Qbar l)) (y := -1)
    (by rw [← sub_eq_add_neg, norm_neg, norm_one]; exact lt_of_lt_of_le h (le_max_right _ _))
  rw [this, norm_neg, norm_one]

variable (l) in
private def U1 : Subgroup (Qbar l)ˣ where
  carrier := {a | Cong a 1}
  one_mem' := by simp [Cong]
  mul_mem' {a b} ha hb := by
    have h := IsUltrametricDist.norm_add_le_max (((a : Qbar l) - 1) * b) ((b : Qbar l) - 1)
    rw [norm_mul, norm_of_cong hb, mul_one, show ((a : Qbar l) - 1) * b + (b - 1) = a * b - 1 by ring] at h
    exact h.trans_lt (max_lt ha hb)
  inv_mem' {a} ha := by
    have h : ‖((a⁻¹ : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, norm_of_cong ha, inv_one]
    change ‖((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1‖ < 1
    rw [show ((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = (a⁻¹ : (Qbar l)ˣ) * (1 - a) by rw [mul_sub, Units.inv_mul, mul_one],
      norm_mul, h, one_mul, norm_sub_rev]
    exact ha


variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]



variable [NumberField F] [IsAlgClosure F Ω]





end Local

