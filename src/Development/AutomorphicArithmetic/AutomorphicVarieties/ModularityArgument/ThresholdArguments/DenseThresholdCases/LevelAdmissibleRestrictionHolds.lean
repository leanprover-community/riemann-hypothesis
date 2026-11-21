import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnderCPl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlAllOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
namespace UpperTheory.V.Z.Win.A4
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
end
theorem safeUP'_alt (_P : _root_.UpperTheory.V.Af.Hypotheses') {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n M : ℕ}
    {m : Fin n → ℤ} {ι : Qbar l ≃+* ℂ} {r : G ℚ Ω →* GL (Fin n) (Qbar l)} (hi : IsIrr r) (hl : Level l M m r) (ha : IsAutQA ι r)
    (h : SafeRA l M m r) : SafePA l M m r :=
  h.imp_left fun ⟨h1, h2⟩ => ⟨h1, potQ flagLaws splitIrr Ω l ι n r hl.cont hi ha h2⟩
end UpperTheory.V.Z.Win.A4
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr
open UpperTheory.GalN.V
theorem UpperTheory.V.Z.Win.A4.admissible_restriction_level_n_of_printed_results : _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.AdmResNAlt := by
  intro hP K _ _ _ hK n hn m wt hm M hM l _ hl Ω _ _ _ _ _ _ ι r hr hirr
  have hC := Lev.LevelF.of_level hr.level
  have hF := Lev.levelFRes ℚ K Ω l n M m r hC
  obtain ⟨⟨P, hreg, hA⟩, hW⟩ := hr.aut hC.cont K hK hirr
  obtain ⟨θ, hθ, hd⟩ := hr.dual
  obtain ⟨χ, μ, hpol, -, -⟩ := _root_.UpperTheory.V.Z.Bc.polarization_k_of_printed_results hP K hK n (by omega) l Ω ι r wt θ P hθ hd hA
  exact ⟨hirr, ⟨P, hreg, ⟨χ, hpol⟩, hA⟩, hW, hF, _root_.UpperTheory.V.Z.Win.A4.safeRes' K (_root_.UpperTheory.V.Z.Win.A4.safeUP'_alt hP hr.irr hr.level hr.aut hr.safe)⟩
end
end
end
