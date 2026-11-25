module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSchwartzBruhatIndicatorLocalLatticeCompletion

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isSchwartzBruhat_indicator_localLatticeCompletion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ v : HeightOneSpectrum (𝓞 F), IsSB ({X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ)) := by
  first | exact @GlobalTheory.LatticeIndicator.isSB_indicator_latLoc
