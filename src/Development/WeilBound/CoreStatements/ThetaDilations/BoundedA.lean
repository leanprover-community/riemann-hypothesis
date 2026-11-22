module

public import Development.WeilBound.CoreStatements.ThetaDilations.OrbitAdelic
public import Development.WeilBound.CoreStatements.ThetaDilations.ProdRho
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ReductionToSiegelDomainStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionModularityStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionAutomorphyStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionCuspExpansionStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBoundStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCountStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormulaStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummableStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealQuadraticFormLemmaStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariantStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionWhittakerEquivariantStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuadraticLevelSetDensityStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeFundamentalDomainVolumeStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOperatorIntegralInvarianceStatement
import CompanionTheory.AutomorphicTheory.ThetaDilations.BoundedA

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem sb_indL {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] {a : ℕ} (ha : 0 < a) :
    SB (indL (F := F) (ι := ι) a) := by
  have := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.1
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha.ne'
  have e : indL (F := F) (ι := ι) a = ind 0 (LN F ι 1) ∘ Homeomorph.smul (uA (Units.mk0 (a : F) ha')) := by
    funext u
    have h : (∀ i, (a : A F) * u i ∈ Oh F) ↔ uA (Units.mk0 (a : F) ha') • u - 0 ∈ LN F ι 1 := by
      rw [sub_zero]
      refine forall_congr' fun i => ?_
      have : (uA (Units.mk0 (a : F) ha') • u) i = (a : A F) * u i := by simp [uA, Units.smul_def]
      simp [this]
    by_cases hu : ∀ i, (a : A F) * u i ∈ Oh F
    · exact (Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hu _).trans
        (ind_of_mem (h.1 hu)).symm
    · exact (Set.indicator_of_notMem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hu _).trans
        (ind_of_not (mt h.2 hu)).symm
  exact e ▸ sb_homeo (sb_ind 0 (co_LN one_pos)) _

theorem bounded_a : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∃ C : ℝ, ∀ a : ℕ, 0 < a → ∀ x : InfinitePlace F → ℝ, SB (indL (F := F) (ι := ι) a) ∧ ‖((∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) - eis ψ lf B ρ P (indL a) (fun w => (x w : ℂ) + Complex.I))‖ ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) :=
  _root_.CompanionTheory.PlacePermOperatorBicommutantSpan.bounded_a

end PositivityTheory.PlacePermOperatorBicommutantSpan
