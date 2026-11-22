module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueJointTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.DetDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperatorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLinesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLinesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledFockVacuumEqSmulVacuumMulConjStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralInvariantFormDiagonalLagrangianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzIntegralMulStarNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceSplittingConstantHalfRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceSplittingConstantEqDoubledSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

end Tensor

theorem i_locfin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := GlobalTheory.T.isLocallyFinite_piTensorSumOfFactorOperators

theorem i_expact : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := GlobalTheory.T.weakExponential_action_on_fockVectors

theorem i_actslaws : GlobalTheory.RealLift.ActsLaws := GlobalTheory.T.archActionReadings_compatible

theorem i_derex : GlobalTheory.RealLift.DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist

theorem i_fockex : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives

theorem i_vacline : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives

theorem i_polrange : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws

theorem i_genex : GlobalTheory.RealLift.GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist

theorem i_lineex : GlobalTheory.RealLift.LineEx := GlobalTheory.T.unitaryLieElements_generate_oneParamLines

theorem i_kline : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines

theorem i_frameex : GlobalTheory.RealLift.FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists

section Helpers

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq, MultilinearMap.map_update_zero]

end Helpers

section Exp

variable {V V' Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup Z] [Module ℂ Z]

end Exp

theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Side

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

include Φ in
theorem pol_eq (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ T, f = Φ T := by
  rw [← hrange] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨T, rfl⟩

end Side

section SideW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

end SideW

end GlobalTheory.RealLift.Main
