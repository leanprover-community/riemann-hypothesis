module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.MainCotSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Mprime
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ChrInvNeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ExistsAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.FdAdjoinRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LemmaX
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ResidualBernoulliNonvanishing
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ConductorAtMapInjectiveCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PmExTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThFinal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LamEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.PhiAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ProModularRingExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.SgnEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section




section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.DescentVanishingReductions
open UpperTheory.V.Lit UpperTheory.V.W
theorem adjoint_lift_of_prints (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.UnramifiedInputs :=
  have hN := hH.litN
  ⟨⟨_root_.UpperTheory.V.W.locPrints_of_litN hN, hN.coh.pt, hN.coh.gf, hN.coh.ge, hN.coh.uo, hN.coh.gw⟩, hH, _root_.UpperTheory.V.HV.Core.modU_of_printsH hH, levEx, lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN),
    b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))⟩
theorem adjoint_lifting_of_cohomology (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Th.AdjointLiftingTheorem := _root_.UpperTheory.V.Th.adjoint_lifting_of_cohomology hH (_root_.UpperTheory.V.W.cohP_alt hH.litN)
theorem pmEx_of_printsH (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.PMExAlt := _root_.UpperTheory.Gal.projectedFormsSystemPart.pm_exists_of_unramified_adjoint_lifting (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH) (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH)
theorem countII_and_countIII_of_printsH_of_sp4In (hH : _root_.UpperTheory.V.Af.HypothesesH') (hK : ∃ CK : ℝ, LemmaK CK) (hS : _root_.UpperTheory.V.Aut.SymplecticFourImageDense) : CountII ∧ CountIII := by
  have hN := hH.litN
  obtain ⟨CK, hL⟩ := hK
  refine _root_.UpperTheory.V.Th.sp4Main_alt hS (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH).coh Alg.M.main_holds Alg.M.mprime_holds Alg.lemmaP (_root_.UpperTheory.GalN.V.numberSp4_n_alt hH.toClassicalTheorems)
    (_root_.UpperTheory.V.Th.rigSp4_alt (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH) (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH)) (X.corX X.lemmaX X.residual_bernoulli_nonvanishing) fun Ω _ _ _ l _ => ⟨?_, fun c => ?_⟩
  · exact X.soBar CK hL (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK ℚ Ω l
  · exact X.soFin CK hL (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK ℚ Ω l c.O
end UpperTheory.V.HV.DescentVanishingReductions
end
