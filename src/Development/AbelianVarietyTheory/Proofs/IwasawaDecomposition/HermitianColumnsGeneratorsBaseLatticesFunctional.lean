module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLatticeStepZeroAddConjGeneratorDualSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartBaseLatticeSupDualSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelFunctionalsIntermediateStepsTrueColumnStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClassesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroLevelTypePrimeOrientationFramesFunctionaStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC



theorem herm_rest_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → Formalism.L2.Herm.SymmetricCofactorCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricBaseCompatibility (I.rec7 l Z) H A ∧ Nonempty (Formalism.L2.Herm.SymmetricResidueFieldLevels (I.rec7 l Z) H A) ∧ ∃ X0 : Formalism.L2.Herm.SymmetricLevelZeroData (I.rec7 l Z) H A, ∀ u, (X0 u).piG = X.piG := by
  intro B X I hOk hP l Z H F A hS hH hT hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    have h1 := (hT.piU u).symm.trans (hS u).1.piU
    have h2 := (hT.piU (I.rec7 l Z).u₀).symm.trans (hS _).1.piU
    rw [h1, h2]
    exact hP.cof u
  · intro u pb hpb
    exact ⟨GlobalTheory.T.baseLatticeStepZero_add_conjGeneratorDual_selfDual I hOk hP l Z H F A hS hH hT u pb hpb, GlobalTheory.T.chart_base_lattice_sup_dual_selfDual I hOk hP l Z H F A hS hH hT u pb hpb⟩
  · refine ⟨fun u i h1 hm v β => ?_⟩
    by_cases h2 : i + 1 ≤ (I.rec7 l Z).R.m
    · exact (GlobalTheory.T.chartLevelFunctionals_intermediateSteps_trueColumns I hOk hP l Z H F A hS hH hT u i h1 h2 v β).some
    · have he : i = (I.rec7 l Z).R.m := by omega
      subst he
      exact (GlobalTheory.T.levelFunctional_chart_lastStep_classes I hOk hP l Z H F A hS hH hT u h1 v β).some
  · choose x hx using GlobalTheory.T.stepZeroLevel_typePrimeOrientation_frames_functionals I hOk hP l Z H F A hS hH hT hπ
    exact ⟨x, hx⟩

end GlobalTheory.Mem.Col2.TC
