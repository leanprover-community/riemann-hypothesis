module

public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.PeriodIntegrals.CapelliEig
public import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliEigenvalueKFiniteDiscreteSeriesCoeffStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentredCapelliOperatorFormsAgreeStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CoefRegG

theorem eigDec_of_isKFinCoefT : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  intro k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf
  have H : BranchingSupport.HypsG := CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have hsm : PI.KFinSmooth := H.1.2.2.1
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf
  obtain ⟨h1, h2⟩ := Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap H k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDG hgap hok hs
  refine ⟨h1, h2, fun y g hg => ?_⟩
  have hE := GlobalTheory.T.capelli_eigenvalue_kFinite_discreteSeries_coeff hsm CompanionTheory.D.DSIC.discrete_series_infinitesimal_character k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg
  rw [(GlobalTheory.T.centredCapelliOperator_forms_agree k r _ (y : ℂ) f).1, hE]
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

end GlobalTheory.CoefRegG

end
