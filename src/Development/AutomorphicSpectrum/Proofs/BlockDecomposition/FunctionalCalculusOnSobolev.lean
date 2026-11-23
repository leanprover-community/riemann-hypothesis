module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

theorem phi_keeps_sections : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ) (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T),
      LgFacts → Unimod → RCalc → SobG → CalcSteps →
      (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) →
      ∀ (h : C₀(ℝ, ℂ)) (f : Mat n → E.V), Sob μ f → IsSec E f →
        ∃ f', Sob μ f' ∧ IsSec E f' ∧ cls μ f' = F.Φ h (cls μ f) := by
  intro n _ _ μ _ E
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hL hU hR hSG hCS hΩ h f hf hs
  obtain ⟨-, -, -, -, hC, hO, hCp, -, hP, hCT, -, hFr, hOF, hI, hD⟩ := hCS
  have hrep : ∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x :=
    (hCT n μ E.V hL hU hR hSG hP hFr hC hO hCp hOF hI hD).1
  obtain ⟨f', hf', hcl, -⟩ := GlobalTheory.CompanionTheory.WaveFc.Asm.pres hC hO hL hU hR hSG hP F hrep hΩ h hf
  exact ⟨f', hf', GlobalTheory.CompanionTheory.WaveFc.Asm.sec_pres E hC hO hL hU hR F hrep hΩ h hf hs hf' hcl, hcl⟩

end GlobalTheory.CompanionTheory.FcSmooth
