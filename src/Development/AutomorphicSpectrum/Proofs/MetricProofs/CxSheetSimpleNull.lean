module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimpleOfCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open MeasureTheory CxInt CxComp

theorem cxSheetSimpleNull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) ∧
      ¬ cxSimple (conePts Q) Ψ w} = 0 := by
  intro K _ ι _ Q e Ψ hQ hΨ
  obtain ⟨d, hbd, hnull⟩ := cxGenericCount hQ Ψ hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (cxSimple_of_count hbd hgood.1 hgood.2 hw)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
