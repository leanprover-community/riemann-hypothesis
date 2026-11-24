module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def MaDensLeibniz.Statement : Prop :=
  ∀ (D : ℕ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (f g : (Fin (D + 1) → ℂ) → ℝ) (z : Fin (D + 1) → ℂ),
    ContDiffAt ℝ 2 f z → ContDiffAt ℝ 2 g z →
      maDens (Fin.cons (fun y => f y * g y) φ) z =
          f z * maDens (Fin.cons g φ) z + g z * maDens (Fin.cons f φ) z + gradDens φ f g z +
            gradDens φ g f z ∧
        maDens (Fin.cons (fun y => f y ^ 2 / 2) φ) z =
          f z * maDens (Fin.cons f φ) z + gradDens φ f f z

def EnergyDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (v : (Fin (d + 1) → ℂ) → ℝ),
    AnalyticAt ℂ s y → 0 ≤ gradDens (fun _ : Fin d => euclPot ∘ s) v v y

def GradDensSheetBound.Statement : Prop :=
  ∀ (n d : ℕ) (φ : Fin d → (Fin n → ℂ) → ℝ) (U K : Set (Fin n → ℂ)),
    IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ)
        (v w : (Fin (d + 1) → ℂ) → ℝ), AnalyticAt ℂ s y → s y ∈ K →
          |gradDens (fun i => φ i ∘ s) v w y| ≤
            C * Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) v v y) *
              Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) w w y)

end

end GroundTheory.Heights₂.Heights
