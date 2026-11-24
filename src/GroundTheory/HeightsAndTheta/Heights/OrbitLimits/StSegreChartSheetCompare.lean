module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm oneLine isSmoothHerm_oneLine)
open ComplexSets Matrix

def SegreChartSheetCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι), (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ J ∈ segreChartComponents P σ i, ∀ (A : Matrix (Fin e) (Fin m) ℂ) (x : Fin m → ℂ)
        (s : (Fin e → ℂ) → Fin m → ℂ), x ∈ zeroSet J → IsSheetAt J A x s →
          |ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i L k ∘ s) (A *ᵥ x)| ≤
            C * |ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x)|

end GroundTheory.Heights₂.Heights
