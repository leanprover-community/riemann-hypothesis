module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyProjectionMass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section


open Classical in
def LocalGraphProjectionMass.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))), I₀.card = d →
    (∀ z ∈ S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω) →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (S ∩ B) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s),
          (⨆ x : EuclideanSpace ℂ (Fin d),
              (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
            μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))

end

end GroundTheory.Heights₂.Heights
