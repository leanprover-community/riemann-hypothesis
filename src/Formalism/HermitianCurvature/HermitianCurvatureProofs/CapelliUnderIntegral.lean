module

public import Formalism.HermitianCurvature.StatementQ
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.StatementJF

@[expose] public section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CapelliUnderIntegral

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

open scoped Matrix.Norms.Elementwise

theorem glev0 {k r : ℕ} (g : Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ GV k r := by
  simp only [Q.Glev, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, fun a ha => by simp at ha⟩

theorem integrable_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    Integrable (fun x => (L.map (fun i => φ i x)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem integral_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    ∫ x, (L.map (fun i => φ i x)).sum ∂μ = (L.map (fun i => ∫ x, φ i x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := h i (by simp)
    have hL : ∀ j ∈ L, Integrable (φ j) μ := fun j hj => h j (by simp [hj])
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add hi (integrable_map_sum L φ hL), ih hL]

end Formalism.FourierDecayAlt.P.CapelliUnderIntegral

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

open scoped Matrix.Norms.Elementwise

end Formalism.FourierDecayAlt.P
