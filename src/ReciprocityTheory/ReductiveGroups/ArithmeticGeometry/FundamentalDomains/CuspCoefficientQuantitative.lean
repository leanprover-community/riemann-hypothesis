module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientDecay
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cusp_coefficient_bound_of_unipotent_lattice_lift (hL2 : UnipotentLatticeLift (E := E)) : CuspCoefficientBound (E := E) := by
  intro r X u hu huΛ la P hP hchi ν
  have hiso : X.IsIso (u 0) := ⟨huΛ 0, hu.1 0 0, hu.2.ne_zero 0⟩
  refine ⟨CuspCoefficientFlow.fj_diffOn X.toData la P hP.1 hiso ν, ?_, ?_⟩
  · intro x hx b hb
    have hfl : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b) =
        rmul (X.flow (u 0) (fun τ => (s τ : ℂ)) x) b := fun s => by
      funext τ
      show X.flowMat (u 0) τ (s τ : ℂ) * (mat x τ * mat b τ) =
        (X.flowMat (u 0) τ (s τ : ℂ) * mat x τ) * mat b τ
      rw [Matrix.mul_assoc]
    have hPb : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b)) =
        bchar la b * P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl]
      exact hP.1.1.2.1 _ (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1 b hb
    unfold Data.fj
    split_ifs with h1 h2
    · simp_rw [hPb, mul_assoc]
      rw [integral_const_mul]
      ring
    · simp
    · simp
  · intro b hb x hx
    let a0 : X.Ψ → Fin 2 → ℂ := fun _ => ![1, 0]
    have hemb : X.embV (u 0) = X.uvec u a0 := by
      funext τ
      simp [Data.uvec, a0, Fin.sum_univ_two, Data.embV]
    have hfl : ∀ (s : X.Ψ → ℝ) y, X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.Zb u (fun τ i k => (s τ : ℂ) * a0 τ i * conj (a0 τ k)) y := fun s y => by
      rw [show X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.flowV (X.embV (u 0)) (fun τ => (s τ : ℂ)) y from rfl, hemb, Data.flowV_uvec]
    have hZ : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x) =
        X.Zb u b (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl, hfl, Data.Zb_Zb X.toData u hu.1, Data.Zb_Zb X.toData u hu.1, add_comm]
    have hPZ : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x)) =
        P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hZ]
      exact (hL2 r X u hu huΛ).2.1 la P hP.1.1 hchi b hb _
        (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1
    unfold Data.fj
    simp_rw [hPZ]

end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative
