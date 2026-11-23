module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PackingSeparation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RingOfIntegersCovering

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField InfinitePlace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem integerApproximationCount_holds : IntegerApproximationCount (E := E) := by
  intro r X
  refine ⟨fun w' => ?_, fun R hR => PackingSeparation.count R hR⟩
  classical
  have hconjmem : ∀ φ : E →+* ℂ, φ ∉ X.Ψ → ComplexEmbedding.conjugate φ ∈ X.Ψ := by
    intro φ h
    have := X.cmType (ComplexEmbedding.conjugate φ)
    rw [TraceIntegralBasis.conj_conj] at this
    exact this.mpr h
  let Z : TraceIntegralBasis.VS E := WithLp.toLp 2 (fun w : TraceIntegralBasis.CP E =>
    if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
    else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩))
  obtain ⟨α, hα⟩ := RingOfIntegersCovering.cover_OE Z
  refine ⟨α, fun τ => ?_⟩
  set w : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩ with hw
  have hcoord : ‖Z w - w.1.embedding (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have h := PiLp.norm_apply_le (Z - TraceIntegralBasis.iota E (α : E)) w
    rw [PiLp.sub_apply, TraceIntegralBasis.iota_apply] at h
    exact h.trans hα
  have hZw : Z w = if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
      else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩) := rfl
  have hmk : InfinitePlace.mk w.1.embedding = InfinitePlace.mk τ.1 := mk_embedding _
  rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
  · have hmem : w.1.embedding ∈ X.Ψ := h ▸ τ.2
    have hZ : Z w = w' τ := by
      rw [hZw, dite_eq_left hmem]
      congr 1
      exact Subtype.ext h
    rw [hZ, h] at hcoord
    rwa [norm_sub_rev] at hcoord
  · have hnot : w.1.embedding ∉ X.Ψ := by
      intro hm
      exact ((X.cmType _).mp hm) (h ▸ τ.2)
    have hZ : Z w = conj (w' τ) := by
      rw [hZw, dite_eq_right hnot]
      congr 2
      exact Subtype.ext h
    have hemb : w.1.embedding (α : E) = conj (τ.1 (α : E)) := by
      rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    rw [hZ, hemb, ← map_sub, Complex.norm_conj] at hcoord
    rwa [norm_sub_rev] at hcoord

end ReciprocityTheory.ChartRestriction.G.FD
