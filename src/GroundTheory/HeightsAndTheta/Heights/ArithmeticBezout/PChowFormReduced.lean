module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Helpers

variable {F : Type*} [Field F] {n k : ℕ}

theorem incidence_mono {I W : Ideal (MvPolynomial (Fin n) F)} (hIW : I ≤ W)
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence W k) : u ∈ incidence I k := by
  obtain ⟨x, hx0, hxW, hxu⟩ := hu
  exact ⟨x, hx0, fun g hg => hxW g (hIW hg), hxu⟩

theorem exists_relComps_of_mem_incidence {J : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence J k) :
    ∃ W ∈ relComps J, u ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxu⟩ := hu
  let φ : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F := aeval x
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker φ := fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxu⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  have := RingHom.mem_ker.mp (hWP hj)
  simpa [φ] using this

theorem mem_support_fundCycle_iff {J : Ideal (MvPolynomial (Fin n) F)} (hJ : J.IsRadical)
    {W : Ideal (MvPolynomial (Fin n) F)} : W ∈ (fundCycle J).support ↔ W ∈ relComps J := by
  classical
  rw [Finsupp.mem_support_iff]
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  constructor
  · intro h
    by_contra h'
    exact h (if_neg h')
  · intro h
    rw [if_pos h, localMult_eq_one_of_isRadical hJ h.1]
    exact one_ne_zero

end Helpers

end

end GroundTheory.Heights₂.Heights
