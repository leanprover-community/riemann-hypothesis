module

public import Mathlib.LinearAlgebra.StdBasis
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.Qi34.flagSub :
    {F : Type} →
      [inst : Field F] →
        {N : Type} →
          [inst_1 : AddCommGroup N] → [inst_2 : _root_.Module F N] → {n : ℕ} → Module.Basis (Fin n) F N → ℕ → Submodule F N :=
    fun {F : Type} [Field F] {N : Type} [AddCommGroup N] [_root_.Module F N] {n : ℕ} (b : Module.Basis (Fin n) F N)
        (i : ℕ) ↦
      Submodule.span F ((⇑b : Fin n → N) '' {j : Fin n | (↑j : ℕ) < i})

theorem UpperTheory.Reformulated.B.Qi34.mem_flagSub_iff :
    ∀ {F : Type} [inst : Field F] {n : ℕ} (i : ℕ) (x : Fin n → F),
      x ∈ UpperTheory.Reformulated.B.Qi34.flagSub (Pi.basisFun F (Fin n)) i ↔ ∀ (j : Fin n), i ≤ (↑j : ℕ) → x j = (0 : F) := by
  intro F _ n i x
  unfold UpperTheory.Reformulated.B.Qi34.flagSub
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hx
    have hmem : j ∈ ((Pi.basisFun F (Fin n)).repr x).support := by
      rw [Finsupp.mem_support_iff, Pi.basisFun_repr]
      exact hx
    have hlt : (j : ℕ) < i := h (Finset.mem_coe.mpr hmem)
    omega
  · intro h j hj
    have hx : x j ≠ 0 := by
      have := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj)
      rwa [Pi.basisFun_repr] at this
    show (j : ℕ) < i
    by_contra hlt
    exact hx (h j (not_lt.mp hlt))
