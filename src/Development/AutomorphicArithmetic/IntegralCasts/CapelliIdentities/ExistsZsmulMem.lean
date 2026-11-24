module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
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

theorem UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem.{u_1, u_2} :
    ∀ {E : Type u_1} [inst : Field E] [NumberField E] {W : Type u_2} [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice (E := E) La →
      ∀ (x : W),
        ∃ (d : ℤ),
          d ≠ (0 : ℤ) ∧
            d • x ∈ La := by
  intro E _ _ W _ _ La h x
  refine Submodule.span_induction (p := fun x _ => ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La)
    (fun y hy => ⟨1, one_ne_zero, by simpa using hy⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_
    (h.span_eq_top ▸ Submodule.mem_top : x ∈ Submodule.span E (La : Set W))
  · rintro y z - - ⟨d, hd, hy⟩ ⟨e, he, hz⟩
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add, mul_smul d e z, mul_comm d e, mul_smul e d y]
    exact add_mem (La.zsmul_mem hy e) (La.zsmul_mem hz d)
  · rintro a y - ⟨d, hd, hy⟩
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
    refine ⟨m * d, mul_ne_zero hm hd, ?_⟩
    rw [mul_smul, smul_comm d a y, ← smul_assoc]
    exact h.smul_mem ⟨m • a, hi⟩ _ hy
