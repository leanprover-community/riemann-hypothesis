module

public import Formalism.CharacterColumnKernels.StatementN
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

open Finset

namespace Formalism.NG

theorem descent : StatDescent := by
  intro O _ X X' T T' Z p q b hexp hind f' hf' hvan π'
  obtain ⟨a, haT, rfl⟩ := hexp f' hf'
  have hker : ∀ k, (⟨a k, haT k⟩ : T) ∈ ccIdeal T Z := by
    intro k
    rw [ccIdeal, RingHom.mem_ker]
    funext x
    have hx : x.1 ∉ Z := x.2
    have h0 := hind x.1 hx (fun k => a k x.1) (fun x' hx' => by
      have e := hvan x' (by rw [hx']; exact hx)
      simpa [hx', Finset.sum_apply, Pi.mul_apply, Function.comp] using e)
    have e2 := congrFun h0 k
    simpa [resOff] using e2
  rw [Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, hker k, rfl⟩)

theorem vccSpan : StatVccSpan := by
  intro O _ _ _ X T Z x y hy
  induction hy using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨c, hc, rfl⟩ := hs
    exact iInf₂_le c hc
  | zero => simp
  | add a b _ _ ha hb =>
    exact le_trans (le_min ha hb) IsDiscreteValuationRing.addVal_add
  | smul r a _ ha =>
    rw [smul_eq_mul, IsDiscreteValuationRing.addVal_mul]
    exact le_trans ha le_add_self

end Formalism.NG
