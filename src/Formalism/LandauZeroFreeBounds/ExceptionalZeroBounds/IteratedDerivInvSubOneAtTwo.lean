module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma iteratedDeriv_inv_sub_one_at_two (m : ℕ) :
    iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹) 2 = (-1) ^ m * (m ! : ℂ) := by
  have h : (fun s : ℂ => (s - 1)⁻¹) = fun x => (1 * x - 1)⁻¹ := by simp
  rw [iteratedDeriv_eq_iterate, h, iter_deriv_inv_linear_sub]
  norm_num

lemma iteratedDeriv_lseries_at_two {a : ℕ → ℂ} {G : ℂ → ℂ} {lam : ℂ} (hG : Differentiable ℂ G)
    (hFG : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + lam * (s - 1)⁻¹) (m : ℕ) :
    iteratedDeriv m (LSeries a) 2 = iteratedDeriv m G 2 + lam * ((-1) ^ m * (m ! : ℂ)) := by
  have hU : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : LSeries a =ᶠ[nhds (2 : ℂ)] fun s => G s + lam * (s - 1)⁻¹ := by
    filter_upwards [hU] with s hs using hFG s hs
  have hinv : ContDiffAt ℂ m (fun s : ℂ => lam * (s - 1)⁻¹) 2 :=
    contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (by norm_num))
  rw [(hev.iteratedDeriv m).eq_of_nhds, iteratedDeriv_fun_add hG.contDiff.contDiffAt hinv,
    iteratedDeriv_const_mul_field, iteratedDeriv_inv_sub_one_at_two]

end Formalism.ZeroFreeDirichlet
