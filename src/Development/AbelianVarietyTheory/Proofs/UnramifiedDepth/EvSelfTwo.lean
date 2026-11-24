module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.MultiplicativeSeries

open GlobalTheory.GaugeAdjoint

variable {R : Type} [CommRing R] {d m n : ℕ}

theorem ev_mul {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (f g : PS R m d) :
    ev a (f * g) = ev a f * ev a g :=
  subst_mul (hasSubst_pts ha) f g

theorem ev_sum {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) {ι : Type}
    (t : Finset ι) (f : ι → PS R m d) : ev a (∑ i ∈ t, f i) = ∑ i ∈ t, ev a (f i) := by
  unfold ev

  rw [← coe_substAlgHom (hasSubst_pts ha), map_sum]

theorem ev_self_one (f : PS R 1 d) : ev (n := 1) ![pt R d 0] f = f := by
  have e : (fun q : Fin 1 × Fin d => (![pt R d 0] : Fin 1 → Pt R 1 d) q.1 q.2) = X := by
    funext q
    obtain ⟨j, i⟩ := q
    fin_cases j
    rfl
  rw [ev, e, subst_self]
  rfl

theorem ev_self_two (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f := by
  have e : (fun q : Fin 2 × Fin d => (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) q.1 q.2) = X := by
    funext q
    obtain ⟨j, i⟩ := q
    fin_cases j <;> rfl
  rw [ev, e, subst_self]
  rfl

theorem axis_law (G : FGLaw R d) :
    (fun i => ev (n := 1) ![pt R d 0, 0] (G.F i)) = pt R d 0 := by
  funext i
  rw [← G.comm i, ev_ev_two (const_pt 1) (const_pt 0) const_axis, axis_pt_zero, axis_pt_one,
    G.unit i]
  rfl

theorem partial_eq (G : FGLaw R d) (s : PS R 1 d)
    (h : ev (n := 2) ![G.add (pt R d 0) (pt R d 1)] s =
      ev (n := 2) ![pt R d 0] s * ev (n := 2) ![pt R d 1] s) (i : Fin d) :
    ∑ j, ev (n := 1) ![pt R d 0, 0] (pderiv (R := R) ((1 : Fin 2), i) (G.F j)) *
        pderiv (R := R) ((0 : Fin 1), j) s =
      C (coeff (Finsupp.single ((0 : Fin 1), i) 1) s) * s := by
  have hadd : G.add (pt R (n := 2) d 0) (pt R d 1) = G.F := funext fun j => ev_self_two _
  rw [hadd] at h
  have h0 : pderiv (R := R) ((1 : Fin 2), i) (ev (n := 2) ![pt R d 0] s) = 0 := by
    rw [pderiv_ev (const_one (const_pt 0))]
    simp [pderiv_pt]
  have h1 : pderiv (R := R) ((1 : Fin 2), i) (ev (n := 2) ![pt R d 1] s) =
      ev (n := 2) ![pt R d 1] (pderiv (R := R) ((0 : Fin 1), i) s) := by
    rw [pderiv_ev (const_one (const_pt 1))]
    simp [pderiv_pt]
  have hd := congrArg (fun f => ev (n := 1) ![pt R d 0, 0] (pderiv (R := R) ((1 : Fin 2), i) f)) h
  beta_reduce at hd
  rw [Derivation.leibniz, h0, h1, smul_zero, add_zero, smul_eq_mul, ev_mul const_axis,
    axis_pderiv, ev_ev_one (const_pt 0) const_axis, axis_pt_zero, ev_self_one,
    pderiv_ev (const_one G.const), Fin.sum_univ_one, ev_sum const_axis] at hd
  rw [mul_comm, ← hd]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_mul const_axis, ev_ev_one G.const const_axis, axis_law, ev_self_one, mul_comm]
  rfl

theorem main :
  (∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (s : PS R 1 d),
    ev (n := 2) ![G.add (pt R d 0) (pt R d 1)] s = ev (n := 2) ![pt R d 0] s * ev (n := 2) ![pt R d 1] s →
    ∀ u : Fin d → R, Dof G.F u s = C (∑ i, u i * coeff (Finsupp.single ((0 : Fin 1), i) 1) s) * s) := by
  intro R _ d G s h u

  rw [Dof, map_sum, Finset.sum_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc, ← partial_eq G s h i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

end GlobalTheory.MultiplicativeSeries
