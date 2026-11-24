module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def vEt (Q : LocalPointData G la) (ζ : PtsG G la) : ℝ :=
  if j < D.R.m then (X.vAt la (Q.y ζ) (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ)) else 0

theorem ep_nu_int {S : Scal B} (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) :
    ∃ n : ℤ, (ep (unifO X la G.N) ζ : ℝ) * Q.nu S ζ = n := (hTie ζ).2.2.2.1

theorem levels_eq [Fintype (PtsG G la)] (Q : LocalPointData G la) (T : ℕ) (c : ℝ) :
    (T : ℝ) * max 0 c * ∑ ζ, ((ep (unifO X la G.N) ζ : ℝ) * (fdeg ζ : ℝ)) * vEt Q ζ =
      if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * Q.Net else 0 := by
  split_ifs with hj
  · unfold LocalPointData.Net vEt
    rw [finsum_eq_sum_of_fintype]
    simp only [if_pos hj]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    ring
  · unfold vEt
    simp only [if_neg hj, mul_zero, Finset.sum_const_zero]

end Formalism.MainNotions.Gaps.EtaleWeightGaps
