module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem multAt_pos_of_mem_divSupp {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp P s) : 0 < multAt (P ⊔ Ideal.span {s}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W)))
  rw [multAt, dite_eq_left hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
