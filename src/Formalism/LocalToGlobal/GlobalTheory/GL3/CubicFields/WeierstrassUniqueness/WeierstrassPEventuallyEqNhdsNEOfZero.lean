module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)


open Filter Topology in
theorem weierstrassP_eventuallyEq_nhdsNE_of_zero (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) (x : ℂ) :
    L.weierstrassP =ᶠ[𝓝[≠] x] L'.weierstrassP := by
  set f : ℂ → ℂ := fun z => L.weierstrassP z - L'.weierstrassP z with hf
  have hm : MeromorphicOn f Set.univ := fun z _ =>
    (L.meromorphic_weierstrassP z).sub (L'.meromorphic_weierstrassP z)
  have h0 : meromorphicOrderAt f 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [h] with z hz
    simp [hf, hz]
  have hx : meromorphicOrderAt f x = ⊤ := by
    by_contra hne
    have := (hm.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
      ⟨⟨x, Set.mem_univ _⟩, hne⟩ ⟨0, Set.mem_univ _⟩
    exact this h0
  rw [meromorphicOrderAt_eq_top_iff] at hx
  filter_upwards [hx] with z hz
  exact sub_eq_zero.1 hz


theorem lattice_subset_of_weierstrassP (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) :
    (L.lattice : Set ℂ) ⊆ L'.lattice := by
  intro l hl
  by_contra hl'
  have h1 := L.order_weierstrassP l hl
  have h2 : 0 ≤ meromorphicOrderAt L'.weierstrassP l :=
    (L'.analyticOnNhd_weierstrassP l hl').meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr (weierstrassP_eventuallyEq_nhdsNE_of_zero L L' h l), h1] at h2
  exact absurd h2 (by decide)


theorem lattice_eq_of_weierstrassP (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) :
    (L.lattice : Set ℂ) = L'.lattice :=
  Set.Subset.antisymm (lattice_subset_of_weierstrassP L L' h)
    (lattice_subset_of_weierstrassP L' L h.symm)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
