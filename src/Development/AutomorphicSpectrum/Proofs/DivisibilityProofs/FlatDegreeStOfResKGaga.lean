module

public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsConstSectionKroneckerCharStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem flatDegreeSt_of_resK_gaga : Geo.ResK.ResKStatement → GagaSections → GlobalTheory.FlatCore.FlatDegreeSt := by
  intro hR hG E _ _ _ H _ _ χ hχ Dw l Xo c r U x hL Z τ
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_const_section_kronecker_char hR hG E H Dw l Xo c r U x hL χ hχ Z τ
  let t : GlobalTheory.FlatLine.FlatSec U x Z τ := s.relat (GlobalTheory.FlatLine.flDefect_vw Dw c τ)
    (by simpa using GlobalTheory.FlatLine.finite_flDefect_vw (Dw := Dw) (c := c) τ)
  have ht : t.deg = GlobalTheory.FlatLine.flatDegVal Dw (GlobalTheory.CM.logOm E χ).re := by
    have h2 := GlobalTheory.FlatLine.ConstSec.deg_relat s (GlobalTheory.FlatLine.flDefect_vw Dw c τ)
      (by simpa using GlobalTheory.FlatLine.finite_flDefect_vw (Dw := Dw) (c := c) τ)
    simp only [Pi.zero_apply, zero_sub, neg_mul, finsum_neg_distrib, GlobalTheory.FlatLine.sum_flDefect_vw] at h2
    show (s.relat _ _).deg = _
    rw [h2, hs, GlobalTheory.FlatLine.flatDegVal]; ring
  refine ⟨⟨t⟩, fun s' => ?_⟩
  rw [GlobalTheory.FlatLine.ConstSec.deg_eq hL.unf hL.geo t s', ht, neg_neg]

end GlobalTheory.CompanionTheory.Ar.Br
