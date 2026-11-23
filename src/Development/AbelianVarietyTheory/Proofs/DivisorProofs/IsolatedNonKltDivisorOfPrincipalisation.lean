module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedLcCentreOfZeroLcThresholdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalCutAngehrnSiuInductionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory

theorem isolatedNonKltDivisor_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.IsolatedNonKltDivisor := by
  intro hP X _ _ _ p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hnef hbig hx hc hvol hsum
  letI := algebraΓOfHom p
  have hLB : N₀.IsLB := hnef.isLB
  obtain ⟨A, hA, hj⟩ := GlobalTheory.T.exists_logCanonical_cut_angehrnSiu_induction hP X p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hLB hnef hbig hx hc hvol
  obtain ⟨j', lam, μ, m', D₀, hj', hm', hD₀, hμ, hlam, hnum, hcut⟩ := hj 0 (by omega)
  obtain rfl : j' = 0 := Nat.le_zero.mp hj'
  exact GlobalTheory.T.exists_isolated_lcCentre_of_zero_lcThreshold hP X p n hproj hdim hn Δ r N₀ x c hΔ hklt hr hLB hnef hbig hx hc hvol hsum
    A lam μ m' D₀ hA hm' hD₀ hμ (by simpa using hlam) hnum hcut

end GlobalTheory
