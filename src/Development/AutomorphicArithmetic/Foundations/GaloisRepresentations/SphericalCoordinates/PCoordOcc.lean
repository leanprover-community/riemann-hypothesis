module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.coordOcc_of :
    UpperTheory.Gal.W2.WitOfAd → UpperTheory.Gal.W2.PlacePer → UpperTheory.Gal.W2.CoordOcc := by
  intro hW hP p _ D G L _ _ v _ t₀ _ ρ _ PD RD N hN hNp B a
  obtain ⟨D', t, j, hcls, hpl, hco, hloc⟩ :=
    hW p D G L B N hN hNp a.1.1 ((PD B).lat a.1.2) ((PD B).isLat _) ((PD B).perf _)
  obtain ⟨Q, hQ, hrel⟩ := (RD B).per a.2
  have hev : Even (Module.finrank ℚ D.F) := by
    rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank]
    simp [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  have hg : 2 * D.g = Module.finrank ℤ D.La := by
    obtain ⟨k, hk⟩ := hev
    rw [D.rankLa, Datum.g, hk, ← two_mul, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact ⟨D', t, Q.comp j, j, hcls, (hP p D G L B.β ρ D' j hpl).2 Q hQ hg, hpl, hco, hloc, Q, hQ,
    fun u => rfl, hrel⟩
