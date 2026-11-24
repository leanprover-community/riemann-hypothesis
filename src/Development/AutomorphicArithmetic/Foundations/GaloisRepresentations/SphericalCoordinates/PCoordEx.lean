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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.coordEx_of :
    UpperTheory.Gal.W2.PlaceEx → UpperTheory.Gal.W2.AdOfWit → UpperTheory.Gal.W2.PlaceLoc → UpperTheory.Gal.W2.PlacePer → UpperTheory.Gal.W2.CoordEx := by
  intro hEx hAd hLoc hPer p _ D G L ha hm v hv t₀ ht₀ ρ hρ PD RD N hN hNp D' t P hC hP
  obtain ⟨q, j, hj⟩ := hEx p D G L ha hm v hv t₀ ht₀ ρ hρ N D' t hC ⟨P, hP⟩
  obtain ⟨⟨f, nu, rfl, h1, h2⟩, hH⟩ := hC
  have hW : IsWit D' f nu := by
    refine ⟨h1, fun n hn hnp => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := h2 n hn hnp
    refine ⟨a1, a2, a3, a4, fun a a' => ?_⟩
    have e : D.plat.EF a a' = 2 * D.EF a a' := by
      show ((2 : ℤ) • D.EF) a a' = _
      simp [LinearMap.smul_apply]
    have := a5 a a'
    rw [e] at this
    exact this
  obtain ⟨h₁, hR⟩ := hAd p D G L (Quot.out q) D' j hj f nu hW
  obtain ⟨M, hM, hs, hML⟩ := hLoc p D G L _ D' j hj hH
  obtain ⟨hp, rfl⟩ := (PD (Quot.out q)).onto M hM hs
  obtain ⟨Q, hQ, hQP⟩ := (hPer p D G L _ ρ D' j hj).1 P hP
  obtain ⟨z, hz⟩ := (RD (Quot.out q)).line Q hQ
  exact ⟨q, ((h₁, hp), z), j, hj, hR N hN hNp, hML, Q, hQ, hQP, hz⟩
