module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.finrank_archimedean_eq_two_mul_dim :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → UpperTheory.Gal.W2.ArchSpan → Module.finrank ℝ (Arch G) = Module.finrank ℚ (VQ D) ∧ Module.finrank ℝ (Arch G) = 2 * D.g := by
  intro p _ D G L hm hA
  have h1 : Module.finrank ℝ (Arch G) = Fintype.card (InfinitePlace G.F) * (G.n * 2) := by
    have hc : Module.finrank ℝ (Fin G.n → ℂ) = G.n * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    unfold Arch
    rw [Module.finrank_pi_fintype]
    simp [hc]
  have h2 : Module.finrank ℝ (Arch G) = G.n * Module.finrank ℚ G.F := (hA G.F G.n).2.1
  have h3 : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    (AlgEquiv.ofRingEquiv (f := L.e) (fun r => by simp)).toLinearEquiv.finrank_eq.symm
  have h4 : Module.finrank ℚ (VQ D) = D.m * D.n * Module.finrank ℚ D.F := by
    haveI := D.freeLa
    rw [← D.rankLa]
    exact Module.finrank_baseChange
  have hg : D.g = D.m * D.n * Module.finrank ℚ D.F / 2 := rfl
  have h2' : Module.finrank ℝ (Arch G) = D.n * Module.finrank ℚ D.F := by
    rw [h2, h3, L.n_eq]
  have h1' : Module.finrank ℝ (Arch G) = 2 * (Fintype.card (InfinitePlace G.F) * D.n) := by
    rw [h1, L.n_eq]; ring
  rw [hm, _root_.one_mul] at h4 hg
  refine ⟨by rw [h2', h4], ?_⟩
  rw [hg, ← h2', h1']
  omega
