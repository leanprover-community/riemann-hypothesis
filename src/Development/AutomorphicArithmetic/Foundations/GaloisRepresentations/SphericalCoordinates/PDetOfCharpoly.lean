module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma det_one_sub_smul_matrix {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (y : ℂ) :
    (1 - y • M).det = Polynomial.eval y M.charpoly.reverse := by
  rw [Matrix.reverse_charpoly, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply]; ring
  · simp [Matrix.one_apply, h]; ring

private lemma det_one_sub_smul_linear {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) (y : ℂ) :
    LinearMap.det (1 - y • f) = Polynomial.eval y f.charpoly.reverse := by
  classical
  let b := Module.finBasis ℂ V
  rw [← LinearMap.det_toMatrix b, map_sub, map_smul, LinearMap.toMatrix_one,
    det_one_sub_smul_matrix, LinearMap.charpoly_toMatrix]

theorem UpperTheory.Gal.W2.detOfCharpoly_of :
    UpperTheory.Gal.W2.DetOfCharpoly := by
  intro V W _ _ _ _ _ _ T Θ d A h y
  rw [det_one_sub_smul_linear, det_one_sub_smul_linear, ← Polynomial.eval_mul,
    ← Polynomial.reverse_mul_of_domain, ← h, det_one_sub_smul_matrix]
