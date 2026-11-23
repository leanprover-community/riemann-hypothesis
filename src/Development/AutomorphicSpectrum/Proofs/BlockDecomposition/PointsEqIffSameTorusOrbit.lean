module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

@[expose] public section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.Orbit

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_mem_blockChart (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) :
    ∃ i, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) :=
  ⟨ptChart _ k, GlobalTheory.CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩

theorem exists_ne_zero_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (k : Fin (m + 1)) : ∃ i, z ⟨k, i⟩ ≠ 0 :=
  (exists_mem_blockChart w k).imp fun i hi => (h k i).1.1 hi

theorem sameOrbit_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z z' : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (h' : IsUnder w z') : SameOrbit z z' := by
  choose c hc using exists_mem_blockChart w
  refine ⟨fun k => z ⟨k, c k⟩ / z' ⟨k, c k⟩,
    fun k => div_ne_zero ((h k _).1.1 (hc k)) ((h' k _).1.1 (hc k)), ?_⟩
  funext ⟨k, j⟩
  have e := ((h k (c k)).2 j (hc k)).symm.trans ((h' k (c k)).2 j (hc k))
  have a := (h k _).1.1 (hc k)
  have b := (h' k _).1.1 (hc k)
  rw [div_eq_div_iff a b] at e
  show z ⟨k, j⟩ = z ⟨k, c k⟩ / z' ⟨k, c k⟩ * z' ⟨k, j⟩
  rw [div_mul_eq_mul_div, eq_div_iff b]
  linear_combination e

theorem eq_iff_sameOrbit (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y y' : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ)
    (h : IsUnder (PtsOver.map i rfl _ y) z) (h' : IsUnder (PtsOver.map i rfl _ y') z') :
    y = y' ↔ SameOrbit z z' := by
  constructor
  · rintro rfl
    exact sameOrbit_of_isUnder h h'
  · intro ho
    have e := (Under.existsUnique_isUnder m n z (exists_ne_zero_of_isUnder h)).unique h
      (isUnder_of_sameOrbit m n _ z' z h' ho)
    exact Subtype.ext ((cancel_mono i).1 (congrArg Subtype.val e))

end GlobalTheory.CompanionTheory.MixZ.Orbit
