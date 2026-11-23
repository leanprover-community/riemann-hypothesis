module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Unique

theorem pullRatio_top_eq {N : ℕ} {x x' : Sp ℂ ⟶ PSpace ℤ N} (i j : Fin (N + 1))
    (h : ⊤ ≤ x ⁻¹ᵁ chart ℤ N i) (h' : ⊤ ≤ x' ⁻¹ᵁ chart ℤ N i)
    (e : valR x (chart ℤ N i) (ratio ℤ N i j) = valR x' (chart ℤ N i) (ratio ℤ N i j)) :
    pullRatio x ⊤ i h j = pullRatio x' ⊤ i h' j := by
  rw [valR, valR, dite_eq_left h, dite_eq_left h'] at e
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 e

theorem valR_comp_prB {m : ℕ} {n : Fin (m + 1) → ℕ} (x : Sp ℂ ⟶ MP ℤ m n) {k : Fin (m + 1)} (i j : Bk n k)
    (h : ⊤ ≤ x ⁻¹ᵁ blockChart n k i) :
    valR (x ≫ prB n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) =
      valR x (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) := by
  have h' : ⊤ ≤ (x ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) i := h
  rw [valR, valR, dite_eq_left h, dite_eq_left h', pullRatio,
    ← Scheme.Hom.appLE_comp_appLE x (prB n k) (chart ℤ (n k) i) (blockChart n k i) ⊤ le_rfl h]
  rfl

end GlobalTheory.CompanionTheory.MPDict.Unique


open GlobalTheory.CompanionTheory.MPDict.Unique in
theorem GlobalTheory.CompanionTheory.MPDict.isUnder_unique : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y' := by
  intro m n z y y' h h'
  refine Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_)
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (ptChart (y.1 (IsLocalRing.closedPoint ℂ)) k)) :=
    mem_ptsIn.2 (mem_ptChart _ k)
  obtain ⟨i, hi⟩ : ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ⟨_, hy⟩
  have hz : z ⟨k, i⟩ ≠ 0 := ((h k i).1).1 hi
  have hi' : y' ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((h' k i).1).2 hz
  refine GlobalTheory.ProjSpace.hom_ext ?_ fun t => ⟨⊤, trivial, i, hi, hi', fun j => ?_⟩
  · have s : pr ℤ m n k ≫ PSpace.str ℤ (n k) = mpStr ℤ m n := pr_toSpecBase ℤ m n k
    rw [Category.assoc, Category.assoc, s, y.2, y'.2]
  · have a : ⊤ ≤ y.1 ⁻¹ᵁ blockChart n k i := hi
    have a' : ⊤ ≤ y'.1 ⁻¹ᵁ blockChart n k i := hi'
    refine pullRatio_top_eq (x := y.1 ≫ prB n k) (x' := y'.1 ≫ prB n k) i j a a' ?_
    rw [valR_comp_prB y.1 i j a, valR_comp_prB y'.1 i j a']
    exact ((h k i).2 j hi).trans ((h' k i).2 j hi').symm
