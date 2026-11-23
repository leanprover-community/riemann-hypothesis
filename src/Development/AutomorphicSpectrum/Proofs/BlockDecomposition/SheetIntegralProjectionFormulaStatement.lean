module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIntegralProjectionFormula
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

@[expose] public section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

theorem _root_.GlobalTheory.T.sheet_integral_projection_formula : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n),
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (i (genericPoint X))) (D + 1) → IsGoodProj (ptIdeal (i (genericPoint X))) Ψ →
    ∀ {ι : Type} (e : ι → OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
      (Γ : ι → (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (S : ι → Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)),
      (∀ l, GlobalTheory.CompanionTheory.MixZ.ArchEq.IsPiece i Ψ N (e l) (Γ l)) → (∀ l, S l ⊆ (e l).source) →
      Pairwise (Function.onFun Disjoint S) → ∀ v : Fin D → ℂ,
      (∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (segre z) = Fin.cons 1 v →
        ∃ y, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ y ∈ ⋃ l, S l) →
      ∀ (h : (((k : Fin (m + 1)) → Bk n k) → ℂ) → ℝ) (T : ι → ℝ),
      (∀ l, v ∈ (e l) '' S l → h (segre (Γ l v)) = T l) →
      ∑ᶠ w ∈ fibre (ptIdeal (i (genericPoint X))) Ψ v, h w = ∑' l, ((e l) '' S l).indicator (fun _ => T l) v := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.finsum_fibre_eq | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.finsum_fibre_eq | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.finsum_fibre_eq <;> assumption)
