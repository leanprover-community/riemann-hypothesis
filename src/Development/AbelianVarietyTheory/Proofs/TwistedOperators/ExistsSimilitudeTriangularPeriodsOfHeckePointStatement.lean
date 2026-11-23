module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

theorem _root_.GlobalTheory.T.exists_similitude_triangular_periods_of_heckePoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → ∃ (gam : (U.X k).Λ →ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (p : ℚ) ^ 2 * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ w : (U.X k').Λ, ∃ v, gam v = (p ^ 2) • w) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ m < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) m = p * ∑ j ∈ Finset.range (Dw.mult τ), A τ m j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (m : Fin (Dw.mult τ)), A τ m m = Formalism.L2.PjFree.toC (t (some ⟨τ, m⟩) : CAt σ) := by
  first | exact @GlobalTheory.HeckeEx.exists_similitude_tri_of_hkPt | exact GlobalTheory.HeckeEx.exists_similitude_tri_of_hkPt | (intros; apply GlobalTheory.HeckeEx.exists_similitude_tri_of_hkPt <;> assumption)
