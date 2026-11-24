module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReading
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.movedSection_reading_eq_movedFrame_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (φD : Dw.La →ₗ[𝓞 E] (Fin r → E)), Function.Injective φD → Submodule.span E (Set.range φD) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φD x) (φD y))) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ (U.X k).ξ0).im < 0) → ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ), ((δ : Matrix (Fin r) (Fin r) E).det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) E).det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)) := by
  first | exact @GlobalTheory.GeoLevel.rdU_move_eq | exact GlobalTheory.GeoLevel.rdU_move_eq | (intros; apply GlobalTheory.GeoLevel.rdU_move_eq <;> assumption)
