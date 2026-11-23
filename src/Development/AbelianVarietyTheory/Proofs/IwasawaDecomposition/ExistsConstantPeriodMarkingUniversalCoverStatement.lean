module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.exists_constant_periodMarking_universalCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (n g' r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g') (lam : (Fin n → ℂ) → Fin r → Fin g' → ℂ) (ρ : Fin g' → Fin r → ℂ), IsLogChart k ch ex lam ρ → ∃ (i : Fin Fu.n) (T₀ : (Fu.Di i).La ≃+ (Fin r → ℤ)), ∀ s ∈ logDom n k, ∀ (a : CxFr Z σ) (W : Letter Dw → Fin g' → ℂ), a.1 = ch.symm (logExp k s) → Dirs a (fun w => (ex a.1 w).left) W → ∃ (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La), Per Fu a i Q ∧ IsIsom (Fu.Di i) gm ∧ ∀ v, ∑ z, Q (gm v) z • W z = ∑ m, T₀ v m • lam s m := by
  first | exact @GlobalTheory.ShFam.Hor.Mark.exists_marking_const | exact GlobalTheory.ShFam.Hor.Mark.exists_marking_const | (intros; apply GlobalTheory.ShFam.Hor.Mark.exists_marking_const <;> assumption)
