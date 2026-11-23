module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLieEigenspaceFrameAtUniformisation
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

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology


theorem _root_.GlobalTheory.T.eventually_lieEigenspaceFrameAt_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ᶠ w in nhds v, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := by
  first | exact @GlobalTheory.UnifFrame.eventually_frameAt_unif | exact GlobalTheory.UnifFrame.eventually_frameAt_unif | (intros; apply GlobalTheory.UnifFrame.eventually_frameAt_unif <;> assumption)
