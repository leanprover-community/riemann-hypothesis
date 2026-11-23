module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedPointOverOfLieEigenspaceFrame
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ z ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  first | exact @GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame | exact GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame | (intros; apply GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame <;> assumption)
