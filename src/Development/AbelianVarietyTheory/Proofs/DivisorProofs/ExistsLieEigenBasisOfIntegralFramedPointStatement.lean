module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisOfIntegralFramedPoint
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

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), Integral T io y → ∀ (χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y), χ ≫ pullback.snd _ _ = spMap φ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) → ∀ (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n), ∃ v : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt (χ ≫ pullback.fst _ _) ⟶ Y.t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis Y.t.act (χ ≫ pullback.fst _ _) (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (letI := io.toAlgebra; SameVec Y y (y.u τ (Fin.cast hn.symm i)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (v i).left)) := by
  first | exact @GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec | exact GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec | (intros; apply GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec <;> assumption)
