module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → (∃ g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr), (∀ b, IsUnit (g b).det) ∧ ∀ (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg g a y y' → LieInt T io m1 m2 y'.u) ∧ (LieInt T io m1 m2 y.u → ∀ (X : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.V)) (a : T.Fr) (y' : FrPt Xo c T.Fr), (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T.V T.Fr)) a y y' → LieInt T io m1 m2 y'.u) := by
  first | exact @GlobalTheory.LamT.lieInt_exists_and_change | exact GlobalTheory.LamT.lieInt_exists_and_change | (intros; apply GlobalTheory.LamT.lieInt_exists_and_change <;> assumption)
