module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedSmoothProjModificationOffO
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS

theorem _root_.GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  first | exact @GlobalTheory.ModifGeomConn.geometricallyConnected_modif | exact GlobalTheory.ModifGeomConn.geometricallyConnected_modif | (intros; apply GlobalTheory.ModifGeomConn.geometricallyConnected_modif <;> assumption)
