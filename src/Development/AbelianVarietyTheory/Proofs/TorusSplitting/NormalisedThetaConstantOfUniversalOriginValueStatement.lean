module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormalisedThetaConstantOfUniversalOriginValue
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.normalisedThetaConstant_of_universal_origin_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra c.F F] (z : FrPt Xo c F), z.x = spMap (algebraMap (FractionRing R) F) ≫ x → ∀ th : GlobalTheory.UT.SecA A F 1, Φ.SecTie z.x z.s th → ∀ (m : ℕ), Odd m → ∀ (p : ptO Xo z.x ⟶ Xo.univ.t.G) (p' : TFK (R := R) F ⟶ A.A) (w : F), p ^ (m ^ 2) = 1 → p'.left ≫ Φ.φ = p.left → IsNullVal Xo c m z p w → ∃ t, GlobalTheory.UT.ThC A Φ.ρ m th p' t w := by
  first | exact @GlobalTheory.EtaVal.NullMove.thC_of_isNullVal | exact GlobalTheory.EtaVal.NullMove.thC_of_isNullVal | (intros; apply GlobalTheory.EtaVal.NullMove.thC_of_isNullVal <;> assumption)
