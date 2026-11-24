module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FibPointsMulEquiv
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_mulEquiv_ptO_hom_of_eq_spMap_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap (FractionRing R) F) ≫ x → ∃ tr : (ptO Xo xF ⟶ Xo.univ.t.G) ≃* (TFK (R := R) F ⟶ A.A), (∀ p, (tr p).left ≫ Φ.φ = p.left) ∧ ∀ (a : Xo.univ.t.G ⟶ Xo.univ.t.G) (a' : A.A ⟶ A.A), a'.left ≫ Φ.φ = Φ.φ ≫ a.left → ∀ p, tr (p ≫ a) = tr p ≫ a' := by
  first | exact @GlobalTheory.EtaVal.fib_points_mulEquiv | exact GlobalTheory.EtaVal.fib_points_mulEquiv | (intros; apply GlobalTheory.EtaVal.fib_points_mulEquiv <;> assumption)
