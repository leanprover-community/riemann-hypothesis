module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinear
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaNullValue_existsUnique_natural_linear : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (N : ℕ), Odd N → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (p : ptO Xo y.x ⟶ Xo.univ.t.G), p ^ (N ^ 2) = 1 → ∃! w, IsNullVal Xo c N y p w) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap ψ y z → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo z.x ⟶ Xo.univ.t.G), p'.left = spMap ψ.toRingHom ≫ p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N z p' (ψ w)) ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo y'.x ⟶ Xo.univ.t.G), p'.left = p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N y' p' ((t none : Sˣ) * w) := by
  first | exact @GlobalTheory.nullValue_existsUnique_natural_linear | exact GlobalTheory.nullValue_existsUnique_natural_linear | (intros; apply GlobalTheory.nullValue_existsUnique_natural_linear <;> assumption)
