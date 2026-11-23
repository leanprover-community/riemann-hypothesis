module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
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

noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
namespace GlobalTheory.UPoinc.UModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def valInt (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* OO p :=
  (RatModel.valLoc t.y z₁ (specializes_of_eq t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem val_eq_valInt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : t.val a = (valInt t a : PadicAlgCl p) :=
  RatModel.val_spMap_comp (OO p).subtype t.y (specializes_of_eq t.cen) (X₁.M.stalkEquiv z₁ a)

theorem norm_val_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖t.val a‖ ≤ 1 := by
  rw [val_eq_valInt]
  have h : Valued.v (valInt t a : PadicAlgCl p) ≤ 1 := (valInt t a).2
  exact_mod_cast h

end GlobalTheory.UPoinc.UModel
