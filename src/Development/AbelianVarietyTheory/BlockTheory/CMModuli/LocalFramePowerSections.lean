module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections

abbrev PowSec {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (N : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (N : ℤ)))

def IsTrait {R₁ W : Type} [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [IsLocalRing W] (ρ : R₁ →+* W)
    (κ : FractionRing R₁ →+* FractionRing W) : Prop :=
  GlobalTheory.UU.CDVR W ∧ κ.comp (algebraMap R₁ (FractionRing R₁)) = (algebraMap W (FractionRing W)).comp ρ

section Frames

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G)


end Frames

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  (Xo : Moduli D l) {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Data

end GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections
end
