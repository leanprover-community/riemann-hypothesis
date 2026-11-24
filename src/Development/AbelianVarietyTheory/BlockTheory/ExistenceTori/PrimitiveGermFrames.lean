module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetChartLaws
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SymmetricAdjointUnits
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]

section Group

variable (G : Over X₀) [GrpObj G] [IsCommMonObj G]

variable (x : Sp S ⟶ X₀) {d : ℕ}


variable {G x}

end Group

section Germ

variable {G : Over X₀} [GrpObj G] {x : Sp S ⟶ X₀} {d : ℕ}

end Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev PrimIso (t : SAB H X₀) : Type :=
  LB.Iso t.PP.L (cubeLB t.G ![𝟙 t.G, t.act.act H.w0] t.PP.L)

end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames
