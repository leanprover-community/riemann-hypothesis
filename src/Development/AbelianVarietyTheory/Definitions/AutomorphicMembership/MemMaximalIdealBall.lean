module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Cht

section Ball

variable {C : Type} [NormedField C] [IsUltrametricDist C]

end Ball

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure PtAt (Z : Mdl Y i₀) (C : SCF p) : Type where
  P : PointsOfFlagModel.PtC (Y Z.i) C
  z : Sp ↥(intO ↥C.S) ⟶ Z.X
  z_π : z ≫ Z.π = P.yt

namespace PtAt

variable {Z : Mdl Y i₀} {C : SCF p} (y : PtAt Z C)

def gen : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ y.z

end PtAt

structure Fam (Y : LocalSystem Xo p W) (i₀ : Idx H p) (C : SCF p) : Type where
  pt : ∀ Z : Mdl Y i₀, PtAt Z C
  compat : ∀ Z₁ Z₂ : Mdl Y i₀, Corr Z₁ Z₂ → NatImg Z₁ Z₂ (pt Z₁).gen (pt Z₂).gen

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

abbrev idx0 (ct : At S κ p) : Idx A.H p := ⟨κ.l, κ.c, κ.good p ct.hp⟩

structure DVP (ct : At S κ p) : Type where
  C : SCF p
  K : Subfield ↥C.S
  closed : IsClosed (K : Set ↥C.S)
  dvr : IsDiscreteValuationRing ↥(intO ↥K)
  dense : Dense {x : ↥C.S | IsAlgebraic ↥K x}
  fam : Fam ct.Y (idx0 ct) C
  rat : ∃ w : Sp ↥K ⟶ ct.YY.X, spMap K.subtype ≫ w = (fam.pt ct.YY).gen

variable {ct : At S κ p}

structure Ext (y : DVP ct) : Type where
  L : Subfield ↥y.C.S
  le : y.K ≤ L
  fin : (Subfield.inclusion le).Finite
  π : ↥(intO ↥L)
  irr : Irreducible π

variable {y : DVP ct}

variable {Z : ct.Mdl} {e : Ext y}

end GlobalTheory.LocM.Cht
