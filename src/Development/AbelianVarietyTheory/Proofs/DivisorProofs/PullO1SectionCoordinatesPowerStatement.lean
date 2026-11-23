module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullO1SectionCoordinatesPower
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pull_O1_section_coordinates_power : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (I : Type) [Finite I] (th : I → Ω) (δ : LB M.Z) (t : I → δ.Sec) (N D : ℕ) (e : Fin (N + 1) → Ω) (h : M.Z ⟶ PSpace o N), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → SecCoord δ t M.pt th → PCrd (M.pt ≫ h) e → SameScale M th e D → LBIso ((GlobalTheory.ProjSpace.O1 o N).pull h) (lbPow δ D) := by
  first | exact @GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow | exact GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow | (intros; apply GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow <;> assumption)
