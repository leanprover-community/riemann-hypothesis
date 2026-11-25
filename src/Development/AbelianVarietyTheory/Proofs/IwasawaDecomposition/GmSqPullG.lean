module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SqLevel

open TopologicalSpace

variable {X : Scheme.{0}}

abbrev sqLB (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {L : LB X} {x : X} {J : Fin 1 → L.ι} : x ∈ (sqLB L).U J ↔ x ∈ L.U (J 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_sq_pull {Y : Scheme.{0}} {L : LB X} {F : Y ⟶ X} {y : Y} {J : PUnit → Fin 1 → L.ι} :
    y ∈ ((sqLB L).pull F).U J ↔ F y ∈ L.U (J PUnit.unit 0) :=
  mem_pull.trans mem_sq

variable {B G E : Scheme.{0}} {M : LB B} {L : LB G} {p : E ⟶ B} {f : E ⟶ G}

theorem sqIso_le (q : (PUnit → Fin 1 → M.ι) × (PUnit → Fin 1 → L.ι)) :
    ((sqLB M).pull p).U q.1 ⊓ ((sqLB L).pull f).U q.2 ≤
      (M.pull p).U (fun _ => q.1 PUnit.unit 0) ⊓ (L.pull f).U (fun _ => q.2 PUnit.unit 0) :=
  fun _ h => ⟨mem_pull.2 (mem_sq_pull.1 h.1), mem_pull.2 (mem_sq_pull.1 h.2)⟩

def sqIso (w : LB.Iso (L.pull f) (M.pull p)) : LB.Iso ((sqLB L).pull f) ((sqLB M).pull p) :=
  ⟨fun q => res (sqIso_le q) (w.s (fun _ => q.1 PUnit.unit 0, fun _ => q.2 PUnit.unit 0)) ^ 2⟩

end GlobalTheory.SqLevel
