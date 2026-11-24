module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
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
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

def crysAct (o₀ : GlobalTheory.UPel.HT.Obj b N t) : D.O →+* Module.End k (HdR o₀.A) :=
  RingHom.mk'
    { toFun x := haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)
      map_one' := by
        haveI := o₀.act.hom 1
        exact (push_congr (dp0 k) (𝟙 _) o₀.act.one).trans (push_id (dp0 k) (𝟙 _))
      map_mul' x y := by
        haveI := o₀.act.hom
        exact (push_congr (dp0 k) (𝟙 _) (o₀.act.mul x y)).trans (push_comp (dp0 k) (𝟙 _) _ _) }
    fun x y ↦ by
      haveI := o₀.act.hom
      haveI : IsMonHom (o₀.act.act x * o₀.act.act y) := o₀.act.add x y ▸ o₀.act.hom _
      exact (push_congr (dp0 k) (𝟙 _) (o₀.act.add x y)).trans (push_mul (dp0 k) (𝟙 _) _ _)

theorem crysAct_apply (o₀ : GlobalTheory.UPel.HT.Obj b N t) (x : D.O) :
    crysAct o₀ x = (haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)) := rfl

def rhoPart (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1)

def lieZ (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → 𝓞 D.F) (y : HdR o₀.A), y ∈ rhoPart o₀ β ∧
    (∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) ∧ z = ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y}

end GlobalTheory.HTCount
