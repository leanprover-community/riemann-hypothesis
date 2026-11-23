module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsZeroPtEpsScalePt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open GlobalTheory.TanPtMod

namespace GlobalTheory.UPel.HT.ES.WTors

theorem killedBy_iff_map {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy o w x := by
  constructor
  · intro h a ha
    exact h _ (Ideal.mem_map_of_mem _ ha)
  · intro h a ha
    simp only [GlobalTheory.IwLevel.htAct_act]
    refine Submodule.span_induction (p := fun y _ => x ≫ o.act.act y = 1) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨c, hc, rfl⟩
      exact h c hc
    · have h0 : o.act.act 0 = 1 := by
        have := o.act.add 0 0
        rw [add_zero] at this
        exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
      rw [h0, comp_one]
    · intro y z _ _ hy hz
      rw [o.act.add, comp_mul, hy, hz, _root_.mul_one]
    · intro c y _ hy
      haveI := o.act.hom c
      rw [smul_eq_mul, o.act.mul, ← Category.assoc, hy, one_comp]

end GlobalTheory.UPel.HT.ES.WTors
