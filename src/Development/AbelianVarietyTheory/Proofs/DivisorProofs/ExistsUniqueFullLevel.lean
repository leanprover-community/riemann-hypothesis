module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSympLevel
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullSymplecticLevelStructureOfTateIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullSymplecticLevelStructureUniqueOfLevelsStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem weilIs_unitOn_unique {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {k : Type} [Field k] (x : Sp k ⟶ S) (n : ℤ) (g g' : Over.mk x ⟶ G) (c c' : kˣ)
    (h : Out.WeilIs G L n g g' (unitOn c)) (h' : Out.WeilIs G L n g g' (unitOn c')) : c = c' := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.weilIs_unique_fieldPoint <;> assumption

theorem exists_unique_fullLevel {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (z : kˣ) (hz : IsPrimitiveRoot z l.M')
    (hzA : (z : k) ^ (l.M' / l.A) = β b.ζ) :
    ∃! ev : D.La → (Over.mk x ⟶ o.t.G),
      IsSympLevel D (fun a g => g ≫ o.t.act.act a)
          (fun n g g' c => Out.WeilIs o.t.G o.t.PP.L n g g' (unitOn c)) l.M' z ev ∧
        Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev := by
  obtain ⟨-, I, hIA, hetaA, heta⟩ := o.geom k x β hx
  have hzA' : z ^ (l.M' / l.A) = I.ζ l.A := Units.ext (by rw [Units.val_pow_eq_pow_val, hzA, hIA])
  obtain ⟨ev, hev, hA, hM⟩ := GlobalTheory.T.exists_fullSymplecticLevelStructure_of_tateIso l I hz hzA'
  have hi : Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev :=
    ⟨fun a => (hA a).trans (hetaA a).symm, fun a ha => (hM a ha).trans (heta a ha).symm⟩
  refine ⟨ev, ⟨hev, hi⟩, ?_⟩
  rintro ev' ⟨h1, h2⟩
  have := GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels l (fun g g' c c' => weilIs_unitOn_unique o.t.G o.t.PP.isLB x _ g g' c c') hz
    hev hi h1 h2
  exact this.symm

end GlobalTheory.FullLevel
