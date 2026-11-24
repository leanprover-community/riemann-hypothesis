module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc.LgModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

variable {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q' R : V4.Slot} {Bd : BdT} {Lk : LkT Bd}

theorem ev_all {p : Ctx → Prop} (h : ∀ K, p K) : Ev p :=
  ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0,
    fun K _ _ _ _ _ => h K⟩⟩⟩⟩⟩

def LgAt (KP : ∀ B : Base, Fr B.toPre → Prop) (Q R : V4.Slot) (K : Ctx) : Prop :=
  large₂ K fun B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

theorem largeBaseProperty_conditional : LargeBaseCondition KP Q fun K X f T c => LgAt KP Q R K → R K X f T c :=
  ev_all fun K => by
    by_cases h : LgAt KP Q R K
    · exact large₂.imp h fun _ _ _ _ t k C W V S N G c q _ => t k C W V S N G c q
    · exact GroupRetwisting.lg_all K fun _ _ _ _ _ _ _ _ _ _ _ _ _ a => (h a).elim

theorem rowL_of_good {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (h : GroupRetwisting.LargeBaseConditionG KP Q R) (hr : Row (sAnd Q' R) Lk H) :
    RowL KP Q Q' Lk H := by
  obtain ⟨E, e, hH⟩ := hr
  refine ⟨_, largeBaseProperty_conditional (R := R), fun κ D O c b => Built (sAnd Q' R) Lk κ D O c b ∧ E κ D O c b,
    ((EvP.of_evGd h).and e).mono fun _ _ hk t β q c b l =>
      ⟨Built.intro hk ⟨q.1, q.2 t.1⟩ l, t.2 β ⟨q.1, q.2 t.1⟩ c b l⟩, fun 𝒜 σ s => hH 𝒜 σ fun Fm hc => ?_⟩
  obtain ⟨κ, a, b, t⟩ := s Fm hc
  exact ⟨κ, a, b, fun x hx i => (t x hx i).2⟩

end GlobalTheory.Fc.LgModel

end
