module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colView_of_built {𝒮 : GlobalTheory.Mem.Top.Bl.Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (b : GlobalTheory.Mem.Top.Bl.Built 𝒮 K w Z c) : ColView w Z c.O.tw c.O.nch :=
  { jets := b.pin.jets
    rowInt := b.what₂.rowInt
    tw_eq := congrArg (fun s => s.2.2.1) b.ker_eq
    tup := ⟨b.n.tp, b.n.xi⟩ }

theorem overCols_built : ∀ 𝒮 : Slots, OverCols (IsBuilt 𝒮) ∧ ∀ P : CP, (∀ K B f T w Z c, P K B f T w Z c → BuiltC 𝒮 K B f T w Z c) →
    OverCols (positionOf P) := by
  intro 𝒮
  have key : ∀ P : CP, (∀ K B f T w Z c, P K B f T w Z c → BuiltC 𝒮 K B f T w Z c) → OverCols (positionOf P) :=
    fun P hP K X f T c hc =>
      positionOf_mono (fun K B f T w Z c h => let ⟨b⟩ := hP K B f T w Z c h; colView_of_built b) K X f T c hc
  exact ⟨key (BuiltC 𝒮) fun _ _ _ _ _ _ _ h => h, key⟩

end GlobalTheory.Fc.Cv

end
