module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapEstimateOfPartial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms

theorem bij_of_inj_back {A B : Type} [Finite A] (f : A → B) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    Function.Bijective f := by
  haveI : Finite B := Finite.of_injective g hg
  exact hf.bijective_of_nat_card_le (Nat.card_le_card_of_injective g hg)

theorem stabiliser_bijective_of_injection
    (h : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      ∀ c, ∃ g : (D.mem u).C.stab D.R.m ((D.fm u).til c) → (D.fm u).stabilizer₂ c, Function.Injective g) :
    StabiliserMapBijective := by
  intro D u Ch chOf Tf c
  obtain ⟨g, hg⟩ := h D u Ch chOf Tf c
  exact bij_of_inj_back _ ((D.fm u).stabMap_inj c) g hg

end Formalism.L2.GlobalTheoryTheory.Br
