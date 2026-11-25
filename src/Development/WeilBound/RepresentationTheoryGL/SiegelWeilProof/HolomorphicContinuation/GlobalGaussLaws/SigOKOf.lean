module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigAtLeast
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH

namespace PositivityTheory.Rg.Sw.Glob

theorem cnt_add {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at h
  exact h

theorem sigOK_of (hlt : WittLBlt) (heq : WittLBeq) : SigOK := by
  intro D n V s hr hs
  by_contra hne
  push Not at hne
  choose ε fr hfr hng using hne
  obtain ⟨h1, h2, h3⟩ := hr
  have hb : ∀ τ, V.rank - n ≤ cnt (ε τ) true ∧ V.rank - n ≤ cnt (ε τ) false := by
    intro τ
    have hc := cnt_add (ε τ)
    unfold GoodSig at hng
    have := hng τ
    push Not at this
    obtain ⟨a, b, c, d⟩ := this
    constructor <;> omega
  have hS : SigAtLeast D V (V.rank - n) := fun τ =>
    ⟨ε τ, fr τ, (hfr τ).1, (hfr τ).2.1, (hb τ).1, (hb τ).2⟩
  have hw : V.rank - n ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
    rcases Nat.lt_or_ge (2 * (V.rank - n)) V.rank with h | h
    · exact hlt D V _ h hS
    · exact heq D V _ (by omega) hS
  omega

end PositivityTheory.Rg.Sw.Glob
