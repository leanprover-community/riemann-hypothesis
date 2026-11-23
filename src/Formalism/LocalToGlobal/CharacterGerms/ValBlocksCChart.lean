module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjugate
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

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

section Gen

variable {d : ℕ} [NeZero d] (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

abbrev rdS (o : Orb) : RowData C V d (fun _ => I0 o) (JJ fun _ => I0 o) := (Y.rawSelf (p o)).rowData (H o)

def imgFamS {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : Set (∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

theorem valO_self (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n)
    {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : ValO (fun o => rdS Y p H o) N (imgFamS Y p Ls n pl) ν := by
  rintro Po ⟨P, hP, hQ⟩ kind hk S t ht gr hg
  have key := val_self (hs := hs) (hv := hv) (N := N) (pl := pl) (P := P) (hP := hP) (Po := Po) (hQ := hQ)
    (kind := kind) (hk := hk) (S := S) (t := t) (ht := ht) (gr := gr) (hg := hg)
  exact WithBot.coe_le_coe.1 (hν.trans key)

end Gen

section Two

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y 2 (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

end Two

end Formalism.L2.FormalSeriesBounds.RF
