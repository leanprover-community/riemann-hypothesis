module

public import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjugate
public import Formalism.LocalToGlobal.CharacterGerms.RowTieVal
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

abbrev IIof {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (o : Orb) (g : Fin 2) : Type :=
  Σ t : ZMod d, Fin (r (tau o g t))

section Defs

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
  {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]

def blkProd (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt (X := X) L o i)) → Fin n) : MvPolynomial (Fin n × WVO I) C :=
  ∏ o, toAll o (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o))

end Defs

section Mem

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (O : Subring C) (n : ℕ)

variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]

end Mem

end Formalism.L2.FormalSeriesBounds.RF
