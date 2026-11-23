module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

abbrev Form (R : Type*) (n : ℕ) := Finset (Fin n) → R

def sg {n : ℕ} (I : Finset (Fin n)) (m : Fin n) : ℤ := (-1) ^ (I.filter fun j => m < j).card

variable {R : Type*} [CommRing R] {n : ℕ}

def oneF : Form R n := fun I => if I = ∅ then 1 else 0

def wedgeF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ I, ((sg I m : ℤ) : R) * K (I.erase m) * X m

def contrF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ Iᶜ, ((sg I m : ℤ) : R) * X m * K (insert m I)

def stepF (up : Bool) (K : Form R n) (X : Fin n → R) : Form R n :=
  if up then wedgeF K X else contrF K X

variable {ι : Type*}

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
