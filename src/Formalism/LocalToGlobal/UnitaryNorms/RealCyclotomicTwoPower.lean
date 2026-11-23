module

public import Formalism.FrobeniusOrbits.Statement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open IntermediateField NumberField

namespace Formalism.L2.Host

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

abbrev Qb : Type := AlgebraicClosure ℚ

abbrev Fld : Type := IntermediateField ℚ Qb

def sqrts (m : ℤ) : Set Qb := {z | z ^ 2 = (m : Qb)}

def mus (N : ℕ) : Set Qb := {z | z ^ N = 1}

def sqQ (m : ℤ) : Fld := adjoin ℚ (sqrts m)

def cycQ (N : ℕ) : Fld := adjoin ℚ (mus N)

def cycQplus (N : ℕ) : Fld := adjoin ℚ ((fun z => z + z⁻¹) '' mus N)

def KQ (d : ℕ) : Fld := sqQ (-(d : ℤ))

def biquadraticField (q d : ℕ) : Fld := sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ))

def realCyclotomicTwoPower (e : ℕ) : Fld := cycQplus (2 ^ (e + 2))

def EQ (e q d : ℕ) : Fld := biquadraticField q d ⊔ realCyclotomicTwoPower e

def FQ (e q d : ℕ) : Fld := sqQ ((q : ℤ) * (d : ℤ)) ⊔ realCyclotomicTwoPower e

abbrev GalOf (L : Fld) : Subgroup (Qb ≃ₐ[ℚ] Qb) := L.fixingSubgroup

def restr (L : Fld) (s : Qb ≃ₐ[ℚ] Qb) : L →ₐ[ℚ] Qb := (s : Qb →ₐ[ℚ] Qb).comp L.val

def ActsAs (e q d : ℕ) (s : EQ e q d →ₐ[ℚ] Qb) (g : GG e) : Prop :=
  (∀ x : EQ e q d, (x : Qb) ∈ sqrts (-(q : ℤ)) → s x = (((g.1.1 : ℤˣ) : ℤ) : Qb) * x) ∧
  (∀ x : EQ e q d, (x : Qb) ∈ sqrts (-(d : ℤ)) → s x = (((g.1.2 : ℤˣ) : ℤ) : Qb) * x) ∧
  ∃ u : (ZMod (2 ^ (e + 2)))ˣ, hcl e u = g.2 ∧
    ∀ (x : EQ e q d) (z : Qb), z ∈ mus (2 ^ (e + 2)) → (x : Qb) = z + z⁻¹ →
      s x = z ^ (u : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val

def condN (e q d : ℕ) : ℕ := 2 ^ (e + 2) * q * d

def IsCond (L : Fld) (N : ℕ) : Prop := L ≤ cycQ N ∧ ∀ M : ℕ, 0 < M → L ≤ cycQ M → N ∣ M


open Classical in
def sqSign {p : ℕ} (u : (ZMod p)ˣ) : ℤˣ := if IsSquare (u : ZMod p) then 1 else -1

theorem q_dvd_condN (e q d : ℕ) : q ∣ condN e q d := by
  unfold condN
  exact dvd_mul_of_dvd_left (dvd_mul_left q _) d
theorem d_dvd_condN (e q d : ℕ) : d ∣ condN e q d := by
  unfold condN
  exact dvd_mul_left d _
theorem two_pow_dvd_condN (e q d : ℕ) : 2 ^ (e + 2) ∣ condN e q d := by
  unfold condN
  exact dvd_mul_of_dvd_left (dvd_mul_right _ q) d

def CondEQ (e q d : ℕ) : Prop := IsCond (EQ e q d) (condN e q d)

end Formalism.L2.Host
