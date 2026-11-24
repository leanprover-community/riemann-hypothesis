module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.GradeZeroInterpolatingElement

def dimL (j : ℤ × ℤ) : ℕ :=
  if j = wAl ∨ j = wBe ∨ j = wPs ∨ j = wTh ∨ j = 0 then 2 else if j ∈ wts then 1 else 0

def dimP (j : ℤ × ℤ) : ℕ := if j = 0 then 2 else if j ∈ wts then 1 else 0

namespace Raw

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)

section

variable {R : Type} [CommRing R] [Algebra c.O R]

def eqL (ρ : D.Gp l →* M4 R) : Prop :=
  (∀ g : D.Gp l, IsGSp (algebraMap c.O R (D.th g)) (ρ g)) ∧
    Ord ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O R (D.ps i g)) D.s0 ρ

def eqP (p : ℕ) (ρ : D.Gp p →* M4 R) : Prop :=
  (∀ g : D.Gp p, IsGSp (algebraMap c.O R (D.th g)) (ρ g)) ∧ ∀ g : D.Gp p, (g : G ℚ Ω) ∈ D.Ip p ⊓ D.ψ.ker → ρ g = 1

end

abbrev LocEq (v : ℕ) : Type 1 := ∀ (R : Type) [CommRing R] [Algebra c.O R], (D.Gp v →* M4 R) → Prop

def tanSet (v : ℕ) (P : D.LocEq v) (w : ℤ × ℤ) : Set (D.Gp v → M4 c.O) :=
  {z | (∀ g, z g ∈ spW c.O w) ∧ (∀ i j, AdicCont (maximalIdeal c.O) fun g => z g i j) ∧
    ∃ ρ : D.Gp v →* M4 (DualNumber c.O), P _ ρ ∧
      ∀ (g : D.Gp v) i j, (ρ g i j).fst = D.r0 g i j ∧ (ρ g i j).snd = (z g * D.r0 g) i j}

end Raw

end UpperTheory.V.GradeZeroInterpolatingElement

end
