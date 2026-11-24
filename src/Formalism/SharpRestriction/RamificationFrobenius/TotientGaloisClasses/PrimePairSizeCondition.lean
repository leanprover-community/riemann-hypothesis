module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Mathlib.NumberTheory.DirichletCharacter.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.HC

structure PChar where
  N : ℕ
  [ne : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive

attribute [instance] PChar.ne

namespace PChar

def val (ψ : PChar) (a : ℕ) : ℂ := ψ.χ (a : ZMod ψ.N)

def one : PChar := ⟨1, 1, DirichletCharacter.isPrimitive_one_level_one⟩

def inv (ψ : PChar) : PChar :=
  ⟨ψ.N, ψ.χ⁻¹, by
    have h : ψ.χ.conductor = ψ.N := ψ.prim
    exact (DirichletCharacter.conductor_inv ψ.χ).trans h⟩

def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PChar :=
  @PChar.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

def IsReal (ψ : PChar) : Prop := ∀ a : ZMod ψ.N, (ψ.χ a).im = 0

end PChar

structure KSet where
  KEPT : Finset PChar
  one_mem : PChar.one ∈ KEPT
  inv_mem : ∀ ψ ∈ KEPT, ψ.inv ∈ KEPT

  psK : Option PChar
  psK_spec : ∀ ψ, psK = some ψ → ψ ∈ KEPT ∧ ψ.χ.Odd ∧ ψ.IsReal

structure HType extends KSet where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  J : ℕ
  one_le_J : 1 ≤ J
  P0 : ℕ
  P0_pos : 0 < P0

  t : ℝ → ℕ
  Ct : ℝ
  t_le : ∀ x : ℝ, 1 ≤ x → (t x : ℝ) ≤ x ^ Ct

namespace HType

variable (T : HType)

end HType

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

theorem condN_pos : 0 < H.condN :=
  Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos

instance condN_neZero : NeZero H.condN := ⟨H.condN_pos.ne'⟩

end HostRaw

end Formalism.HC

end
