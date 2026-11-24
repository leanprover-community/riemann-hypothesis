module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Finset

namespace UpperTheory.V.Stk

open UpperTheory.V.Bern

def Ev (M k : ℕ) (b : ZMod M) : ℚ := bcoef M k b.val / k

def yCl {M : ℕ} (a : ℕ) (b : ZMod M) : ZMod M := (a : ZMod M)⁻¹ * b

def Eva (M k a : ℕ) (b : ZMod M) : ℚ := Ev M k b - (a : ℚ) ^ k * Ev M k (yCl a b)

def jv (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) * (yCl a b).val - b.val) / M

def Eone (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) - 1) / 2 - jv M a b

def dk (k : ℕ) : ℕ := 2 * k * primorial (k + 1)

theorem dk_pos {k : ℕ} (hk : 0 < k) : 0 < dk k := by
  unfold dk
  exact Nat.mul_pos (by omega) (primorial_pos _)

section Elements

variable {M : ℕ} [NeZero M] {Γ : Type} [Group Γ]

def sumEl {R : Type} [CommRing R] (φ : (ZMod M)ˣ →* Γ) (f : ZMod M → R) : MonoidAlgebra R Γ :=
  ∑ b : (ZMod M)ˣ, MonoidAlgebra.single (φ b)⁻¹ (f b)

def yForm (k a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ := -sumEl φ (Eva M k a)

def xEl (a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ (Eone M a)

def ytEl (e a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ fun b => (b.val : ℤ) ^ e * Eone M a b

end Elements

section Maps

variable {G Γ : Type} [Group G] [Group Γ]

abbrev cf (R Γ : Type) [CommRing R] [Group Γ] : MonoidAlgebra ℤ Γ →+* MonoidAlgebra R Γ :=
  MonoidAlgebra.mapRingHom Γ (Int.castRingHom R)

theorem cf_single (R : Type) [CommRing R] (g : Γ) (n : ℤ) :
    cf R Γ (MonoidAlgebra.single g n) = MonoidAlgebra.single g (n : R) := by
  simp [cf]

theorem cf_sumEl (R : Type) [CommRing R] {M : ℕ} [NeZero M] (φ : (ZMod M)ˣ →* Γ) (f : ZMod M → ℤ) :
    cf R Γ (sumEl φ f) = sumEl φ fun b => (f b : R) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumEl, map_sum, cf_single]

theorem sumEl_add {R : Type} [CommRing R] {M : ℕ} [NeZero M] (φ : (ZMod M)ˣ →* Γ) (f g : ZMod M → R) :
    sumEl φ (fun b => f b + g b) = sumEl φ f + sumEl φ g := by
  simp only [sumEl, MonoidAlgebra.single_add, Finset.sum_add_distrib]

end Maps

end UpperTheory.V.Stk

end
