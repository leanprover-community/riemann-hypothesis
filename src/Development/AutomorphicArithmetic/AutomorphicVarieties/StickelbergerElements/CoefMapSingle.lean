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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace UpperTheory.V.B4

open UpperTheory.V.Bern

def Ek (M k : ℕ) (b : ZMod M) : ℚ := bcoef M k b.val / k

def yCl {M : ℕ} (a : ℕ) (b : ZMod M) : ZMod M := (a : ZMod M)⁻¹ * b

def jv (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) * (yCl a b).val - b.val) / M

def Eone (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) - 1) / 2 - jv M a b

def ck (l k : ℕ) : ℕ := padicValNat l (2 * k * primorial (k + 1))

def Zl (l : ℕ) [Fact l.Prime] : Subring ℚ where
  carrier := {x | ¬ l ∣ x.den}
  zero_mem' := by simpa using (Fact.out : l.Prime).ne_one
  one_mem' := by simpa using (Fact.out : l.Prime).ne_one
  add_mem' {x y} hx hy h := ((Fact.out : l.Prime).dvd_mul.1 (h.trans (Rat.add_den_dvd x y))).elim hx hy
  mul_mem' {x y} hx hy h := ((Fact.out : l.Prime).dvd_mul.1 (h.trans (Rat.mul_den_dvd x y))).elim hx hy
  neg_mem' {x} hx := by simpa using hx

theorem mem_Zl {l : ℕ} [Fact l.Prime] {x : ℚ} : x ∈ Zl l ↔ ¬ l ∣ x.den := Iff.rfl

section Elements

variable {M : ℕ} [NeZero M] {Γ : Type} [CommGroup Γ]

def sumEl {R : Type} [CommRing R] (φ : (ZMod M)ˣ →* Γ) (f : ZMod M → R) : MonoidAlgebra R Γ :=
  ∑ b : (ZMod M)ˣ, MonoidAlgebra.single (φ b)⁻¹ (f b)

def thetaEl (k : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ := -sumEl φ (Ek M k)

def yEl (k a : ℕ) (ha : a.Coprime M) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ :=
  (1 - MonoidAlgebra.single (φ (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℚ) ^ k)) * thetaEl k φ

def xEl (a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ (Eone M a)

def ytEl (e a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ fun b => (b.val : ℤ) ^ e * Eone M a b

end Elements

section Maps

variable {G Γ : Type} [CommGroup G] [CommGroup Γ]

def coefMap (R Γ : Type) [CommRing R] [CommGroup Γ] : MonoidAlgebra ℤ Γ →+* MonoidAlgebra R Γ :=
  (MonoidAlgebra.lift ℤ (MonoidAlgebra R Γ) Γ (MonoidAlgebra.of R Γ)).toRingHom

theorem coefMap_single (R : Type) [CommRing R] (g : Γ) (n : ℤ) :
    coefMap R Γ (MonoidAlgebra.single g n) = MonoidAlgebra.single g (n : R) := by
  simp [coefMap, MonoidAlgebra.smul_single]

def IntAt (l : ℕ) [Fact l.Prime] (r : ℕ) (z : MonoidAlgebra ℚ Γ) : Prop := ∀ g, z.coeff g / (l : ℚ) ^ r ∈ Zl l

end Maps

end UpperTheory.V.B4

end
