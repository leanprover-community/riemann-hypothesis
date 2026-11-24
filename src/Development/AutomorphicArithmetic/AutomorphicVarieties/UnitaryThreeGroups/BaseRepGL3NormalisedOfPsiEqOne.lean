module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.V.U3

open Matrix

section Shape

variable {G : Type*} [Group G] {R : Type*} [CommRing R]

def HasMult {m : ℕ} (η : G →* ℤˣ) (r : G →* GG (m := m) (R := R)) : Prop := ∀ g, (r g).right = η g

def zeta (c g₁ : G) (r : G →* GG (m := 3) (R := R)) : R := zmat c g₁ r 0 0

def MatIrr {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ W : Submodule R (Fin m → R), (∀ g ∈ H, ∀ v ∈ W, a g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

def mats {m : ℕ} (r : G →* GG (m := m) (R := R)) (g : G) : Matrix (Fin m) (Fin m) R := (r g).mat

def TypeI (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop := MatIrr η.ker (mats r)

def Upper (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop := ∀ g ∈ η.ker, ∀ a b, wt a b < 0 → (r g).mat a b = 0

def Lower (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop := ∀ g ∈ η.ker, ∀ a b, 0 < wt a b → (r g).mat a b = 0

def Block (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop := ∀ g ∈ η.ker, ∀ a b, Odd (wt a b) → (r g).mat a b = 0

def corner (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 2) (Fin 2) R := X.submatrix ![0, 2] ![0, 2]

def TypeII (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) : Prop :=
  Block η r ∧ MatIrr η.ker fun g => corner (r g).mat

def Wfun (r : G →* GG (m := 3) (R := R)) (g : G) : Matrix (Fin 2) (Fin 2) R :=
  if (r g).right = 1 then corner (r g).mat else corner (r g).mat * Matrix.diagonal ![-1, 1]

def MatIso {m : ℕ} (H : Subgroup G) (a a' : G → Matrix (Fin m) (Fin m) R) : Prop :=
  ∃ M : GL (Fin m) R, ∀ g ∈ H, (M : Matrix (Fin m) (Fin m) R) * a g = a' g * M

end Shape

section Deform

variable {G : Type*} [Group G] {C : Type*} [CommRing C] {m : ℕ}

def IsCoc (r : G →* GG (m := m) (R := C)) (γ : G → Matrix (Fin m) (Fin m) C) : Prop :=
  ∀ g h, γ (g * h) = γ g + adRep r g (γ h)

def EntIn (I : Ideal C) (X : Matrix (Fin m) (Fin m) C) : Prop := ∀ a b, X a b ∈ I

def IsDeform (r : G →* GG (m := m) (R := C)) (γ : G → Matrix (Fin m) (Fin m) C) (r' : G →* GG (m := m) (R := C)) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ (r' g).mat = (1 + γ g) * (r g).mat

def zvar (c g₁ : G) (r : G →* GG (m := 3) (R := C)) (γ : G → Matrix (Fin 3) (Fin 3) C) : Matrix (Fin 3) (Fin 3) C :=
  γ g₁ * (r g₁).mat - γ (gstar c g₁) * (r (gstar c g₁)).mat

structure NormCoc (c g₁ : G) (r : G →* GG (m := 3) (R := C)) (γ : G → Matrix (Fin 3) (Fin 3) C) : Prop where
  atc : γ c = 0
  z12 : zvar c g₁ r γ 0 1 = 0
  z21 : zvar c g₁ r γ 1 0 = 0

def cob (r : G →* GG (m := m) (R := C)) (X : Matrix (Fin m) (Fin m) C) (g : G) : Matrix (Fin m) (Fin m) C :=
  X - adRep r g X

def CongOne (I : Ideal C) (h : GL (Fin m) C) : Prop := EntIn I ((h : Matrix (Fin m) (Fin m) C) - 1)

end Deform

structure Marks {G : Type*} [Group G] {k : Type*} [CommRing k] (η : G →* ℤˣ) (Ψ : G →* kˣ) (c g₁ : G) : Prop where
  csq : c * c = 1
  ηc : η c = -1
  Ψc : Ψ c = 1
  ηg : η g₁ = 1
  Ψg : IsUnit (((Ψ g₁ : kˣ) : k) ^ 2 - 1)

theorem hasSimilitudeFactor_diagonalRepr {G : Type*} [Group G] {R : Type*} [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) :
    HasMult η (r0 η Ψ) := fun _ => rfl

theorem baseRepGL3_normalised_of_psi_eq_one {G : Type*} [Group G] {R : Type*} [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ)
    {c : G} (g₁ : G) (hc : Ψ c = 1) : Normalised c g₁ (r0 η Ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · show Matrix.diagonal (fun i => ((Ψ c ^ wt1 i : Rˣ) : R)) = 1
    rw [hc]
    simp
  · show Matrix.diagonal _ 0 1 - Matrix.diagonal _ 0 1 = (0 : R)
    simp
  · show Matrix.diagonal _ 1 0 - Matrix.diagonal _ 1 0 = (0 : R)
    simp

end UpperTheory.V.U3
