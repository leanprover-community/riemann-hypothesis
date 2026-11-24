module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.ShiftLastLetterThresholds
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

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

noncomputable def Wm (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  LinearMap.mulLeft ℚ_[p] (X (Fin.last K, a))

noncomputable def dW (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  (pderiv (Fin.last K, a)).toLinearMap

noncomputable def eulW (p : ℕ) [Fact p.Prime] (K r : ℕ) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  ∑ a : Fin r, Wm p K a ∘ₗ dW p K a

noncomputable def Uop (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  Wm p K a ∘ₗ (((c : ℤ) : ℚ_[p]) • LinearMap.id - eulW p K r) - ∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b

noncomputable def Omega (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (c : ℤ) (ρ : Fin r) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  ∑ a ∈ univ.erase ρ, Uop p LL c (univ.erase ρ) a ∘ₗ dW p K a

def UComm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a s t : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
    LL.vec (Fin.last K) = true → s ∈ Cs → t ∈ Cs →
    glAct p LL (K + 1) s t (Uop p LL c Cs a F) - Uop p LL c Cs a (glAct p LL (K + 1) s t F) =
      if t = a then Uop p LL c Cs s F else 0

def UKeepsLast : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (c : ℤ) (a : Fin r),
    LL.vec (Fin.last K) = true →
    ∀ F ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ), Uop p LL c univ a F ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ)

def UKeepsEarly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r)
    (j : ℕ) (M : WithTop ℤ), j ≤ K →
    ∀ F ∈ YCond p LL j M, Uop p LL c Cs a F ∈ YCond p LL j M

def UDeg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r) (o : ℕ),
    ∀ F ∈ Pol p r (setLast LL o), Uop p LL c Cs a F ∈ Pol p r (setLast LL (o + 1))

def ResU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (ρ a : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), a ≠ ρ →
    initPart (Fin.last K, ρ) 0 (Uop p LL c univ a F) = Uop p LL c (univ.erase ρ) a (initPart (Fin.last K, ρ) 0 F)

def Sl2Injective : Prop :=
  ∀ (k V : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] (e f h : V →ₗ[k] V),
    (∀ x, h (e x) - e (h x) = (2 : k) • e x) → (∀ x, h (f x) - f (h x) = -((2 : k) • f x)) →
    (∀ x, e (f x) - f (e x) = h x) →
    ∀ (u : V) (μ : ℤ) (j : ℕ), h u = ((μ : ℤ) : k) • u → (∃ s : ℕ, (f ^ s) u = 0) → μ + j ≤ 0 → (e ^ j) u = 0 → u = 0

def EArith : Prop :=
  ∀ (s : ℕ) (ka : ℕ → ℤ) (β : ℕ → ℕ) (c : ℤ),
    (∀ i, i + 1 < s → ka (i + 1) + β (i + 1) ≤ ka i) → (0 < s → ka 0 + β 0 ≤ c) →
    1 ≤ ∑ a ∈ range s, β a →
    0 < (c - (∑ a ∈ range s, (β a : ℤ)) + 1) * (∑ a ∈ range s, (β a : ℤ)) - (∑ a ∈ range s, (β a : ℤ) * ka a) +
      ∑ b ∈ range s, ∑ a ∈ range b, ((β a : ℤ) + 1) * (β b : ℤ)

def OmegaInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (ρ : Fin r) (c : ℤ) (o : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true →
    ∀ x ∈ Pol p r (setLast LL (o + 1)) ⊓ FreeOf p (Fin.last K, ρ) ⊓
        TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ),
      Omega p LL c ρ x = 0 → x = 0

end Formalism.InvariantFactorPaths.L4
