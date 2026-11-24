module

public import Formalism.MahlerMeasure.CsSaturated
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

def setLast {K : ℕ} (LL : Letters (K + 1)) (o : ℕ) : Letters (K + 1) where
  vec := LL.vec
  deg := Function.update LL.deg (Fin.last K) o

def shiftLastLetterThresholds (K : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (e : ℕ) : Fin q → WithTop ℤ :=
  fun k => if K + 1 ≤ J k then M k + ((-(e : ℤ) : ℤ) : WithTop ℤ) else M k

def shiftWt {r : ℕ} (w : Fin r → ℤ) (ρ : Fin r) (e : ℕ) : Fin r → ℤ :=
  Function.update w ρ (w ρ - e)

noncomputable def FreeOf (p : ℕ) [Fact p.Prime] {σ : Type} (v : σ) : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p] {m | m v = 0}

noncomputable def TypesLE (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (M : WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (la : Fin r → ℤ) (_ : ((la 0 : ℤ) : WithTop ℤ) ≤ M), IsoC p LL j Cs la

noncomputable def XSp (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  Pol p r LL ⊓ FreeOf p (Fin.last K, ρ) ⊓
    ⨅ k, (if K + 1 ≤ J k then YCond p LL K (M k) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) (M k)
      else YCond p LL (J k) (M k))

noncomputable def XH (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  XSp p LL J M ρ ⊓ HWC p LL (K + 1) (univ.erase ρ) w ⊓ WtSpC p LL (K + 1) univ w

def ResOntoK (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Prop :=
  ∀ x ∈ XSp p LL J M ρ, ∃ h ∈ Y p LL J M, initPart (Fin.last K, ρ) 0 h = x

noncomputable def grSpan (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ) :
    Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  Submodule.span ℚ_[p] (grLat p LLw J M ρ w (Fin.last K, ρ) e : Set (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]))

def ProjAt (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e D : ℕ) : Prop :=
  ∃ Pr : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
    ∀ m : Fin (K + 1) × Fin r →₀ ℕ, MultiDeg LLw m →
      Pr (monomial m 1) ∈ grSpan p LLw J M ρ w e ∧
      ((p : ℚ_[p]) ^ D) • Pr (monomial m 1) ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      ∀ g ∈ grSpan p LLw J M ρ w e, fock p g (Pr (monomial m 1)) = fock p g (monomial m 1)

def SatAt (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e c : ℕ) : Prop :=
  ∀ x ∈ grSpan p LLw J M ρ w e, x ∈ IntPol p (Fin (K + 1) × Fin r) →
    ((p : ℚ_[p]) ^ c) • x ∈ grLat p LLw J M ρ w (Fin.last K, ρ) e

end Formalism.InvariantFactorPaths.L4
