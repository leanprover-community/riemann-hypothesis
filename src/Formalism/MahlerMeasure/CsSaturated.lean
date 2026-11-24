module

public import Formalism.MahlerMeasure.HasOrder
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

namespace Formalism.GM.M

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def WtSpC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p] {m | ∀ c ∈ Cs, wt LL j c m = la c}

def GlStableC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Prop :=
  ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S

noncomputable def HWC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  WtSpC p LL j Cs la ⊓ ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ Cs ∧ d ∈ Cs ∧ c < d), LinearMap.ker (glAct p LL j c d)

noncomputable def IsoC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {S | HWC p LL j Cs la ≤ S ∧ GlStableC p LL j Cs S}

def CsSaturated {r : ℕ} (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ)) : Prop :=
  ∀ la la', (∀ c ∈ Cs, la c = la' c) → (la ∈ T ↔ la' ∈ T)

def IsTypeProj (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop :=
  P ∘ₗ P = P ∧ LinearMap.range P = ⨆ (la : Fin r → ℤ) (_ : la ∈ T), IsoC p LL j Cs la ∧
    LinearMap.ker P = ⨆ (la : Fin r → ℤ) (_ : la ∉ T), IsoC p LL j Cs la

noncomputable def WeylLat (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {L | h ∈ L ∧ ∀ c d : Fin r, c ≠ d → ∀ k : ℕ, ∀ x ∈ L,
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈ L}

noncomputable def MMw (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  Y p LLw J M ⊓ HWC p LLw K (univ.erase ρ) w ⊓ WtSpC p LLw K univ w

noncomputable def MMwZ (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  (MMw p LLw J M ρ w).restrictScalars ℤ_[p] ⊓ IntPol p (Fin K × Fin r)

noncomputable def FilE (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (v : Fin K × Fin r) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  MMwZ p LLw J M ρ w ⊓ (MvPolynomial.restrictSupport ℚ_[p] {m | e ≤ m v}).restrictScalars ℤ_[p]

noncomputable def grLat (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (v : Fin K × Fin r) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  Submodule.span ℤ_[p] (initPart v e '' (FilE p LLw J M ρ w v e : Set (MvPolynomial (Fin K × Fin r) ℚ_[p])))

end Formalism.GM.M
