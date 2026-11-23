module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.QuantumMinorsCasimir

noncomputable def GlRel.{u_1} : {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop := fun {A} [Ring A] {n} E =>
  ∀ (a b c d : Fin n), E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - if d = a then E c b else 0

noncomputable def Tm.{u_1} : {A : Type u_1} → [inst : Ring A] → [Algebra ℂ A] → {n : ℕ} → (Fin n → Fin n → A) → ℂ → Fin n → Fin n → A := fun {A} [Ring A] [Algebra ℂ A] {n} E u a b => (if a = b then (algebraMap ℂ A) u else 0) + E a b

noncomputable def qminor.{u_1} : {A : Type u_1} →
  [inst : Ring A] → [Algebra ℂ A] → {n t : ℕ} → (Fin n → Fin n → A) → (Fin t → Fin n) → (Fin t → Fin n) → ℂ → A := fun {A} [Ring A] [Algebra ℂ A] {n t} E a b u =>
  ∑ σ,
    ↑↑(Equiv.Perm.sign σ) *
      (List.ofFn fun k => Tm E (u - ↑↑k) (a (σ k)) (b k)).prod

noncomputable def qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor E (id : Fin n → Fin n) id u

theorem casimir : ∀ {V : Type} [inst : AddCommGroup V]
  [inst_1 : Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V),
  GlRel E →
    ∀ (k : ℂ) (φ : V),
      (E 0 0) φ + (E 1 1) φ = 0 →
        (E 0 1) φ - (E 1 0) φ = (Complex.I * k) • φ →
          (E 0 0) φ - (E 1 1) φ = Complex.I • ((E 0 1) φ + (E 1 0) φ) →
            ∀ (u : ℂ),
              (qdet E (u + 1 / 2)) φ =
                ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ := by
  intro V _ _ E h k φ h1 h2 h3 u
  have hq : ∀ v : ℂ, qdet E v φ =
      (v * (v - 1)) • φ + v • E 1 1 φ + (v - 1) • E 0 0 φ + E 0 0 (E 1 1 φ) - E 1 0 (E 0 1 φ) := by
    intro v
    have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
    have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
    unfold qdet qminor Tm
    rw [hu, Finset.sum_pair hne]
    simp [List.ofFn_succ, Module.algebraMap_end_apply]
    module
  have c (a b c d : Fin 2) := congrArg (fun f : Module.End ℂ V => f φ) (h a b c d)
  have cad := c 0 0 1 1
  have cab := c 0 0 0 1
  have cac := c 0 0 1 0
  have cdb := c 1 1 0 1
  have cdc := c 1 1 1 0
  have cbc := c 0 1 1 0
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, Fin.zero_eq_one_iff,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, LinearMap.zero_apply] at cad cab cac cdb cdc cbc
  have z (a b : Fin 2) := congrArg (E a b) h1
  have w (a b : Fin 2) := congrArg (E a b) h2
  have g (a b : Fin 2) := congrArg (E a b) h3
  simp only [map_add (f := _), map_sub, map_smul, map_zero] at z w g
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hq]
  linear_combination (norm := skip) u • h1 + (1 / 4 : ℂ) • (z 0 0 + z 1 1 - (g 0 0 - g 1 1)
    - Complex.I • (g 0 1 + g 1 0) - (2 * Complex.I) • h2 + (w 0 1 - w 1 0) + (Complex.I * k) • h2
    + (2 : ℂ) • cad - Complex.I • (cab + cac - cdb - cdc) + (2 : ℂ) • cbc)
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end UpperTheory.Reformulated.B.QuantumMinorsCasimir
