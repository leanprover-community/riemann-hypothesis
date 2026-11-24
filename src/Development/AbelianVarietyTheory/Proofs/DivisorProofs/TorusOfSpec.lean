module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
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

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapOrb

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsModelMap (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) : Prop :=
  (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧ (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧
    ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

theorem isModel_iff (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : IsModel w e B u x γ ↔ ∃ ψ, IsModelMap w e B u x γ ψ := Iff.rfl

def pullLat (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : Submodule K.O B.A where
  carrier := {y | ∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E}
  zero_mem' := by
    intro c i
    simp
  add_mem' := by
    intro a b ha hb c i
    rw [smul_add, map_add (f := _), Matrix.mulVec_add, Pi.add_apply]
    exact add_mem (ha c i) (hb c i)
  smul_mem' := by
    intro c' a ha c i
    rw [smul_smul]
    exact ha (c * c') i

def torusOf (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : B.Aˣ :=
  if h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y then h.choose else 1

theorem torusOf_spec (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) (a : B.Aˣ)
    (ha : ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y) : torusOf w B ψ g = a := by
  have h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y := ⟨a, ha⟩
  unfold torusOf
  rw [dite_eq_left h]
  apply Units.ext
  have h1 := h.choose_spec 1
  have h2 := ha 1
  rw [mul_one] at h1 h2
  exact ψ.injective (h1.trans h2.symm)

end GlobalTheory.KapOrb
