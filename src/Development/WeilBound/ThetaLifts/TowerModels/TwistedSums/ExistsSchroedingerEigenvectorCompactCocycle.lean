module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterCocycleTrivialNearZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.VacLoc
open _root_.GlobalTheory

theorem exists_twisted_sum_ne_zero : ∀ {G Y X : Type} [AddCommGroup G] [Fintype G] [AddCommGroup Y] [AddCommGroup X] [Module ℂ X]
    (θ : Y → AddChar G ℂ), (∀ w w', θ (w + w') = θ w * θ w') → (∀ a : G, (∀ w, θ w a = 1) → a = 0) →
    ∀ c : G → X, c 0 ≠ 0 → ∃ w, ∑ a, θ w a • c a ≠ 0 := by
  intro G Y X _ _ _ _ _ θ hθ hsep c hc0
  classical
  by_contra hall
  push_neg at hall
  have h1 : θ 0 = 1 := by
    have := hθ 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := θ 0) (by rw [mul_one]; exact this.symm)
  let S : Subgroup (AddChar G ℂ) :=
    { carrier := Set.range θ
      one_mem' := ⟨0, h1⟩
      mul_mem' := by rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩; exact ⟨w + w', hθ w w'⟩
      inv_mem' := by
        rintro _ ⟨w, rfl⟩
        exact ⟨-w, eq_inv_of_mul_eq_one_right (by rw [← hθ, add_neg_cancel, h1])⟩ }
  have key : ∀ a : G, a ≠ 0 → ∑ s : S, (s : AddChar G ℂ) a = 0 := by
    intro a ha
    obtain ⟨w, hw⟩ : ∃ w, θ w a ≠ 1 := by
      by_contra h
      push_neg at h
      exact ha (hsep a h)
    let s₀ : S := ⟨θ w, w, rfl⟩
    have e : ∑ s : S, (s : AddChar G ℂ) a = θ w a * ∑ s : S, (s : AddChar G ℂ) a := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.mulLeft s₀) (fun s => θ w a * (s : AddChar G ℂ) a)
        (fun s => (s : AddChar G ℂ) a) (fun s => by simp [s₀])).symm
    have h2 : (1 - θ w a) * ∑ s : S, (s : AddChar G ℂ) a = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hw))
  have hsum : ∀ s : S, ∑ a, (s : AddChar G ℂ) a • c a = 0 := by
    rintro ⟨_, w, rfl⟩
    exact hall w
  have htot : ∑ s : S, ∑ a, (s : AddChar G ℂ) a • c a = (∑ s : S, (s : AddChar G ℂ) 0) • c 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    rw [Finset.sum_eq_single (0 : G)]
    · intro a _ ha; rw [key a ha, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun s _ => hsum s), Finset.sum_const_zero] at htot
  simp only [AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ] at htot
  have hcard : (Fintype.card S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [nsmul_eq_mul, mul_one] at htot
  exact hc0 ((smul_eq_zero.mp htot.symm).resolve_left hcard)

theorem avg_fixed : ∀ {A X : Type} [AddCommGroup A] [AddCommGroup X] [Module ℂ X] (H : AddSubgroup A)
    [Fintype (A ⧸ H)] (π : A → X →ₗ[ℂ] X), (∀ a b x, π (a + b) x = π a (π b x)) →
    ∀ x₀ : X, (∀ h ∈ H, π h x₀ = x₀) → ∀ b : A,
      π b (∑ q : A ⧸ H, π (Quotient.out q) x₀) = ∑ q : A ⧸ H, π (Quotient.out q) x₀ := by
  intro A X _ _ _ H _ π hπ x₀ hx₀ b
  have hrep : ∀ a : A, π (Quotient.out (a : A ⧸ H)) x₀ = π a x₀ := by
    intro a
    have h : -a + Quotient.out (a : A ⧸ H) ∈ H :=
      QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (a : A ⧸ H)).symm
    rw [show Quotient.out (a : A ⧸ H) = a + (-a + Quotient.out (a : A ⧸ H)) by abel, hπ, hx₀ _ h]

  rw [map_sum]
  calc ∑ q : A ⧸ H, π b (π (Quotient.out q) x₀) = ∑ q : A ⧸ H, π (b + Quotient.out q) x₀ :=
        Finset.sum_congr rfl fun q _ => (hπ _ _ _).symm
    _ = ∑ q : A ⧸ H, π (Quotient.out ((b : A ⧸ H) + q)) x₀ := by
        refine Finset.sum_congr rfl fun q _ => ?_
        conv_rhs => rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.mk_add, hrep]
    _ = ∑ q : A ⧸ H, π (Quotient.out q) x₀ :=
        Fintype.sum_equiv (Equiv.addLeft (b : A ⧸ H)) _ _ (fun _ => rfl)

end Tw.VacLoc

namespace Tw.VacLoc
open _root_.GlobalTheory

open GlobalTheory.WeilM

section Schr

variable {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]

def schrL (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' f g := by funext x; simp only [schr, Pi.add_apply]; ring
  map_smul' c f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem schr_zero_vec (φ : (κ → R) → ℂ) : schr ψ 0 φ = φ := by
  funext x; simp [schr]

theorem schr_neg_schr (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) : schr ψ (-w) (schr ψ w φ) = φ := by
  rw [schr_schr, neg_add_cancel, schr_zero_vec]
  simp [neg_dotProduct, dotProduct_neg]

theorem schr_comm (v w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ v (schr ψ w φ) = ψ (v.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ v.2) • schr ψ w (schr ψ v φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct]
  congr 1
  · congr 1; ring
  · congr 1; abel

end Schr



theorem exists_schr_eigen : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ {κ M : Type} [Fintype κ] [Fintype M] (u : M → (κ → Fv F v) × (κ → Fv F v))
      (χ : (M → v.adicCompletionIntegers F) → ℂ), Continuous χ →
      (∀ a : M → v.adicCompletionIntegers F, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1) →
      (∀ a b : M → v.adicCompletionIntegers F, χ (a + b) = χ a * χ b *
        ψ (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
          (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2)))) →
      ∃ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ ≠ 0 ∧
        ∀ a : M → v.adicCompletionIntegers F, GlobalTheory.WeilM.schr ψ (∑ m, (a m : Fv F v) • u m) φ = χ a • φ :=
  @GlobalTheory.VacLoc.exists_schr_eigen

end Tw.VacLoc
