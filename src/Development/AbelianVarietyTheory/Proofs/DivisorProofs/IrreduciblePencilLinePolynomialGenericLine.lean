module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc.GenericLine

variable (F : Type) [Field F] (D N : ℕ)

abbrev Idx := (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)

def shiftFun (c : F) : Option (Idx D N) → MvPolynomial (Option (Idx D N)) F
  | some (Sum.inr (Sum.inl j)) =>
      X (some (Sum.inr (Sum.inl j))) + C c * (X (some (Sum.inr (Sum.inr j))) * X none)
  | o => X o

def shift (c : F) : MvPolynomial (Option (Idx D N)) F →ₐ[F] MvPolynomial (Option (Idx D N)) F :=
  aeval (shiftFun F D N c)

theorem shift_comp (c : F) : (shift F D N c).comp (shift F D N (-c)) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  rintro (_ | (p | j | j))
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]

def theta : MvPolynomial (Option (Idx D N)) F ≃ₐ[F] MvPolynomial (Option (Idx D N)) F :=
  AlgEquiv.ofAlgHom (shift F D N 1) (shift F D N (-1))
    (by simpa using shift_comp F D N 1) (by simpa using shift_comp F D N (-1))

def place : Fin (D + 1) × Fin N → Option (Idx D N) := fun p =>
  Fin.lastCases (motive := fun _ => Option (Idx D N)) (some (Sum.inr (Sum.inl p.2)))
    (fun i => some (Sum.inl (i, p.2))) p.1

theorem place_injective : Function.Injective (place D N) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  induction a using Fin.lastCases <;> induction a' using Fin.lastCases <;> simp_all [place]

theorem line_eq (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    GlobalTheory.PencilDisc.line (fun i j => (X (Sum.inl (i, j)) : MvPolynomial (Idx D N) F))
      (fun j => X (Sum.inr (Sum.inl j))) (fun j => X (Sum.inr (Sum.inr j))) f =
    optionEquivLeft F (Idx D N) (theta F D N (rename (place D N) f)) := by
  have key : (aeval (join (fun i j => (Polynomial.C (X (Sum.inl (i, j)) : MvPolynomial (Idx D N) F)))
      (fun j => Polynomial.C (X (Sum.inr (Sum.inl j))) + Polynomial.C (X (Sum.inr (Sum.inr j))) * Polynomial.X)) :
      MvPolynomial (Fin (D + 1) × Fin N) F →ₐ[F] Polynomial (MvPolynomial (Idx D N) F)) =
      ((optionEquivLeft F (Idx D N)).toAlgHom.comp ((theta F D N).toAlgHom.comp (rename (place D N)))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    induction i using Fin.lastCases <;> simp [join, place, theta, shift, shiftFun, AlgEquiv.ofAlgHom_apply]
  exact congrArg (fun φ => φ f) key

end GlobalTheory.PencilDisc.GenericLine

private theorem irreducible_rename_of_injective' {σ τ K : Type} [Field K] (g : σ → τ)
    (hg : Function.Injective g) (f : MvPolynomial σ K) (hf : Irreducible f) :
    Irreducible (rename g f) := by
  classical
  have hk : ∀ p : MvPolynomial σ K, killCompl hg (rename g p) = p := killCompl_rename_app hg
  have hf0 : rename g f ≠ 0 := by
    intro h
    apply hf.ne_zero
    rw [← hk f, h, map_zero]
  have hvars : ∀ a : MvPolynomial τ K, a ∣ rename g f → ∃ q, rename g q = a := by
    rintro a ⟨b, hab⟩
    have ha : a ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hab
      exact hf0 hab
    have hb : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hab
      exact hf0 hab
    refine exists_rename_eq_of_vars_subset_range a g hg ?_
    intro i hi
    by_contra hni
    have h1 : degreeOf i (rename g f) = 0 := by
      by_contra hne
      have hmem : i ∈ (rename g f).vars := mem_vars_iff_degreeOf_ne_zero.2 hne
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (vars_rename g f hmem)
      exact hni ⟨j, rfl⟩
    rw [hab, degreeOf_mul_eq ha hb] at h1
    exact mem_vars_iff_degreeOf_ne_zero.1 (Finset.mem_coe.1 hi) (by omega)
  refine irreducible_iff.2 ⟨?_, ?_⟩
  · intro hu
    exact (irreducible_iff.1 hf).1 (by simpa [hk] using hu.map (killCompl hg))
  · intro a b hab
    obtain ⟨a', rfl⟩ := hvars a ⟨b, hab⟩
    obtain ⟨b', rfl⟩ := hvars b ⟨rename g a', by rw [hab, mul_comm]⟩
    rw [← map_mul] at hab
    rcases (irreducible_iff.1 hf).2 (rename_injective g hg hab) with h | h
    · exact Or.inl (h.map _)
    · exact Or.inr (h.map _)


open GlobalTheory.PencilDisc.GenericLine in
theorem GlobalTheory.PencilDisc.irreducible_line_generic (F : Type) [Field F] (D N : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : Irreducible f) :
    Irreducible (GlobalTheory.PencilDisc.line
      (fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F))
      (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j))) f) := by
  rw [line_eq F D N f, MulEquiv.irreducible_iff, MulEquiv.irreducible_iff]
  exact irreducible_rename_of_injective' (place D N) (place_injective D N) f hf
