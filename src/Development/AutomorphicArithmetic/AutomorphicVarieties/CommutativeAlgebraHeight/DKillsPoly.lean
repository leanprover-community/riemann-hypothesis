module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_kills_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E) (M : Set E), Submodule.span A M = ⊤ → (∀ (k : ℕ) (h : Fin k → E), (∀ a, h a ∈ M) → D.D (MvPolynomial (Fin k) A) (1 + Det.gen h * (1 ⊗ₜ x)) = 1) → D.Kills x := by
  intro n A E _ _ _ D x M hM H B _ _ h
  have key : ∀ e : E, ((1 : B) ⊗ₜ[A] e) ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    intro e
    have he : e ∈ Submodule.span A M := hM ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [tmul_add]; exact add_mem ha hb
    | smul a y _ hy =>
      rw [tmul_smul, ← algebraMap_smul B]
      exact Submodule.smul_mem _ _ hy
  have hh : h ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    induction h with
    | add a b ha hb => exact add_mem ha hb
    | tmul b e =>
      have : b ⊗ₜ[A] e = b • ((1 : B) ⊗ₜ[A] e) := by simp [smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (key e)
  obtain ⟨k, f, g, rfl⟩ := Submodule.mem_span_set'.1 hh
  choose m hm hmg using fun i => (g i).2
  have h1 := D.nat _ B (MvPolynomial.aeval f) (1 + Det.gen m * (1 ⊗ₜ x))
  rw [H k m hm, map_one] at h1
  refine Eq.trans (congrArg _ ?_) h1

  simp only [Det.gen, map_add (f := _), map_mul, map_one, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X,
  AlgHom.id_apply, ← hmg, smul_tmul', smul_eq_mul, mul_one]
