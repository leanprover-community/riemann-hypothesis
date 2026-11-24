module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceWedgePairingPerfectRationalFormsStatement
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma perfectPairing_surjective {F Q P : Type*} [Field F] [AddCommGroup Q] [Module F Q] [AddCommGroup P] [Module F P]
    [FiniteDimensional F Q] [FiniteDimensional F P] (hr : Module.finrank F Q = Module.finrank F P)
    (B : Q →ₗ[F] P →ₗ[F] F) (hB : ∀ w, (∀ y, B w y = 0) → w = 0) :
    Function.Surjective B ∧ Function.Surjective B.flip := by
  have hinj : Function.Injective B :=
    (injective_iff_map_eq_zero B).2 fun w hw => hB w fun y => by simp [hw]
  have hs : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (P →ₗ[F] F) = Module.finrank F P from Subspace.dual_finrank_eq, hr])).1 hinj
  refine ⟨hs, ?_⟩
  have hinj' : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    refine (Module.forall_dual_apply_eq_zero_iff F y).1 fun f => ?_
    obtain ⟨w, rfl⟩ := hs f
    exact LinearMap.congr_fun hy w
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (Q →ₗ[F] F) = Module.finrank F Q from Subspace.dual_finrank_eq, hr])).1 hinj'

theorem UpperTheory.Gal.productCup_of_system.dualForm_of :
    DualForm := by
  intro F K _ _ _ _ _ _ d x hc τ ht a ha ψ
  obtain ⟨hinj, hrk, hfdP⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht (d - a) a (by omega)
  obtain ⟨-, -, hfdQ⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht a (d - a) (by omega)
  haveI : FiniteDimensional F K := hc.fin
  haveI : FiniteDimensional F (⋀[K]^(d - a) Ω[K⁄ℂ]) := Module.Finite.trans K _
  haveI : FiniteDimensional F (⋀[K]^a Ω[K⁄ℂ]) := Module.Finite.trans K _
  let T : DR ℂ K →ₗ[F] F := (Algebra.trace F K) ∘ₗ (τ.restrictScalars F)
  let B : (⋀[K]^a Ω[K⁄ℂ]) →ₗ[F] (⋀[K]^(d - a) Ω[K⁄ℂ]) →ₗ[F] F :=
    LinearMap.mk₂ F (fun w y => T ((y : DR ℂ K) * (w : DR ℂ K)))
      (fun w w' y => by simp [mul_add])
      (fun c w y => by simp [mul_smul_comm])
      (fun w y y' => by simp [add_mul])
      (fun c w y => by simp [smul_mul_assoc])
  have hr : Module.finrank F (⋀[K]^a Ω[K⁄ℂ]) = Module.finrank F (⋀[K]^(d - a) Ω[K⁄ℂ]) := by
    rw [← Module.finrank_mul_finrank F K (⋀[K]^a Ω[K⁄ℂ]),
      ← Module.finrank_mul_finrank F K (⋀[K]^(d - a) Ω[K⁄ℂ]), hrk]
  obtain ⟨hs, hs'⟩ := perfectPairing_surjective hr B (fun w hw => Subtype.ext (hinj w.1 w.2 fun y hy => hw ⟨y, hy⟩))
  constructor
  · obtain ⟨w, hw⟩ := hs (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
  · obtain ⟨w, hw⟩ := hs' (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
