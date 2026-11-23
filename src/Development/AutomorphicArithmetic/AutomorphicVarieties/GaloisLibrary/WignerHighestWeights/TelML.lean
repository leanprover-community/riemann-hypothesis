module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rpML {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ)
    (b : Fin n → X →ₗ[ℂ] Module.End ℂ M) :
    ∃ R : (Fin n → X) →ₘₗ[ℂ] Module.End ℂ M, ∀ x, R x = rp n b x := by
  induction n with
  | zero => exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) _ 1, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih (Fin.tail b)
    let g : X →ₗ[ℂ] (Fin n → X) →ₘₗ[ℂ] Module.End ℂ M :=
      { toFun := fun x0 => (LinearMap.mulRight ℂ (b 0 x0)).compMultilinearMap R
        map_add' := fun u v => MultilinearMap.ext fun y => by simp [mul_add]
        map_smul' := fun c u => MultilinearMap.ext fun y => by simp }
    refine ⟨LinearMap.uncurryLeft (M := fun _ : Fin (n + 1) => X) g, fun x => ?_⟩
    rw [rp_succ, ← hR]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telML :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M),
      ∃ T : (X →ₗ[ℂ] M) →ₗ[ℂ] (Fin n → X) →ₘₗ[ℂ] M, ∀ f x, T f x = tel n a b f x := by
  intro X M _ _ _ _ n a b
  induction n with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih (Fin.tail a) (Fin.tail b)
    obtain ⟨R, hR⟩ := rpML n (Fin.tail b)
    let g : (X →ₗ[ℂ] M) → X →ₗ[ℂ] (Fin n → X) →ₘₗ[ℂ] M := fun f =>
      { toFun := fun x0 => (a 0 x0).compMultilinearMap (T f) +
          (LinearMap.applyₗ (f x0) : Module.End ℂ M →ₗ[ℂ] M).compMultilinearMap R
        map_add' := fun u v => MultilinearMap.ext fun y => by simp; abel
        map_smul' := fun c u => MultilinearMap.ext fun y => by simp }
    have hg : ∀ (f : X →ₗ[ℂ] M) (x : Fin (n + 1) → X),
        LinearMap.uncurryLeft (σ := RingHom.id ℂ) (M := fun _ : Fin (n + 1) => X) (g f) x =
        a 0 (x 0) (T f (Fin.tail x)) + R (Fin.tail x) (f (x 0)) := by
      intro f x
      rfl
    refine ⟨{ toFun := fun f => LinearMap.uncurryLeft (M := fun _ : Fin (n + 1) => X) (g f)
              map_add' := fun u v => MultilinearMap.ext fun y => ?_
              map_smul' := fun c u => MultilinearMap.ext fun y => ?_ }, fun f x => ?_⟩
    · simp only [add_apply, hg, map_add (f := _), LinearMap.add_apply]
      abel
    · simp only [smul_apply, hg, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_add]
    · rw [tel_succ, ← hT, ← hR]
      exact hg f x
