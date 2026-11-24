module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem semilinear_basis_image_indep_of_basis :
    ∀ (K : Type) [Field K] (e : K →+* ℂ) (V : Type) [AddCommGroup V] [Module K V]
      (W : Type) [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) (ι κ : Type)
      (b : Module.Basis ι K V) (b' : Module.Basis κ K V),
      (LinearIndependent ℂ (fun i => j (b i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) →
      LinearIndependent ℂ (fun i => j (b' i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b' i)) = ⊤ := by
  intro K _ e V _ _ W _ _ j ι κ b b' ⟨hli, hsp⟩
  letI : Algebra K ℂ := e.toAlgebra
  letI : Module K W := Module.compHom W e
  haveI : IsScalarTower K ℂ W := ⟨fun k c w => by
    change (e k * c) • w = e k • c • w
    exact mul_smul _ _ _⟩
  let j' : V →ₗ[K] W :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun k v => j.map_smulₛₗ k v }
  let L : ℂ ⊗[K] V →ₗ[ℂ] W := j'.liftBaseChange ℂ
  have hL : ∀ v : V, L (1 ⊗ₜ[K] v) = j v := fun v => by
    simp [L, j']
  let c : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let E : ℂ ⊗[K] V ≃ₗ[ℂ] W := (b.baseChange ℂ).equiv c (Equiv.refl ι)
  have hE : (E : ℂ ⊗[K] V →ₗ[ℂ] W) = L := by
    refine (b.baseChange ℂ).ext fun i => ?_
    rw [LinearEquiv.coe_coe]
    simp only [E, Module.Basis.equiv_apply, Equiv.refl_apply, c, Module.Basis.mk_apply]
    rw [Module.Basis.baseChange_apply, hL]
  have hb : (fun i => j (b' i)) = ⇑((b'.baseChange ℂ).map E) := by
    funext i
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, ← hL, ← hE, LinearEquiv.coe_coe]
  rw [hb]
  exact ⟨Module.Basis.linearIndependent _, Module.Basis.span_eq _⟩

end GlobalTheory
