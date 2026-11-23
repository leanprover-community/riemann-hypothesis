module

public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem conjLinear_onto_of_injective_of_le_range :
    ∀ (W M : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (J₀ J₁ : W →ₗ⋆[ℂ] M), (∀ p ∈ S, ∃ ξ, J₀ ξ = p) → Function.Injective J₁ → (∀ ξ, J₁ ξ ∈ S) → ∀ p ∈ S, ∃ ξ, J₁ ξ = p := by
  intro W M _ _ _ _ _ S J₀ J₁ h0 hinj hS
  let f0 : W →ₗ[ℝ] M :=
    { toFun := J₀
      map_add' := J₀.map_add
      map_smul' := fun r x => by
        show J₀ (r • x) = r • J₀ x
        rw [← Complex.coe_smul, J₀.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }
  let f1 : W →ₗ[ℝ] M :=
    { toFun := J₁
      map_add' := J₁.map_add
      map_smul' := fun r x => by
        show J₁ (r • x) = r • J₁ x
        rw [← Complex.coe_smul, J₁.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }

  have hle0 : S.restrictScalars ℝ ≤ LinearMap.range f0 := fun p hp => h0 p hp
  have hle1 : LinearMap.range f1 ≤ S.restrictScalars ℝ := by
    rintro _ ⟨ξ, rfl⟩
    exact hS ξ
  have hf1 : Function.Injective f1 := hinj
  have : FiniteDimensional ℝ (S.restrictScalars ℝ) := Submodule.finiteDimensional_of_le hle0
  have hdim : Module.finrank ℝ (S.restrictScalars ℝ) ≤ Module.finrank ℝ (LinearMap.range f1) := by
    rw [LinearMap.finrank_range_of_inj hf1]
    exact (Submodule.finrank_mono hle0).trans (LinearMap.finrank_range_le f0)

  have heq : LinearMap.range f1 = S.restrictScalars ℝ := Submodule.eq_of_le_of_finrank_le hle1 hdim
  intro p hp
  have hp' : p ∈ LinearMap.range f1 := heq ▸ hp
  obtain ⟨ξ, hξ⟩ := hp'
  exact ⟨ξ, hξ⟩

end GlobalTheory
