module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef




theorem extHom_onto : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L), F.Onto → (extHom hL hb₁ hb₂ F).Onto := by
  intro l _ G _ _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hF
  choose x hx hfx using fun i => hF (b₂ i) (hb₂.1 i)
  have key : ∀ i j, ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m =
      (1 : Matrix (Fin k₂) (Fin k₂) ↥LL.1) i j := by
    intro i j
    have h1 := congrFun (LinearMap.toMatrix_mulVec_repr b₁ b₂ F.f (x j)) i
    rw [hfx j, Module.Basis.repr_self] at h1
    rw [Matrix.one_apply, ← show _ = ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m from rfl.symm]
    refine Eq.trans h1 ?_
    rw [Finsupp.single_apply]
    simp only [eq_comm]
  let X : Matrix (Fin k₁) (Fin k₂) ↥LL'.1 := fun m j => incl hL (b₁.repr (x j) m)
  have hX : extMat hL b₁ b₂ F * X = 1 := by
    refine Matrix.ext fun i j => ?_
    have := congrArg (incl hL) (key i j)

    rw [map_sum] at this
    simp only [map_mul] at this
    rw [Matrix.mul_apply]
    refine Eq.trans this ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  intro y hy
  refine ⟨X.mulVec y, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ (incl_integral hL (hb₁.2 _ (hx j) i)) (hy j)
  · change (extMat hL b₁ b₂ F).mulVec (X.mulVec y) = y
    rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec]

end GlobalTheory.BaseCoef
