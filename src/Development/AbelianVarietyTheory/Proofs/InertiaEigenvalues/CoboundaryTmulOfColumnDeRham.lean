module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CobColumn

theorem coboundary_tmul_of_column : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (β : ι → P.R.BdR),
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun x => P.actQdR (g : GQ l) (β x)) - β) →
    ∃ b : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR, ∀ g,
      c₀ g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) (repOf ρ₀) g b - b := by
  intro l _ P K ι _ _ ρ₀ c₀ β h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (ι → P.R.BdR) :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).toLinearMap ∘ₗ (TensorProduct.comm ℚ_[l] _ _).toLinearMap
  have hΦinj : Function.Injective Φ :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).injective.comp (TensorProduct.comm ℚ_[l] _ _).injective
  have hΦ : ∀ v b i, Φ (v ⊗ₜ b) i = algebraMap ℚ_[l] P.R.BdR (v i) * b := by
    intro v b i
    simp [Φ, piScalarRight_apply, piScalarRightHom_tmul, Algebra.smul_def]
  have hact : ∀ g v b, actVdR (P.PD K) (repOf ρ₀) g (v ⊗ₜ b) = repOf ρ₀ g v ⊗ₜ P.actQdR (g : GQ l) b := by
    intro g v b
    rw [← P.PD_actdR K g b]
    rfl
  refine ⟨∑ x, Pi.single x 1 ⊗ₜ β x, fun g => hΦinj ?_⟩
  funext i
  have hi := congrFun (h g) i

  simp only [map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, hact, hΦ, repOf_apply, mul_one]
  rw [hi]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    rw [Finset.sum_eq_single x (fun y _ hy => by simp [Pi.single_eq_of_ne hy]) (by simp)]
    simp
  · rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx; simp [Pi.single_eq_of_ne' hx]
    · simp

end GlobalTheory.CobColumn

end
