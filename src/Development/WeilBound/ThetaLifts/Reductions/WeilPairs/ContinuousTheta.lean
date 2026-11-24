module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace PositivityTheory.ThKW.RealC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem theta_inc {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (x : E) :
    θ (infPartF F E (incAF F E x)) = τ x := by
  have : infPartF F E (incAF F E x) = fstA F 1 ⊗ₜ[F] x := rfl
  rw [this, map_one, h.1]

theorem continuous_theta {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) :
    Continuous (θ.comp (infPartF F E)) := by
  haveI := isModuleTopology_AE F E
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  exact h.2.comp (continuous_fst (X := Ainf F) (Y := Af F))

theorem herm_map {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  rw [conjTranspose_apply, map_apply, map_apply, ← hτ, hJ.1]

theorem unit_map {σ : E →ₐ[F] E} (τ : E →+* ℂ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsUnit (J.map τ).det := by
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [this]
  exact ((map_ne_zero τ).2 hJ.2).isUnit

theorem re_xi {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {ξ : E} (hσ : σ ξ = -ξ) :
    (τ ξ).re = 0 := by
  have := congrArg Complex.re (hτ ξ)
  rw [hσ, map_neg] at this
  simp at this
  linarith

theorem im_xi {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {ξ : E} (hξ : ξ ≠ 0) (hσ : σ ξ = -ξ) :
    (τ ξ).im ≠ 0 := fun h => (map_ne_zero τ).2 hξ (Complex.ext (re_xi hτ hσ) h)

end PositivityTheory.ThKW.RealC
