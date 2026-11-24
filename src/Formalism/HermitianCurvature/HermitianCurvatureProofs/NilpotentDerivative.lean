module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nd_deriv_smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℂ) (v : E) :
    deriv (fun t => φ t • v) 0 = deriv φ 0 • v := by
  by_cases hφ : DifferentiableAt ℝ φ 0
  · exact deriv_smul_const hφ v
  by_cases hv : v = 0
  · simp [hv]
  rw [deriv_zero_of_not_differentiableAt hφ, zero_smul]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hφ
  obtain ⟨ℓ, -, hℓv⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
  have h1 : DifferentiableAt ℝ (fun t => ℓ (φ t • v)) 0 :=
    (ℓ.restrictScalars ℝ).differentiableAt.comp 0 hd
  have hn : ℓ v ≠ 0 := by
    rw [hℓv]; exact RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  have h2 : φ = fun t => ℓ (φ t • v) * (ℓ v)⁻¹ := by
    funext t
    rw [map_smul, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  rw [h2]
  exact h1.mul_const _

theorem nd_exp_mem {k r : ℕ} {X : B.Mat k r} (hX : X ∈ JfS.lieOf (Nset k r)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Q.Nlev k r 0 :=
  ⟨hX t, (hX t).1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

theorem nd_om_mem {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r z z' :=
  ⟨⟨hg.1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩

theorem nilpotent_derivative : NDiff := by
  intro k r Wp Wq _ _ _ _ D m J hJ
  obtain ⟨_, hL, hR, _⟩ := hJ
  constructor
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
    have e : (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) =
        fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hR g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) 0 = _
    have e : (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) =
        fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hL g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
