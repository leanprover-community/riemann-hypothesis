module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.QuadFiniteDimensional
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PIW.AdelicOrbitU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem stFix : StFix := by
  intro F E _ _ _ _ σ h2 hfix R _ _
  have hσσ : ∀ a : E, σ (σ a) = a := fun a => quad_sigma_sigma (σ := σ) (h2 := h2) (hfix := hfix) a
  refine ⟨fun z => quad_sig_sig σ R hσσ z, ?_⟩
  intro z hz
  obtain ⟨θ, _hθ0, hσθ, ⟨d, _hd0, hd⟩, hli⟩ := quad_exists_theta (σ := σ) (h2 := h2) (hfix := hfix)
  obtain ⟨a, b, rfl⟩ : ∃ a b : R, z = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ :=
    ⟨_, _, quad_decomp (h2 := h2) (hli := hli) (R := R) z⟩
  rw [quad_sig (R := R) (σ := σ) (hσθ := hσθ)] at hz
  have h1 : (-b) ⊗ₜ[F] θ = b ⊗ₜ[F] θ := add_left_cancel hz
  have hb : b ⊗ₜ[F] θ = 0 := by
    have h2' : (2 : F) • (b ⊗ₜ[F] θ) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      rw [TensorProduct.neg_tmul, neg_add_cancel]
    exact (smul_eq_zero.mp h2').resolve_left two_ne_zero
  have h12 : algebraMap F R (1 / 2) * (2 * a) = a := by
    rw [← mul_assoc, show (2 : R) = algebraMap F R 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  rw [quad_trace (h2 := h2) (hli := hli) (R := R) (hd := hd), hb, add_zero, h12]
  simp [Algebra.TensorProduct.algebraMap_apply]

end PIW.AdelicOrbitU
