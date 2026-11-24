module

import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasurePreservingPiProd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

namespace JL

def RightInvS : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μ →
    ∀ s ∈ SLoc ε e z, μ.map (fun x => x * s) = μ

theorem frameLoc_swap {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' : ℝ}
    (hF : FrameLoc ε k e z z' T T') : FrameLoc ε k e z' z T' T :=
  ⟨hF.dim, hF.k_pos, hF.sig, hF.e_li, hF.ee, hF.ez', hF.ez, hF.zz', hF.zz, hF.T'_pos, hF.T_pos⟩

theorem lintegral_mul_right_of_map {n : ℕ} {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε))
    (t : Formalism.REAL.UJ ε) (hμ : μ.map (fun x => x * t) = μ) (F : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂μ := by
  have hE : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * t) :=
    (MeasurableEquiv.mulRight t).measurableEmbedding
  calc ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂(μ.map (fun x => x * t)) := (hE.lintegral_map F).symm
    _ = ∫⁻ x, F x ∂μ := by rw [hμ]

theorem inner_dc {n : ℕ} {ε : Fin n → Bool} (μS μS' : Measure (Formalism.REAL.UJ ε))
    (s₁ s₁' g : Formalism.REAL.UJ ε) (h₁ : μS.map (fun x => x * s₁) = μS)
    (h₁' : μS'.map (fun x => x * s₁') = μS') (φ : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ s, ∫⁻ s', φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) ∂μS' ∂μS = ∫⁻ s, ∫⁻ s', φ (s * g * s'⁻¹) ∂μS' ∂μS := by
  have key : ∀ s s' : Formalism.REAL.UJ ε,
      φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) = φ ((s * s₁) * g * (s' * s₁')⁻¹) := by
    intro s s'
    congr 1
    group
  have inner : ∀ x : Formalism.REAL.UJ ε,
      ∫⁻ s', φ (x * g * (s' * s₁')⁻¹) ∂μS' = ∫⁻ s', φ (x * g * s'⁻¹) ∂μS' := fun x =>
    lintegral_mul_right_of_map μS' s₁' h₁' (fun y => φ (x * g * y⁻¹))
  simp_rw [key, inner]
  exact lintegral_mul_right_of_map μS s₁ h₁ (fun x => ∫⁻ s', φ (x * g * s'⁻¹) ∂μS')

theorem measurableSet_goodLoc (r : ℕ) (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  apply Formalism.L2.SG.RealObj.InfCut.ProductExactness.measurableSet_goodLoc <;> assumption

end JL

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
