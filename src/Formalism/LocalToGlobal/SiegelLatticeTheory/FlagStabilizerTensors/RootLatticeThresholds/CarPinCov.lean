module

public import Formalism.HermitianCurvature.StatementD
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPin

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem choose_congr {α : Sort*} {p q : α → Prop} (e : p = q) (h : ∃ x, p x) (h' : ∃ x, q x) :
    h.choose = h'.choose := by
  subst e; rfl

theorem orbIntegrand_smul (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ) (p : Formalism.FourierDecayAlt.B.SS k r) :
    Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p = c • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p := by
  unfold Formalism.FourierDecayAlt.D.orbIntegrand Formalism.FourierDecayAlt.B.rho
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem orbJ_smulF (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) {c : ℂ} (hc : c ≠ 0) :
    Formalism.FourierDecayAlt.D.orbJ D γ μ (fun g => c • F g) = c • Formalism.FourierDecayAlt.D.orbJ D γ μ F := by
  have hP : (fun θ => Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
      (fun θ => Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS) := by
    funext θ
    have e : (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) =
        c • (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) := by
      funext p; rw [orbIntegrand_smul, smul_comm]; rfl
    rw [e, integrable_smul_iff hc]
  have e2 : ∀ θ : Formalism.FourierDecayAlt.B.SS k r → ℝ, (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) =
      fun p => c • (θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) := fun θ => by
    funext p; rw [orbIntegrand_smul, smul_comm]
  unfold Formalism.FourierDecayAlt.D.orbJ
  by_cases h2 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS
  · have h1 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS := by
      rw [show (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
        ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS from congrArg Exists hP]
      exact h2
    rw [dite_eq_left h1, dite_eq_left h2, choose_congr hP h1 h2, e2, integral_smul]
  · have h1 : ¬ ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS := by
      rw [show (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
        ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS from congrArg Exists hP]
      exact h2
    rw [dite_eq_right h1, dite_eq_right h2, smul_zero]

end Lin

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

end Formalism.L2.SG.Pf.Carrier.CarPin
