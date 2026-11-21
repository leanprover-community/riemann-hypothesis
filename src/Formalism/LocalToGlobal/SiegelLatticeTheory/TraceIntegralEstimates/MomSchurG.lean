import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomFinal
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchur
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit

set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.CayleySignature

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParamTieG (D : D7) (Cn : ℝ) : Prop :=
  0 < kaS D ∧ ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → IsHCParam lam' →
    ∃ h : ℝ, GapAtLeast (epsSH D.R) lam' h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h

def ParamTieGF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i =>
    Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ParamTieG (Fm.D x i) Cn




end Formalism.L2.S.Pv.Mom
