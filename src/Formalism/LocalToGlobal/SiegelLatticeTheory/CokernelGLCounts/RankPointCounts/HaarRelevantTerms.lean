import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HaarPushforward
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MapConjOfBounded

noncomputable section

open scoped ComplexConjugate
open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.CovariantRepresentation Formalism.L2.SG.HaarPushforward

namespace Formalism.L2.SG.HaarRelevantTerms

def RHaarRelC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    (∀ r ∈ Rset t, X.psiInfU u r * starRingEnd ℂ (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) = 1) →
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∃ ν : Measure X.B.I.Ginf, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (Rset t)ᶜ = 0 ∧
      (∀ K : Set X.B.I.Ginf, IsCompact K → ν K < ⊤) ∧ (∀ r ∈ Rset t, ν.map (fun x => r * x) = ν) ∧
      ν.map (fun x => x⁻¹) = ν ∧ ν.map (fun x => h⁻¹ * x * h) = ν

def FixDecC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), t.relevant →
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∃ k n : X.B.I.Ginf, h = k * n ∧ n ∈ Rset t ∧ (∀ r, r ∈ Rset t ↔ k⁻¹ * r * k ∈ Rset t) ∧
      ∃ C : Set X.B.I.Ginf, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C




end Formalism.L2.SG.HaarRelevantTerms
