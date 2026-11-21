import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs3

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}


end Abs3

end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma




def KernelDiagonalVolumeModulusConditions (n₀ : ℕ) (A C cb c₁ A₂ cε C₁ : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.KernelDiag ∧ X.FinVol ∧
    ∃ Mod : Set X.I.GA, MeasurableSet Mod ∧ X.ProbMod c₁ Mod ∧
      X.NearStep (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) c₁ A₂ Mod ∧
      X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) Mod ∧ X.DeepInt (A₂ + 1) Mod


end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def LocFinF (X : CData) : Prop := IsLocallyFiniteMeasure X.μf



example (X : CData) [SecondCountableTopology X.I.Gf] : BorelSpace X.I.GA := inferInstance
example (X : CData) : IsTopologicalGroup X.I.GA := inferInstance
example (X : CData) [SecondCountableTopology X.I.Gf] : SecondCountableTopology X.I.GA := inferInstance
theorem automorphic_L2_secondCountable (X : CData) [SecondCountableTopology X.I.Gf] : SecondCountableTopology X.L2 := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  infer_instance
example (X : CData) : IsLocallyFiniteMeasure (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) := inferInstance
example (X : CData) : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)).IsHaarMeasure := inferInstance
example (X : CData) : LocallyCompactSpace X.I.Ginf := inferInstance
example (X : CData) : BorelSpace X.I.Ginf := inferInstance
example (X : CData) : T2Space X.I.Ginf := inferInstance

theorem rr_muA_locFin (X : CData) (h : LocFinF X) : IsLocallyFiniteMeasure (X.I.muA X.μf) := by
  have : IsLocallyFiniteMeasure X.μf := h
  unfold AutInst.muA; infer_instance

theorem rr_muA_openPos (X : CData) [X.μf.IsHaarMeasure] : (X.I.muA X.μf).IsOpenPosMeasure := by
  unfold AutInst.muA; infer_instance


end Formalism.MainNotions.LeviCoordinates

end
end
