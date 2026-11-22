module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihilaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjActionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltrationStatement

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem conj_embK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  show conjEmb τ ((H.bar z : 𝓞 E) : E) = τ (z : E)
  rw [H.bar_eq]
  simp [conjEmb, IsCMField.complexEmbedding_complexConj]

end GlobalTheory.KSExist
