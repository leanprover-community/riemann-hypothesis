module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ValuesEqOfCommonPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.SecGlueInt

theorem exists_secZ_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c) (w : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, ((∏ i, C.t i ^ w i : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R) → ∃ f ∈ GlobalTheory.AllWt.secZ Xo c w, ∀ Z, evC h Z f = b Z := by
  intro E _ _ _ H Dw l Xo c h w b hb
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.Reg.SecGlue.exists_sec_core E H Dw l Xo c hL h (hA h) w b hb
  exact ⟨g, GlobalTheory.AllWt.mem_secZ.2 ⟨h1, h2⟩, h3⟩

end GlobalTheory.SecGlueInt
