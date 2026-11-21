import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingRealStatement

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flatWeight_rule_reads_nonvanishing_detSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → ∃ f g : Rul Xo c, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) ∧ g ∈ secZ Xo c (-exOf Dw (flatWt Dw τ) 0) ∧ idem Z * f = f ∧ idem Z * g = g ∧ f * g = idem Z ∧ Reads Y V τ sig f := by
  first | exact @GlobalTheory.BdryUnit.ReadDet.exists_reads | exact GlobalTheory.BdryUnit.ReadDet.exists_reads | (intros; apply GlobalTheory.BdryUnit.ReadDet.exists_reads <;> assumption)
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_length_of_reading_horizontal_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig → f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) → Reads Y V τ sig f → ∀ σ, GoodEmb c σ → ∃ b : ℝ, 0 < b ∧ homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) f '' framesOn (U σ) Z = {b} := by
  first | exact @GlobalTheory.BdryUnit.const_length_of_reads | exact GlobalTheory.BdryUnit.const_length_of_reads | (intros; apply GlobalTheory.BdryUnit.const_length_of_reads <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem unit_at_eqChar_points : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), Nonempty (ArchSec U x Z (flatWt Dw τ)) → ∃ s₀ : ArchSec U x Z (flatWt Dw τ), ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s₀.sig) = 0 := by
  intro hP hQ2 hQ3 E _ _ _ H Dw l Xo c r U x hL Z τ _
  obtain ⟨Y, V, sig, hV, hs, hnv, hh⟩ := GlobalTheory.T.exists_model_rule_section hP hQ2 hQ3 E H Dw l Xo c r U x hL Z τ
  obtain ⟨f, g, hf, hg, hfi, hgi, hfg, hR⟩ := GlobalTheory.T.exists_flatWeight_rule_reads_nonvanishing_detSection E H Dw l Xo c Y Z V τ sig hV hs hnv
  have hnorm := GlobalTheory.T.constant_length_of_reading_horizontal_section E H Dw l Xo c r U x hL Z τ Y V sig f hV hs hnv hh hf hR
  choose b hb hb' using fun σ => hnorm _ (goodEmb_goodOf c σ)
  exact ⟨⟨f, g, hf, hg, hfi, hgi, hfg, b, hb, hb'⟩, fun T io y₀ h0 hZ =>
    GlobalTheory.T.rule_section_nowhere_vanishing_real hP E H Dw l Xo c Y Z V τ sig f hV hs hnv hR T io y₀ h0 hZ⟩

end GlobalTheory.BdryUnit

end
end
