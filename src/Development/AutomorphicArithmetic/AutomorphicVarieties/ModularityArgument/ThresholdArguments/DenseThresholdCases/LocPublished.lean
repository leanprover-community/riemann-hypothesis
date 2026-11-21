import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UnitaryThreeAutomorphyOfInputs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ModU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaU

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W
private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
theorem UpperTheory.V.W.modU_of_printsH :
    Pa.CohP → LocCFTAll → Pa.PfromAut → _root_.UpperTheory.V.W.HidaUAlt → _root_.UpperTheory.V.W.ModUAlt := by
  intro hcoh hloc hP hH l _ L Ω _ _ _ _ _ _ s V hS hμ c hc n hn r B Λ ι
  obtain ⟨J, hJ, hA⟩ := hH l L Ω s V hS hμ c hc n hn r B Λ ι
  haveI := coef_isCoef l c
  obtain ⟨h1, h3⟩ := hP hcoh l L Ω s V c.O n r B J hn hS (hloc l L Ω s) ((muL l L Ω s V).1 hμ) hA
  exact ⟨J, hJ, h1, h3⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.W
theorem cohP_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Pa.CohP :=
  ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
theorem global_compat_printed_of_literal_automorphy_n (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : GC.Hypotheses₂ :=
  ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
theorem locPrints_of_litN (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Loc.LocalPublishedTheorems :=
  ⟨hN.coh.lfK, hN.coh.ltK, hN.coh.leK, hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.bk⟩
theorem local_class_field_theory_all_of_literal_automorphy (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : LocCFTAll := locCFT hN.aut.art (_root_.UpperTheory.V.W.cohP_alt hN)
theorem modularity_unitary_of_automorphy_hida_unitary (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hP : Pa.PfromAut) (hH : _root_.UpperTheory.V.W.HidaUAlt) : _root_.UpperTheory.V.W.ModUAlt := _root_.UpperTheory.V.W.modU_of_printsH (_root_.UpperTheory.V.W.cohP_alt hN) (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) hP hH
end UpperTheory.V.W
end
end
