import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasisStatement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDictionaryPartB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDualFamilyHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapTorusSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableNormCommuting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCommutesSeparableHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCentralizerIdentification
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapFirstProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapThirdProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapIntegralProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFirstProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSecondProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeThirdProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFourthProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaFirstHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaSecondHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriContraction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriContractionHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriOrbitalComparison
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeFourthProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTraceFourthProperty

section
open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.Rg.Tf.Loc

theorem quotient_integral_of_compact_open (hT : T0) (h : QuotientIntegralCompactOpen) : H2 := by
  intro F _ _ _ _ n _ _ μG H μH h1 h2 h3 h4 Fn _ h5 h6 Rp h7 h8
  obtain ⟨-, -, ho, hc⟩ := hT.1 F n
  exact h F n μG H μH (unitGL F) ho hc h1 h2 h3 h4 Fn h5 h6 Rp h7 h8

theorem measure_transport_of_open_set (hT : T0) (hD : D0a) (h : MeasureTransportOpenSet) : H4 := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n _ _ _ _ δ γ hh μδ μγ h1 h2 h3 y z hz
  exact h k E hun σ hgen n (unitGL E : Subgroup (GL (Fin n) E)) (unitGL k : Subgroup (GL (Fin n) k))
    (hT.1 E n).2.2.1 (fun g => (hD k E hun σ hgen).2.2.1 n g) δ γ hh μδ μγ h1 h2 h3 y z hz

theorem bcflUnit_of_leaves (hD0a : D0a) (hD0b : D0a → IntegralBasisUnramified) (hD0c : IntegralBasisUnramified → TraceOneIntegralElement) (hT0 : T0) (hA1 : A1)
    (hA2 : A1 → A2) (hA3 : A2 → A3) (hN1 : N1) (hN2 : N2) (hN3 : N1 → N2 → N3)
    (hN4 : D0a → IntegralBasisUnramified → TraceOneIntegralElement → N3 → N4) (hL1 : L1) (hL2 : D0a → L2) (hL3 : TraceOneIntegralElement → L1 → L3)
    (hL4 : D0a → A1 → L4) (hH2U : QuotientIntegralCompactOpen) (hH3 : H3) (hH4U : D0a → T0 → A1 → MeasureTransportOpenSet)
    (hZ1 : D0a → T0 → A1 → A2 → A3 → N4 → L2 → L3 → L4 → H2 → H3 → H4 → Z1)
    (hZ2 : L2 → N4 → Z2) : BCFLUnit := by
  have b := hD0b hD0a
  have c := hD0c b
  have a2 := hA2 hA1
  have n4 := hN4 hD0a b c (hN3 hN1 hN2)
  have l2 := hL2 hD0a
  have z1 := hZ1 hD0a hT0 hA1 a2 (hA3 a2) n4 l2 (hL3 c hL1) (hL4 hD0a hA1) (quotient_integral_of_compact_open hT0 hH2U) hH3
    (measure_transport_of_open_set hT0 hD0a (hH4U hD0a hT0 hA1))
  have z2 := hZ2 l2 n4
  intro k E
  intros
  exact ⟨by apply z1 <;> assumption, by apply z2 <;> assumption⟩

end PositivityTheory.Rg.Tf.Loc
end

section
namespace PositivityTheory.Rg.Tf.Loc

theorem bcflUnit : BCFLUnit :=
  bcflUnit_of_leaves GlobalTheory.T.unramified_extension_integral_basis GlobalTheory.T.integralBasisUnramified_of_d0a GlobalTheory.T.unramified_dual_family_holds GlobalTheory.T.norm_map_torus_surjective GlobalTheory.T.separable_norm_commuting GlobalTheory.T.norm_commutes_separable_holds GlobalTheory.T.norm_centralizer_identification GlobalTheory.T.norm_map_first_property GlobalTheory.T.norm_map_second_property GlobalTheory.T.norm_map_third_property GlobalTheory.T.norm_map_integral_property GlobalTheory.T.lattice_first_property GlobalTheory.T.lattice_second_property GlobalTheory.T.lattice_third_property GlobalTheory.T.lattice_fourth_property GlobalTheory.T.unipotent_hecke_support GlobalTheory.T.hecke_third_property GlobalTheory.T.unipotent_hecke_fourth_property GlobalTheory.T.unit_fundamental_lemma_first_holds GlobalTheory.T.unit_fundamental_lemma_second_holds

end PositivityTheory.Rg.Tf.Loc
end
