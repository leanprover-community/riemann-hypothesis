module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterProperties

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.centre_character_properties : ∀ {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, (∀ z z' : hermA D ρ, chz ψ b₀ (z + z') = chz ψ b₀ z * chz ψ b₀ z') ∧ (∀ z, ‖chz ψ b₀ z‖ = 1) ∧ (∀ z ∈ ratHerm D ρ, chz ψ b₀ z = 1) ∧ Continuous (chz ψ b₀) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts
