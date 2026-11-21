import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalThetaFunctionsLevelFockDegree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunction

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_thetaFunctions_level_fockDegree : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : RealMat S) (sT : RealMat T), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ {f : WO S T → ℂ | IsThetaFunO ψ S T f ∧ (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) ∧ ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0}) := by
  first | exact @GlobalTheory.FockLevelDim.finiteDimensional_level_degree | exact GlobalTheory.FockLevelDim.finiteDimensional_level_degree | (intros; apply GlobalTheory.FockLevelDim.finiteDimensional_level_degree <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_level_compact_translates_thetaFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ K : Set (GA D S), IsCompact K → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ k ∈ K, ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (k, 1) f) = om (k, 1) f := by
  first | exact @GlobalTheory.Core.Rk.Level.exists_common_level | exact GlobalTheory.Core.Rk.Level.exists_common_level | (intros; apply GlobalTheory.Core.Rk.Level.exists_common_level <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem isKFinVec_of_isFockVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ K : Subgroup (GA D S), IsCompact (K : Set (GA D S)) → (∀ k ∈ K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ f, IsFockVec ψ θ S T sS sT f → IsKFinVec om K f := by
  intro D ψ θ S T χS χT om sS sT hW hθ hS hT K hK hc f hf
  obtain ⟨hth, N, hN⟩ := hf
  obtain ⟨U, hU, hUK⟩ := GlobalTheory.T.exists_common_level_compact_translates_thetaFunction D ψ S T χS χT om hW (K : Set (GA D S)) hK f hth
  have hfd := GlobalTheory.T.finiteDimensional_thetaFunctions_level_fockDegree D ψ θ S T sS sT hW.std hθ hS hT U hU N
  refine @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ hfd (Submodule.span_mono ?_)
  rintro g ⟨k, hk, rfl⟩
  exact ⟨hW.om_pres _ f hth, hUK k hk,
    GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ θ S T χS χT om sS sT hW hθ k (hc k hk) N f hth hN⟩

end GlobalTheory.Core.Rk.IP
end
