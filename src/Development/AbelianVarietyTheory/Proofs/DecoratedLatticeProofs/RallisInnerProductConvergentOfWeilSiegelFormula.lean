import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConvergentInnerProductConjugateOrientationWeil
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelPairFlipConjugate

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Proof.Corev

theorem convergent_both_orientations :
    GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D := by
  intro hR hW hE D ψ θ A B χA χB sA sB t cA o K₁ K₂ c m ν f₁ f₂ hS hρ ht hK hm hν hf₁ hf₂
  cases o with
  | false => exact GlobalTheory.T.convergentInnerProduct_conjugateOrientation_weil hR hW hE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hρ ht hK hm hν hf₁ hf₂
  | true =>
    obtain ⟨_, _, _, hθ, _, _, hA, hB, _⟩ := id hS
    exact GlobalTheory.T.convergentInnerProduct_conjugateOrientation_weil hR hW hE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hρ ht
      (GlobalTheory.T.thetaKernelPair_flip_conjugate D ψ θ A B χA χB sA sB K₁ K₂ c hθ hA hB hK) hm hν hf₁ hf₂

end GlobalTheory.Proof.Corev
end

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallisInnerProduct_convergent_of_weilSiegelFormula : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D := by
  atlas_forward_decl GlobalTheory.Proof.Corev.convergent_both_orientations
