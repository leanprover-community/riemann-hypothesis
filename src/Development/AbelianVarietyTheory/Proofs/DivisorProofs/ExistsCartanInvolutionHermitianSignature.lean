import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionOfHasHermitianSignature
import BuildAid.ForwardExisting

section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew.CartanInv

theorem exists_isCartan : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ :=
  GlobalTheory.CartanEx.exists_isCartan

end GlobalTheory.PlaneSkew.CartanInv
end

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_hermitianSignature : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  atlas_forward_decl GlobalTheory.PlaneSkew.CartanInv.exists_isCartan
