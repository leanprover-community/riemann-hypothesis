import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointwiseStabiliserParametrisationBijective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReductionSurjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemIntegralGlOfMiddleBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists

namespace Formalism.FourierDecayAlt.P.FrameLevelIndices

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_one)
open Formalism.FourierDecayAlt.S3

section Index

variable {A : Type} [CommRing A] {r k : ℕ}



theorem card_sG : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (S3x1.parG (r := r) (S3x1.gpUnit (A := A) (k := k))) := by
  refine S3x2.card_of_subgroupSet _ _ fun x => ⟨fun hx => ?_, ?_⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (S3x1.par_det S3x1.gpUnit ((S3x1.isS_iff x).1 hx)),
      (S3x1.isS_iff x).1 hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact (S3x1.isS_iff _).2 hg

end Index

section Local

variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}



end Local

noncomputable def fac (q x : ℕ) : ℝ := 1 - ((q : ℝ) ^ (x + 1))⁻¹




section Om

variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}





end Om

end Formalism.FourierDecayAlt.P.FrameLevelIndices

namespace Formalism.FourierDecayAlt.P

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.FrameLevelIndices




end Formalism.FourierDecayAlt.P
