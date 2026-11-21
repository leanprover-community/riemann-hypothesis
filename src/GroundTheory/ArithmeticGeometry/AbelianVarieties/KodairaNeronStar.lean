import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

noncomputable section

def Scalable {𝒪 : Type*} [CommRing 𝒪] (π : 𝒪) (W : WeierstrassCurve 𝒪) : Prop :=
  π ∣ W.a₁ ∧ π ^ 2 ∣ W.a₂ ∧ π ^ 3 ∣ W.a₃ ∧ π ^ 4 ∣ W.a₄ ∧ π ^ 6 ∣ W.a₆

section Algebra

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪) {π : 𝒪}
  (hπ : Irreducible π)
include hπ






end Algebra

section Bound

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] {π : 𝒪} (hπ : Irreducible π)
include hπ

local notation "ι" => algebraMap 𝒪 K





end Bound

end

end GroundTheory.Arith.Abelian
