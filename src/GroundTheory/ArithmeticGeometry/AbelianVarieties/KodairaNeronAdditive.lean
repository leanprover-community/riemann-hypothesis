import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronIstar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

noncomputable section

section Bound

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] {π : 𝒪} (hπ : Irreducible π)
include hπ

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] hπ in

theorem notScalable_vc {W : WeierstrassCurve 𝒪} (hmin : ∀ C : VariableChange 𝒪, ¬Scalable π (C • W))
    (C : VariableChange 𝒪) : ∀ C' : VariableChange 𝒪, ¬Scalable π (C' • C • W) := by
  intro C'
  rw [← mul_smul]
  exact hmin _






end Bound

end

end GroundTheory.Arith.Abelian
