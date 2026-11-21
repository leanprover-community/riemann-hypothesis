import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

noncomputable section

section Roots

variable {k : Type*} [Field k] [DecidableEq k]

def quadRoots (a b c : k) : Finset k := (C a * X ^ 2 + C b * X + C c).roots.toFinset



def cubicRoots (a b c d : k) : Finset k := (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d).roots.toFinset



end Roots

section Algebra

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] (W : WeierstrassCurve 𝒪) {π : 𝒪}
  (hπ : Irreducible π)
include hπ



end Algebra

section Bound

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

def KNBound (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] (n : ℕ) : Prop :=
  Finite ((curveK K W).Point ⧸ E0 K W) ∧ Nat.card ((curveK K W).Point ⧸ E0 K W) ≤ n

variable (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic]

local notation "ι" => algebraMap 𝒪 K

theorem KNBound.mono {W : WeierstrassCurve 𝒪} [(W.map (algebraMap 𝒪 K)).IsElliptic] {n m : ℕ}
    (h : KNBound K W n) (hnm : n ≤ m) : KNBound K W m :=
  ⟨h.1, h.2.trans hnm⟩





theorem neg_notMem_E0Set {P : (curveK K W).Point} (hP : P ∉ E0Set K W) : -P ∉ E0Set K W :=
  fun h => hP (by simpa using (E0 K W).neg_mem (show -P ∈ E0 K W from h) : P ∈ E0 K W)


variable {π : 𝒪} (hπ : Irreducible π)
include hπ




end Bound

end

end GroundTheory.Arith.Abelian
