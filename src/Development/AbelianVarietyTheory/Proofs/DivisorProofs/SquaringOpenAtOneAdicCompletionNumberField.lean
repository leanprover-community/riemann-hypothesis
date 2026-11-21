import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZeroStatement
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

noncomputable section

namespace GlobalTheory.QSA

theorem sqOpen_and_nhdsNE_zero_neBot_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  intro F _ _ v
  letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    intro h
    have h' : algebraMap F (v.adicCompletion F) 2 = algebraMap F (v.adicCompletion F) 0 := by
      rw [map_ofNat, map_zero]; exact h
    exact two_ne_zero ((algebraMap F (v.adicCompletion F)).injective h')
  refine ⟨GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero (v.adicCompletion F) h2, ?_⟩
  infer_instance

end GlobalTheory.QSA

end
end

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  atlas_forward_decl GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion
