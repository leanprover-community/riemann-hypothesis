import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FockSingularValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfSmulHaarEq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartanStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStableStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirCentralAndOnHighestWeight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentredHarishChandraParameterIsParamBlattner
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaExtremalFirstMember
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaMemHighestWeightSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubrepClosureAnalyticVectors
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVector
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHCModuleOfGradedDenseGK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleCompletionOfGradedIrreducibleGK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleIsHW
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactCoverUnHcModuleFiniteDimIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockTensorIntertwinerUniqueAndRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHighestWeightVectorOfKStable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KTypesUnitaryLowestWeightInCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowestKTypeOfIrreducibleGeneratedModule

section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  first | exact @GlobalTheory.ExtremalGen.exists_generated | exact GlobalTheory.ExtremalGen.exists_generated | (intros; apply GlobalTheory.ExtremalGen.exists_generated <;> assumption)
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.KilledByLowerStable

theorem act_eq_zero_of_lower {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) (hx : KilledByLower act x) (Y : Mat p q)
    (h1 : ∀ (a : Fin p) (j : Ix p q), Y (Sum.inl a) j = 0)
    (h2 : ∀ (i : Ix p q) (b : Fin q), Y i (Sum.inr b) = 0) : act Y x = 0 := by
  have hY : Y = ∑ i, ∑ j, Y i j • Eab i j := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Eab, Matrix.smul_single]
  rw [hY]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rcases i with a | b
  · rw [h1, zero_smul]
  · rcases j with a | b'
    · rw [hx a b, smul_zero]
    · rw [h2, zero_smul]

theorem killedByLower_act : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z →
    ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  intro p q V _ _ act hact Z hZ x hx a b
  have h := congrArg (fun f : Module.End ℂ V => f x) (hact (Eab (Sum.inr b) (Sum.inl a)) Z)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hx a b, map_zero, sub_zero] at h
  rw [← h]
  apply act_eq_zero_of_lower act x hx
  · intro a' j
    have h0 : Z (Sum.inl a') (Sum.inr b) = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hj : j = Sum.inl a
    · subst hj
      simp [Eab, h0]
    · simp [Eab, hj]
  · intro i b'
    have h0 : Z (Sum.inl a) (Sum.inr b') = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hi : i = Sum.inr b
    · subst hi
      simp [Eab, h0]
    · simp [Eab, hi]

end GlobalTheory.KilledByLowerStable
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKilledByLowerNilradical_act_blockDiagonal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z → ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  atlas_forward_decl GlobalTheory.KilledByLowerStable.killedByLower_act
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CasimirLowest

open GlobalTheory.CasimirHighest

theorem casimir_on_vector {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (Λ : Ix p q → ℚ) (e : V)
    (hv : e ∈ hwSub act Λ) (hk : KilledByLower act e) :
    casimir act e = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • e := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
  obtain ⟨hw, hr⟩ := hv
  have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
    (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) e
    (fun i => Λ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
    (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) e
    (fun i => Λ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h3 : ∀ (a : Fin p) (b : Fin q),
      act (Eab (.inl a) (.inr b)) (act (Eab (.inr b) (.inl a)) e) = 0 := by
    intro a b; rw [hk a b, map_zero]
  have h4 : ∀ (b : Fin q) (a : Fin p),
      act (Eab (.inr b) (.inl a)) (act (Eab (.inl a) (.inr b)) e) =
        ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e := by
    intro b a
    have h5 := congrArg (fun f : Module.End ℂ V => f e)
      (act_Eab_comm h (.inr b) (.inl a) (.inl a) (.inr b))
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, h3, sub_zero, hw] at h5
    rw [h5, Rat.cast_sub, sub_smul]
  have h6 : ∑ b : Fin q, ∑ a : Fin p, ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e =
      ((∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) : ℚ) : ℂ) • e := by
    simp only [Rat.cast_sum, Finset.sum_smul]
  simp only [casimir, LinearMap.sum_apply, LinearMap.add_apply, Module.End.mul_apply,
    Fintype.sum_sum_type, Finset.sum_add_distrib, h3, h4, Finset.sum_const_zero, zero_add]
  rw [h1, h2, h6, ← add_smul, ← add_smul, ← Rat.cast_add, ← Rat.cast_add]
  congr 2
  have e1 : ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) =
      ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ)) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ)) =
      ∑ j : Fin q, Λ (Sum.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ)) + p * ∑ j : Fin q, Λ (Sum.inr j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) =
      p * ∑ j : Fin q, Λ (Sum.inr j) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
  rw [e1, e2, e3]
  ring

theorem casimir_on_generated : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  intro p q V _ _ act h Λ e hv hk hg x
  have he := casimir_on_vector h Λ e hv hk
  generalize (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) = c at he ⊢
  have hc := (casimir_central_and_highest p q V act h).1
  have hle : genSub act {e} ≤ LinearMap.ker (casimir act - c • LinearMap.id) := by
    refine sInf_le ⟨?_, ?_⟩
    · rintro y rfl
      simp [he]
    · intro Z y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hy ⊢
      have := congrArg (fun f : Module.End ℂ V => f y) (hc Z)
      simp only [Module.End.mul_apply] at this
      rw [this, hy, map_smul]
  have hx := hle (hg ▸ Submodule.mem_top : x ∈ genSub act {e})
  simpa [sub_eq_zero] using hx

end GlobalTheory.CasimirLowest
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_scalar_on_module_generated_killedByLower : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  atlas_forward_decl GlobalTheory.CasimirLowest.casimir_on_generated
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem normSq_hcParam_sub_rhoSq (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  have hr : rhoSq (p + q) = ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2
      + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    unfold rhoSq
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2) p,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) + q - 1) / 2 - (i : ℕ)) ^ 2) q,
      Nat.add_comm p q, Finset.sum_range_add, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> push_cast <;> ring
  rw [hr]
  unfold normSq
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ i : Fin p, hcParam n ap am (Sum.inl i) ^ 2
      = ∑ i : Fin p, wtK n ap am (Sum.inl i) ^ 2
        + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ))
        + ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  have h2 : ∑ j : Fin q, hcParam n ap am (Sum.inr j) ^ 2
      = ∑ j : Fin q, wtK n ap am (Sum.inr j) ^ 2
        + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))
        + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  rw [h1, h2]
  ring

end GlobalTheory
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_centredHarishChandraParameter_sub_rhoSq : ∀ (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ), normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  atlas_forward_decl GlobalTheory.normSq_hcParam_sub_rhoSq
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm

namespace GlobalTheory.HarmonicShape

theorem weight_eq_wtK (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
    (μ : Ix p q → ℚ) (P : Pol p q n 0) (h1 : IsHW (fockAct1 p q n 0) μ P)
    (h2 : P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am))
    (h3 : KilledByLower (fockAct1 p q n 0) P) : μ = wtK n ap am := by
  have hj : P ∈ jointHW μ (wtH n ap am) := by
    refine ⟨⟨h1.2, h2⟩, ⟨fun a b => ?_, fun a b => by simp⟩, fun _ j => j.elim0, fun i => i.elim0⟩
    have := h3 a b
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero] at this
    exact this
  obtain ⟨α, β, γ, δ, ⟨-, -, -, -, a1, b1, c1, d1, -, -, -, -, e1, e2, e3, -⟩, -⟩ :=
    four_of_joint h1.1 hj
  funext x
  rcases x with i | j
  · have hi := i.2
    have u := e1 i
    have v := e3 ⟨i.1, by omega⟩
    rw [b1 _ (by simp)] at u
    rw [d1 _ ((min_le_left _ _).trans (by rw [Fin.val_rev]; dsimp only; omega))] at v
    simp only [shiftNu, cPair, wtH, hi, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith
  · have hj := j.2
    have hr := j.rev.2
    have u := e2 j
    have v := e3 (Fin.rev ⟨j.rev.1, by omega⟩)
    have hp : ¬ (Fin.rev (⟨j.rev.1, by omega⟩ : Fin n)).1 < p := by
      rw [Fin.val_rev]; dsimp only; omega
    rw [c1 _ (by simp)] at u
    rw [a1 _ ((min_le_left _ _).trans (not_lt.1 hp))] at v
    simp only [shiftNu, cPair, wtH, dif_neg hp, Fin.rev_rev, hr, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith

end GlobalTheory.HarmonicShape
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_highestWeight_eq_lowestKTypeHighestWeight : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (μ : Ix p q → ℚ) (P : Pol p q n 0), IsHW (fockAct1 p q n 0) μ P → P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) → KilledByLower (fockAct1 p q n 0) P → μ = wtK n ap am := by
  atlas_forward_decl GlobalTheory.HarmonicShape.weight_eq_wtK
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GradedCentralCircle

open GlobalTheory.RealPar

variable {p q : ℕ}

theorem flow_eq {T : GrpData p q} (σ : URep T) {X : Mat p q} (hX : X ∈ upq p q) {w : σ.H} {c : ℂ}
    (h0 : HasDerivAt (fun t : ℝ => σ.π (T.expt (t • X)) w) (c • w) 0) :
    σ.π (T.expt X) w = Complex.exp c • w := by
  set f : ℝ → σ.H := fun t => σ.π (T.expt (t • X)) w with hf
  have hd : ∀ t, HasDerivAt f (c • f t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) (c • w) t := by
      have := HasDerivAt.comp_sub_const t t (f := f) (f' := c • w) (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((σ.π (T.expt (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    convert h2 using 1
    · funext s
      simp only [hf, Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    · simp [hf]
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    convert h1.fun_smul (hd t) using 1
    rw [smul_smul, ← add_smul]; simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, ContinuousLinearMap.one_apply] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem exp_injective (c : ℂ) : Function.Injective fun m : ℕ => Complex.exp (Complex.I * (c + m)) := by
  intro m n h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h1 : ((m : ℝ) : ℂ) - (n : ℝ) = ((k : ℝ) * 2 * Real.pi : ℝ) := by
    push_cast
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination hk
  have h2 : (m : ℝ) - n = (k : ℝ) * 2 * Real.pi := by exact_mod_cast h1
  by_cases hk0 : k = 0
  · subst hk0
    have : (m : ℝ) = n := by simpa [sub_eq_zero] using h2
    exact_mod_cast this
  · exfalso
    have hi : Irrational (((k * 2 : ℤ) : ℝ) * Real.pi) :=
      irrational_pi.intCast_mul (by omega)
    have : ((k * 2 : ℤ) : ℝ) * Real.pi = ((m - n : ℤ) : ℝ) := by push_cast; linarith
    rw [this] at hi
    exact Int.not_irrational _ hi

theorem exists_central_eigen : ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (c : ℚ), (∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = ((c : ℂ) + m) • x) → ∃ k ∈ T.Kset, ∃ lam : ℕ → ℂ, Function.Injective lam ∧ ∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x := by
  intro p q T σ M j hj N c hN
  set θ : Ix p q → ℝ := Sum.elim (fun _ => 1) (fun _ => 0) with hθ
  have hX := TorusWt.torX_mem θ
  have hK : IsKC (TorusWt.torX θ) := by
    intro a b hab
    have : a ≠ b := by
      rintro rfl
      cases a <;> simp [sameBlock] at hab
    simp [TorusWt.torX, this]
  have hk := KStabLie.expt_mem T hX hK 1
  rw [one_smul] at hk
  refine ⟨_, hk, _, exp_injective (c : ℂ), fun m x hx => ?_⟩
  apply flow_eq σ hX
  have h0 := hj _ hX x
  have h1 : M.act (TorusWt.torX θ) x = (Complex.I * ((c : ℂ) + m)) • x := by
    rw [TorusWt.torX_eq_sum, map_sum, LinearMap.sum_apply, Fintype.sum_sum_type, mul_smul, ← hN m x hx,
      Finset.smul_sum]
    simp [hθ]
  rw [h1, map_smul] at h0
  exact h0

end GlobalTheory.GradedCentralCircle
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_circle_distinct_graded_eigen : ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (c : ℚ), (∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = ((c : ℂ) + m) • x) → ∃ k ∈ T.Kset, ∃ lam : ℕ → ℂ, Function.Injective lam ∧ ∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x := by
  atlas_forward_decl GlobalTheory.GradedCentralCircle.exists_central_eigen
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod pOf)
open GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix

namespace GlobalTheory.CoshSqInt

variable {p q : ℕ}

theorem pOf_mem_pR (B : Matrix (Fin p) (Fin q) ℂ) : pOf B ∈ pR p q := by
  refine ⟨?_, ?_⟩
  · change (pOf B)ᴴ * Jm p q + Jm p q * pOf B = 0
    rw [(pOf_herm B).eq]
    simp [pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp [pOf]

theorem exists_cartan (T : GrpData p q) (g : T.G) :
    ∃ k ∈ T.Kset, g = k * T.expt (pOf (cartanB (T.covU g))) := by
  set B := cartanB (T.covU g) with hB
  refine ⟨g * (T.expt (pOf B))⁻¹, ?_, by simp⟩
  obtain ⟨k₁, -, k₂, -, h⟩ := isCartan_cartanB (T.covU g)
  have h1 : ((T.cov g : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.fromBlocks k₁ 0 0 k₂ * ((T.cov (T.expt (pOf B)) : GL (Ix p q) ℂ) : Mat p q) := by
    rw [T.expt_cov _ (pOf_mem_pR B).1]; exact h
  have h2 : ((T.cov (g * (T.expt (pOf B))⁻¹) : GL (Ix p q) ℂ) : Mat p q) = Matrix.fromBlocks k₁ 0 0 k₂ := by
    rw [map_mul, map_inv, Units.val_mul, h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  change IsKC _
  rw [h2]
  rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp

theorem decay_sq (n : ℕ) (g : Formalism.BasicNotions.UpqT p q) :
    decay n (pOf (cartanB g)) ^ 2 = coshPow (2 * (n : ℝ)) g := by
  unfold decay coshPow singVal
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (pOf (cartanB g)).toBlocks₁₂ = cartanB g := by simp [pOf]
  rw [this, Real.rpow_neg (Real.cosh_pos _).le, inv_pow, ← pow_mul, mul_comm n 2]
  congr 1
  rw [← Real.rpow_natCast]; push_cast; rfl

theorem memLp_two_of_decay : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n →
    ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f →
    (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  intro hI p q n hn T f C hf hd
  obtain ⟨m, hm⟩ := GlobalTheory.MinfMeasure.exists_isMinf p q
  have hc : 2 * (((p + q : ℕ) : ℝ) - 1) < 2 * (n : ℝ) := by
    have : ((p + q : ℕ) : ℝ) < n := by exact_mod_cast hn
    linarith
  have h1 := hI.1 p q m hm _ hc
  haveI := hm.1
  haveI := GlobalTheory.DetSqrtCover.isHaarMeasure_map_covU T
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.CompactDualUnique.exists_eq_smul (T.haar.map T.covU) m
  have h2 : Integrable (coshPow (2 * (n : ℝ))) (T.haar.map T.covU) := by
    rw [ht]; exact h1.smul_measure_nnreal
  have h3 : Integrable (coshPow (2 * (n : ℝ)) ∘ T.covU) T.haar :=
    h2.comp_measurable (GlobalTheory.DetSqrtCover.continuous_covU T).measurable
  have hfm : AEStronglyMeasurable f T.haar := hf.measurable.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hfm]
  refine (h3.const_mul (C ^ 2)).mono' (hfm.norm.pow 2) (Filter.Eventually.of_forall fun g => ?_)
  obtain ⟨k, hk, hg⟩ := exists_cartan T g
  have h4 := hd k hk _ (pOf_mem_pR (cartanB (T.covU g)))
  rw [← hg] at h4
  rw [Real.norm_of_nonneg (by positivity), Function.comp_apply, ← decay_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h4 2

end GlobalTheory.CoshSqInt
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memLp_two_of_cosh_decay_unitaryPQCover : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n → ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f → (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  atlas_forward_decl GlobalTheory.CoshSqInt.memLp_two_of_decay
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockBilin

theorem gen_ind {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x₀ : V) (h : genSub act {x₀} = ⊤)
    (N : Submodule ℂ V) (h0 : x₀ ∈ N) (hs : ∀ Z, ∀ y ∈ N, act Z y ∈ N) (x : V) : x ∈ N := by
  have hle : genSub act {x₀} ≤ N := sInf_le ⟨by simpa using h0, hs⟩
  rw [h] at hle
  exact hle Submodule.mem_top

theorem uniq {p q : ℕ} {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ U) (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (x₀ : U)
    (h : genSub act {x₀} = ⊤) (f g : U →ₗ[ℂ] V)
    (hf : ∀ Z x, f (act Z x) = a Z (f x)) (hg : ∀ Z x, g (act Z x) = a Z (g x))
    (h0 : f x₀ = g x₀) : f = g := by
  ext x
  have := gen_ind act x₀ h (LinearMap.eqLocus f g) h0 (fun Z y hy => by
    rw [LinearMap.mem_eqLocus] at hy ⊢
    rw [hf, hg, hy]) x
  exact this

theorem exists_bilin : ∀ (p q r s : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ V), (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → ∀ (M₁ : GKMod p q) (M₂ : GKMod r s) (i₁ : M₁.V →ₗ[ℂ] V) (i₂ : M₂.V →ₗ[ℂ] V), (∀ Z x, i₁ (M₁.act Z x) = a₁ Z (i₁ x)) → (∀ Z y, i₂ (M₂.act Z y) = a₂ Z (i₂ y)) → ∀ (x₀ : M₁.V) (y₀ : M₂.V), genSub M₁.act {x₀} = ⊤ → genSub M₂.act {y₀} = ⊤ → i₁ x₀ = i₂ y₀ → ∃ I : M₁.V ⊗[ℂ] M₂.V →ₗ[ℂ] V, (∀ Z x y, a₁ Z (I (x ⊗ₜ y)) = I (M₁.act Z x ⊗ₜ y)) ∧ (∀ Z x y, a₂ Z (I (x ⊗ₜ y)) = I (x ⊗ₜ M₂.act Z y)) ∧ (∀ x, I (x ⊗ₜ y₀) = i₁ x) ∧ ∀ y, I (x₀ ⊗ₜ y) = i₂ y := by
  intro p q r s V _ _ a₁ a₂ hc M₁ M₂ i₁ i₂ h₁ h₂ x₀ y₀ g₁ g₂ h0
  have hc' : ∀ Y Z v, a₁ Y (a₂ Z v) = a₂ Z (a₁ Y v) := fun Y Z v =>
    LinearMap.congr_fun (hc Y Z) v
  let N : Submodule ℂ M₂.V :=
    { carrier := {y | ∃ f : M₁.V →ₗ[ℂ] V, (∀ Z x, f (M₁.act Z x) = a₁ Z (f x)) ∧ f x₀ = i₂ y}
      add_mem' := by
        rintro y y' ⟨f, hf, e⟩ ⟨g, hg, e'⟩
        exact ⟨f + g, fun Z x => by simp [hf, hg], by simp [e, e']⟩
      zero_mem' := ⟨0, by simp, by simp⟩
      smul_mem' := by
        rintro c y ⟨f, hf, e⟩
        exact ⟨c • f, fun Z x => by simp [hf], by simp [e]⟩ }
  have hN : ∀ y, ∃ f : M₁.V →ₗ[ℂ] V, (∀ Z x, f (M₁.act Z x) = a₁ Z (f x)) ∧ f x₀ = i₂ y := by
    intro y
    refine gen_ind M₂.act y₀ g₂ N ⟨i₁, h₁, h0⟩ ?_ y
    rintro Z y ⟨f, hf, e⟩
    exact ⟨a₂ Z ∘ₗ f, fun Y x => by simp [hf, hc'], by simp [e, h₂]⟩
  choose F hF hF0 using hN
  have u := uniq M₁.act a₁ x₀ g₁
  have hadd : ∀ y y', F (y + y') = F y + F y' := fun y y' =>
    u _ _ (hF _) (fun Z x => by simp [hF]) (by simp [hF0])
  have hsmul : ∀ (c : ℂ) y, F (c • y) = c • F y := fun c y =>
    u _ _ (hF _) (fun Z x => by simp [hF]) (by simp [hF0])
  have hact : ∀ Z y, F (M₂.act Z y) = a₂ Z ∘ₗ F y := fun Z y =>
    u _ _ (hF _) (fun Y x => by simp [hF, hc']) (by simp [hF0, h₂])
  have hy0 : F y₀ = i₁ := u _ _ (hF _) h₁ (by rw [hF0, h0])
  let G : M₂.V →ₗ[ℂ] M₁.V →ₗ[ℂ] V := { toFun := F, map_add' := hadd, map_smul' := hsmul }
  have hG : ∀ x y, TensorProduct.lift G.flip (x ⊗ₜ y) = F y x := fun x y => by
    simp [G]
  refine ⟨TensorProduct.lift G.flip, ?_, ?_, ?_, ?_⟩
  · intro Z x y; rw [hG, hG, hF]
  · intro Z x y; rw [hG, hG, hact]; rfl
  · intro x; rw [hG, hy0]
  · intro y; rw [hG, hF0]

end GlobalTheory.FockBilin
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_tensor_map_of_cyclic_commuting : ∀ (p q r s : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ V), (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → ∀ (M₁ : GKMod p q) (M₂ : GKMod r s) (i₁ : M₁.V →ₗ[ℂ] V) (i₂ : M₂.V →ₗ[ℂ] V), (∀ Z x, i₁ (M₁.act Z x) = a₁ Z (i₁ x)) → (∀ Z y, i₂ (M₂.act Z y) = a₂ Z (i₂ y)) → ∀ (x₀ : M₁.V) (y₀ : M₂.V), genSub M₁.act {x₀} = ⊤ → genSub M₂.act {y₀} = ⊤ → i₁ x₀ = i₂ y₀ → ∃ I : M₁.V ⊗[ℂ] M₂.V →ₗ[ℂ] V, (∀ Z x y, a₁ Z (I (x ⊗ₜ y)) = I (M₁.act Z x ⊗ₜ y)) ∧ (∀ Z x y, a₂ Z (I (x ⊗ₜ y)) = I (x ⊗ₜ M₂.act Z y)) ∧ (∀ x, I (x ⊗ₜ y₀) = i₁ x) ∧ ∀ y, I (x₀ ⊗ₜ y) = i₂ y := by
  atlas_forward_decl GlobalTheory.FockBilin.exists_bilin
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockForm

theorem act_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {x : V} (h : x ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  have := (Submodule.mem_iInf _).1 h a
  simpa [LinearMap.mem_ker, sub_eq_zero] using this

theorem form_eq_zero {p q : ℕ} (M : GKMod p q) (D : M.V → M.V → ℂ)
    (hadd₁ : ∀ x x' y, D (x + x') y = D x y + D x' y)
    (hsmul₁ : ∀ (c : ℂ) x y, D (c • x) y = star c * D x y)
    (hadd₂ : ∀ x y y', D x (y + y') = D x y + D x y')
    (hsmul₂ : ∀ (c : ℂ) x y, D x (c • y) = c * D x y)
    (hinv : ∀ Z x y, D (M.act Z x) y = D x (M.act (adjZ Z) y))
    (μ : Ix p q → ℚ) (v : M.V) (hv : v ∈ wtSub M.act μ)
    (hline : ∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) (hgen : genSub M.act {v} = ⊤)
    (hvv : D v v = 0) : ∀ x y, D x y = 0 := by
  have hv0 : ∀ y, D v y = 0 := by
    intro y
    refine Submodule.iSup_induction (motive := fun y => D v y = 0) _ (M.wts y) ?_ ?_ ?_
    · intro ν y hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, rfl⟩ := hline y hy
        rw [hsmul₂, hvv, mul_zero]
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h := hinv (Eab a a) v y
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_of_mem_wtSub hv, act_of_mem_wtSub hy, hsmul₁, hsmul₂] at h
        have hs : star ((μ a : ℚ) : ℂ) = ((μ a : ℚ) : ℂ) := by simp
        rw [hs] at h
        have hne : ((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha.symm
        have : (((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ)) * D v y = 0 := by linear_combination h
        exact (mul_eq_zero.1 this).resolve_left hne
    · have := hsmul₂ 0 v 0
      simpa using this
    · intro y y' h h'
      rw [hadd₂, h, h', add_zero]
  let N : Submodule ℂ M.V :=
    { carrier := {x | ∀ y, D x y = 0}
      add_mem' := fun {x x'} h h' y => by rw [hadd₁, h y, h' y, add_zero]
      zero_mem' := fun y => by simpa using hsmul₁ 0 0 y
      smul_mem' := fun c x h y => by rw [hsmul₁, h y, mul_zero] }
  have hN : genSub M.act {v} ≤ N := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact hv0
    · intro Z x hx y
      rw [hinv]
      exact hx _
  intro x y
  exact hN (hgen ▸ Submodule.mem_top) y

theorem inner_eq_mul : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j : M.V →ₗ[ℂ] H₁) (E₁ E₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (M.act (adjZ Z) y))) → ∀ (μ : Ix p q → ℚ) (v : M.V), v ∈ wtSub M.act μ → (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) → genSub M.act {v} = ⊤ → ‖j v‖ = 1 → ∀ x y, inner ℂ (E₁ x) (E₂ y) = inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y) := by
  intro p q M H₁ _ _ H₂ _ _ j E₁ E₂ hj hE μ v hv hline hgen hnorm x y
  have := form_eq_zero M
    (fun x y => inner ℂ (E₁ x) (E₂ y) - inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y))
    (fun x x' y => by simp only [map_add, inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_left, starRingEnd_apply]; ring)
    (fun x y y' => by simp only [map_add, inner_add_right]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_right]; ring)
    (fun Z x y => by simp only [hj, hE])
    μ v hv hline hgen (by simp [inner_self_eq_norm_sq_to_K, hnorm]) x y
  exact sub_eq_zero.1 this

end GlobalTheory.FockForm
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_inner_forms_proportional_weight_line : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j : M.V →ₗ[ℂ] H₁) (E₁ E₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (M.act (adjZ Z) y))) → ∀ (μ : Ix p q → ℚ) (v : M.V), v ∈ wtSub M.act μ → (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) → genSub M.act {v} = ⊤ → ‖j v‖ = 1 → ∀ x y, inner ℂ (E₁ x) (E₂ y) = inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y) := by
  atlas_forward_decl GlobalTheory.FockForm.inner_eq_mul
end

section
section
open Formalism.BasicNotions.TH

namespace GlobalTheory

theorem mat_compact_eq_sum_units {n : ℕ} (Z : Mat n 0) :
    Z = ∑ a : Fin n, ∑ b : Fin n,
      Z (Sum.inl a) (Sum.inl b) • Eab (Sum.inl a : Ix n 0) (Sum.inl b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Eab,
    Matrix.smul_single, smul_eq_mul, mul_one]

theorem gkMod_compact_glRel {n : ℕ} (M : GKMod n 0) :
    Formalism.REAL.GlRel (fun a b : Fin n => M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b))) := by
  intro a b c d
  show M.act _ * M.act _ - M.act _ * M.act _ = _
  rw [← M.lie, map_sub]
  congr 1
  · split_ifs with h
    · subst h; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne, map_zero]
      intro h'; exact h (Sum.inl_injective h')
  · split_ifs with h
    · subst h; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne, map_zero]
      intro h'; exact h (Sum.inl_injective h')

theorem gkMod_compact_irr_units {n : ℕ} (M : GKMod n 0) (h : Formalism.MainNotions.SchurIrreducible.IrrGK M)
    (S : Submodule ℂ M.V)
    (hS : ∀ a b : Fin n, ∀ x ∈ S, M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b)) x ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  refine h.2 S fun Z y hy => ?_
  rw [mat_compact_eq_sum_units Z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b y hy)

theorem gkMod_compact_isHW_units {n : ℕ} (M : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V)
    (h : IsHW M.act Λ v) :
    Formalism.REAL.IsHW (fun a b : Fin n => M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b)))
      (fun a => ((Λ (Sum.inl a) : ℚ) : ℂ)) v := by
  obtain ⟨-, h1, h2⟩ := h
  simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1 h2
  exact ⟨fun a => h1 _, fun a b hab => h2 (Sum.inl a) (Sum.inl b) hab⟩

theorem exists_intertwiner_map_highestVector :
    ∀ (n : ℕ) (M M' : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V) (v' : M'.V),
      Formalism.MainNotions.SchurIrreducible.IrrGK M → Formalism.MainNotions.SchurIrreducible.IrrGK M' → IsHW M.act Λ v → IsHW M'.act Λ v' →
      ∃ f : M.V →ₗ[ℂ] M'.V, f v = v' ∧ ∀ Z x, f (M.act Z x) = M'.act Z (f x) := by
  intro n M M' Λ v v' hM hM' hv hv'
  have w := gkMod_compact_isHW_units M Λ v hv
  have w' := gkMod_compact_isHW_units M' Λ v' hv'
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_irreducible_isHW M.V M'.V n _ _ _ v v'
    (gkMod_compact_glRel M) (gkMod_compact_glRel M') (gkMod_compact_irr_units M hM)
    (gkMod_compact_irr_units M' hM') w w' hv.1 hv'.1
  obtain ⟨S, hS, hvS, htop⟩ :=
    exists_stable_submodule_topWeight_line M'.V n _ _ v' (gkMod_compact_glRel M') w'
  have hStop : S = ⊤ := by
    rcases gkMod_compact_irr_units M' hM' S hS with h | h
    · rw [h, Submodule.mem_bot] at hvS
      exact absurd hvS hv'.1
    · exact h
  obtain ⟨c, hc⟩ := htop (T v) (by rw [hStop]; trivial) (fun a => by
    rw [← hT a a v, w.1 a, map_smul])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, map_eq_zero_iff T T.injective] at hc
    exact hv.1 hc
  refine ⟨c⁻¹ • T.toLinearMap, ?_, fun Z x => ?_⟩
  · simp [hc, smul_smul, hc0]
  · have key : T (M.act Z x) = M'.act Z (T x) := by
      rw [mat_compact_eq_sum_units Z]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hT a b x]
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, key, map_smul]

end GlobalTheory
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_map_highestWeightVector_compact : ∀ (n : ℕ) (M M' : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V) (v' : M'.V), IrrGK M → IrrGK M' → IsHW M.act Λ v → IsHW M'.act Λ v' → ∃ f : M.V →ₗ[ℂ] M'.V, f v = v' ∧ ∀ Z x, f (M.act Z x) = M'.act Z (f x) := by
  atlas_forward_decl GlobalTheory.exists_intertwiner_map_highestVector
end

section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCoverUn_hcModule_finiteDim_irreducible : ∀ (n : ℕ), 1 ≤ n → ∀ (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H), IrrU τ → IsHCMod τ M j → Nontrivial M.V → FiniteDimensional ℂ M.V ∧ IrrGK M ∧ (∀ h v, ∃ v', j v' = τ.π h (j v)) ∧ ∀ N : Submodule ℂ M.V, (∀ h, ∀ v ∈ N, ∀ v', j v' = τ.π h (j v) → v' ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.CompactCoverIrr.hcMod_finite_irr | exact GlobalTheory.CompactCoverIrr.hcMod_finite_irr | (intros; apply GlobalTheory.CompactCoverIrr.hcMod_finite_irr <;> assumption)
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockIrr

theorem act_diag_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} (h : v ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  have h1 := (Submodule.mem_iInf _).1 h a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
  exact sub_eq_zero.1 h1

theorem irreducible_of_weight_line : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  intro p q M H _ _ E hE hadj S hS μ v U hv hU hline N hNU hN
  by_cases hvN : v ∈ N
  · exact Or.inr (le_antisymm hNU (hU N hvN hN))
  left
  have horth : ∀ x ∈ N, inner ℂ (E x) (E v) = 0 := by
    intro x hx
    have hx' := GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable p q M.V M.act N (fun a => hN a a (hS.refl a)) x hx (M.wts x)
    clear hx
    induction hx' using Submodule.iSup_induction' with
    | mem ν y hy =>
      obtain ⟨hyN, hyν⟩ := hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, hc⟩ := hline y (hNU hyN) hyν
        by_cases hc0 : c = 0
        · simp [hc, hc0]
        · exfalso
          apply hvN
          have : v = c⁻¹ • y := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
          rw [this]
          exact N.smul_mem _ hyN
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h1 := hadj (Eab a a) y v
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_diag_of_mem_wtSub hyν, act_diag_of_mem_wtSub hv, map_smul, map_smul,
          inner_smul_left, inner_smul_right, map_ratCast] at h1
        have hne : ((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha
        have h2 : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) * inner ℂ (E y) (E v) = 0 := by
          rw [sub_mul, h1, sub_self]
        exact (mul_eq_zero.1 h2).resolve_left hne
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, inner_add_left, hy, hz, add_zero]
  let U' : Submodule ℂ M.V :=
    { carrier := {y | ∀ x ∈ N, inner ℂ (E x) (E y) = 0}
      add_mem' := fun {y z} hy hz x hx => by
        rw [map_add, inner_add_right, hy x hx, hz x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun c y hy x hx => by
        rw [map_smul, inner_smul_right, hy x hx, mul_zero] }
  have hUU' : U ≤ U' := by
    refine hU U' horth ?_
    intro a b hab y hy x hx
    have h1 := hadj (adjZ (Eab a b)) x y
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at h1
    rw [← h1]
    apply hy
    rw [GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (hN b a (hS.symm hab) x hx)
  rw [eq_bot_iff]
  intro x hx
  have h0 : inner ℂ (E x) (E x) = 0 := hUU' (hNU hx) x hx
  rw [inner_self_eq_zero] at h0
  exact (Submodule.mem_bot ℂ).2 (hE (by rw [h0, map_zero]))

end GlobalTheory.FockIrr
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  atlas_forward_decl GlobalTheory.FockIrr.irreducible_of_weight_line
end

section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highestWeight_vector_of_KStable : ∀ (p q : ℕ) (M : GKMod p q) (W : Submodule ℂ M.V), FiniteDimensional ℂ W → KStable M.act W → W ≠ ⊥ → ∃ (μ : Ix p q → ℚ) (v : M.V), v ∈ W ∧ IsHW M.act μ v := by
  first | exact @GlobalTheory.ExistsHW.exists_highestWeight | exact GlobalTheory.ExistsHW.exists_highestWeight | (intros; apply GlobalTheory.ExistsHW.exists_highestWeight <;> assumption)
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GKSubmodule

noncomputable def resAct {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) : Mat p q →ₗ[ℂ] Module.End ℂ N where
  toFun Z := (M.act Z).restrict (h Z)
  map_add' X Y := by
    ext x
    simp [LinearMap.restrict_apply]
  map_smul' c X := by
    ext x
    simp [LinearMap.restrict_apply]

theorem resAct_coe {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) (Z : Mat p q) (x : N) :
    ((resAct M N h Z x : N) : M.V) = M.act Z x := rfl

theorem exists_submodule : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), (∀ Z, ∀ x ∈ N, M.act Z x ∈ N) → ∃ (M' : GKMod p q) (i : M'.V →ₗ[ℂ] M.V), Function.Injective i ∧ LinearMap.range i = N ∧ ∀ Z x, i (M'.act Z x) = M.act Z (i x) := by
  intro p q M N h
  have hlie : IsLieAct (resAct M N h) := by
    intro X Y
    ext x
    have := congrArg (fun f : Module.End ℂ M.V => f x) (M.lie X Y)
    simpa [resAct_coe] using this
  have hk : ∀ v : N, ∃ W : Submodule ℂ N, FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (resAct M N h) W := by
    intro v
    obtain ⟨W, hW, hv, hs⟩ := M.kfin v
    refine ⟨W.comap N.subtype, ?_, hv, ?_⟩
    · exact Module.Finite.of_injective
        (N.subtype.restrict (p := W.comap N.subtype) (q := W) (fun x hx => hx))
        (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z : W => (z : M.V)) hab)))
    · intro X hX w hw
      exact hs X hX w hw
  have hw : ∀ v : N, v ∈ ⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ := by
    intro v
    have h1 := GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable p q M.V M.act N (fun a => h _) v v.2 (M.wts v)
    have h2 : (⨆ μ : Ix p q → ℚ, N ⊓ wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ).map N.subtype := by
      refine iSup_le fun μ x hx => ?_
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      refine Submodule.mem_iSup_of_mem μ ?_
      have hx2 := hx.2
      simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
      intro a
      apply Subtype.ext
      simpa [resAct_coe] using hx2 a
    obtain ⟨y, hy, hyv⟩ := h2 h1
    have : y = v := Subtype.ext hyv
    exact this ▸ hy
  exact ⟨{ V := N, act := resAct M N h, lie := hlie, kfin := hk, wts := hw }, N.subtype,
    N.injective_subtype, N.range_subtype, fun _ _ => rfl⟩

end GlobalTheory.GKSubmodule
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gkMod_injective_range_eq_of_act_stable : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), (∀ Z, ∀ x ∈ N, M.act Z x ∈ N) → ∃ (M' : GKMod p q) (i : M'.V →ₗ[ℂ] M.V), Function.Injective i ∧ LinearMap.range i = N ∧ ∀ Z x, i (M'.act Z x) = M.act Z (i x) := by
  atlas_forward_decl GlobalTheory.GKSubmodule.exists_submodule
end

section
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockExtGroup

theorem pi_comm {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) (g : T1.G) (h : T2.G) (x : F.H) :
    F.π (g, 1) (F.π (1, h) x) = F.π (1, h) (F.π (g, 1) x) := by
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul]
  simp

theorem comm_and_extend : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2), 1 ≤ n → ∀ (D : DSRep T1) (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (v₀ : M.V), IrrU τ → IsHCMod τ M j → v₀ ≠ 0 → IsGIntw F D.HK M I → (∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v₀))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) → (∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) → F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v'))) ∧ ∀ v : M.V, ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y) := by
  intro p q n T0 T1 T2 F hn D τ M j I v₀ hτ hM hv₀ hI hJ
  obtain ⟨hfin, -, -, hirr⟩ := GlobalTheory.CompactCoverIrr.hcMod_finite_irr n hn T2 τ M j hτ hM ⟨v₀, 0, hv₀⟩
  obtain ⟨hF, -, hder⟩ := GlobalTheory.FockEmbExp.fock_derived p q n 0 T0 T1 T2 F
  let σ : URep T2 :=
    { H := F.H
      π := F.π.comp (MonoidHom.inr _ _)
      isom := fun _ x => F.isom _ x
      cont := fun x => (F.cont x).comp (hF.comp (continuous_const.prodMk continuous_id)) }
  have h1 : ∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) →
      F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v')) := by
    intro h x v v' hv
    have hK : h ∈ T2.Kset := by
      rintro (a | a) (b | b) hab
      · exact (hab trivial).elim
      · exact b.elim0
      · exact a.elim0
      · exact a.elim0
    let j₂ : M.V →ₗ[ℂ] σ.H := F.ι ∘ₗ I ∘ₗ TensorProduct.mk ℂ D.HK.V M.V x
    obtain ⟨w, hw1, hw2⟩ := GlobalTheory.RealPar.pair_kEquivariant_of_lie n 0 T2
      (GlobalTheory.CoverKGen.kset_gen n 0 (by omega) T2) τ σ M.V (fun Y => M.act Y) j j₂
      (fun Y hY _ w => ⟨hM.2.2 Y hY w, by
        have h2 := hder Y hY (I (x ⊗ₜ w))
        have h3 : fockAct2 p q n 0 Y (I (x ⊗ₜ w)) = I (x ⊗ₜ M.act Y w) := hI.2 Y x w
        rw [h3] at h2
        exact h2⟩) h hK v
    obtain rfl : v' = w := hM.1 (hv.trans hw1)
    exact hw2
  refine ⟨h1, ?_⟩
  let N : Submodule ℂ M.V :=
    { carrier := {v | ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧
        ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)}
      add_mem' := by
        rintro a b ⟨J, hJ1, hJ2⟩ ⟨J', hJ1', hJ2'⟩
        exact ⟨J + J', fun x => by simp [hJ1, hJ1', TensorProduct.tmul_add],
          fun g y => by simp [hJ2, hJ2']⟩
      zero_mem' := ⟨0, fun x => by simp, fun g y => by simp⟩
      smul_mem' := by
        rintro c a ⟨J, hJ1, hJ2⟩
        exact ⟨c • J, fun x => by simp [hJ1, TensorProduct.tmul_smul],
          fun g y => by simp [hJ2]⟩ }
  rcases hirr N (by
    rintro h v ⟨J, hJ1, hJ2⟩ v' hv
    refine ⟨F.π (1, h) ∘L J, fun x => ?_, fun g y => ?_⟩
    · rw [ContinuousLinearMap.comp_apply, hJ1, h1 h x v v' hv]
    · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, pi_comm, hJ2]) with h | h
  · have : v₀ ∈ N := hJ
    rw [h] at this
    exact (hv₀ this).elim
  · intro v
    have : v ∈ N := h ▸ Submodule.mem_top
    exact this

end GlobalTheory.FockExtGroup
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_intertwiner_commutes_unitary_and_extends : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2), 1 ≤ n → ∀ (D : DSRep T1) (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (v₀ : M.V), IrrU τ → IsHCMod τ M j → v₀ ≠ 0 → IsGIntw F D.HK M I → (∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v₀))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) → (∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) → F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v'))) ∧ ∀ v : M.V, ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y) := by
  atlas_forward_decl GlobalTheory.FockExtGroup.comm_and_extend
end

section
noncomputable section

namespace GlobalTheory.HarmModule

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory GlobalTheory.FockTensor
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

section Gen

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}

theorem genSub_le {S : Set V} {N : Submodule ℂ V} (h : S ⊆ N) (hN : ∀ Z, ∀ y ∈ N, act Z y ∈ N) :
    genSub act S ≤ N := sInf_le ⟨h, hN⟩

theorem subset_genSub (S : Set V) : S ⊆ genSub act S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.1 hx

theorem genSub_stable (S : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act S) :
    act Z y ∈ genSub act S :=
  Submodule.mem_sInf.2 fun N hN => hN.2 Z y (Submodule.mem_sInf.1 hy N hN)

theorem stable_of_units {N : Submodule ℂ V} (h : ∀ a b, ∀ x ∈ N, act (Eab a b) x ∈ N) (Z : Mat p q)
    (x : V) (hx : x ∈ N) : act Z x ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  have : Matrix.single a b (Z a b) = Z a b • Eab a b := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply]
  exact N.smul_mem _ (h a b x hx)

theorem kStable_of_units {N : Submodule ℂ V}
    (h : ∀ a b, sameBlock a b → ∀ x ∈ N, act (Eab a b) x ∈ N) : KStable act N :=
  fun _ hZ x hx => GlobalTheory.TensorHW.kc_ind act N x (fun a b hab => h a b hab x hx) hZ

theorem equiv_sameBlock : Equivalence (sameBlock : Ix p q → Ix p q → Prop) :=
  ⟨sameBlock_self, by rintro (a | a) (b | b) h <;> simp_all [sameBlock],
    by rintro (a | a) (b | b) (c | c) h h' <;> simp_all [sameBlock]⟩

end Gen

variable {p q : ℕ}

theorem cyclic (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H)
    (hE : Function.Injective E)
    (hadj : ∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y)))
    (r : Ix p q → ℕ) (hr : Function.Injective r) (μ : Ix p q → ℚ) (v : M.V) (hv0 : v ≠ 0)
    (hv : v ∈ wtSub M.act μ) (hup : ∀ a b, r a < r b → M.act (Eab a b) v = 0)
    (hgen : genSub M.act {v} = ⊤) :
    IrrGK M ∧ (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) ∧
      ∃ W : Submodule ℂ M.V, v ∈ W ∧ FiniteDimensional ℂ W ∧ KStable M.act W ∧
        (∀ N : Submodule ℂ M.V, N ≤ W → KStable M.act N → N = ⊥ ∨ N = W) ∧
        ∀ W' : Submodule ℂ M.V, v ∈ W' → KStable M.act W' → W ≤ W' := by
  have eT : Equivalence (fun _ _ : Ix p q => True) := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  have htop : ∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, True → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → ⊤ ≤ U' :=
    fun U' h1 h2 => hgen ▸ genSub_le (by simpa using h1) (stable_of_units fun a b => h2 a b trivial)
  obtain ⟨U, hU1, hU2, -, hU4, -⟩ := GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal p q M.V M.act M.lie _ eT r hr μ v hv fun a b _ h => hup a b h
  have hline : ∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v := fun x hx => hU4 x (htop U hU1 hU2 trivial) hx
  refine ⟨⟨nontrivial_of_ne v 0 hv0, fun N hN => GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates p q M H E hE hadj _ eT μ v ⊤ hv htop
    (fun x _ hx => hline x hx) N le_top fun a b _ => hN _⟩, hline, ?_⟩
  obtain ⟨W, hW1, hW2, hW3, -, -⟩ := GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal p q M.V M.act M.lie _ equiv_sameBlock r hr μ v hv
    fun a b _ h => hup a b h
  have hmin : ∀ W' : Submodule ℂ M.V, v ∈ W' → KStable M.act W' → W ≤ W' := fun W' h1 h2 =>
    hW3 W' h1 fun a b hab _ => h2 _ (isKC_Eab (equiv_sameBlock.symm hab))
  obtain ⟨W₀, hf, h0, hs⟩ := M.kfin v
  refine ⟨W, hW1, Submodule.finiteDimensional_of_le (hmin W₀ h0 hs), kStable_of_units hW2, fun N hN hN' => ?_, hmin⟩
  exact GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates p q M H E hE hadj _ equiv_sameBlock μ v W hv
    (fun U' h1 h2 => hmin U' h1 (kStable_of_units h2)) (fun x _ hx => hline x hx) N hN
    fun a b hab => hN' _ (isKC_Eab hab)

theorem exists_cyclic_sub (P : GKMod p q) (Δ : P.V) : ∃ (M : GKMod p q) (i : M.V →ₗ[ℂ] P.V) (v : M.V),
    Function.Injective i ∧ i v = Δ ∧ (∀ Z x, i (M.act Z x) = P.act Z (i x)) ∧ genSub M.act {v} = ⊤ := by
  obtain ⟨M, i, h1, h2, h3⟩ := GlobalTheory.T.exists_gkMod_injective_range_eq_of_act_stable p q P (genSub P.act {Δ}) (genSub_stable _)
  have hΔ : Δ ∈ LinearMap.range i := h2 ▸ subset_genSub _ rfl
  obtain ⟨v, hv⟩ := hΔ
  refine ⟨M, i, v, h1, hv, h3, eq_top_iff.2 fun x _ => ?_⟩
  have hle : genSub P.act {Δ} ≤ (genSub M.act {v}).map i := by
    refine genSub_le ?_ ?_
    · rintro _ rfl
      exact ⟨v, subset_genSub _ rfl, hv⟩
    · rintro Z _ ⟨y, hy, rfl⟩
      exact ⟨_, genSub_stable _ Z y hy, h3 Z y⟩
  obtain ⟨y, hy, hxy⟩ := hle (h2 ▸ LinearMap.mem_range_self i x)
  exact h1 hxy ▸ hy

theorem globalize (hpq : 1 ≤ p + q) (T : GrpData p q) (πU : URep T) (M : GKMod p q) (E : M.V →ₗ[ℂ] πU.H)
    (hE : Function.Injective E)
    (hder : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (M.act Y x)) 0)
    (hbd : ∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖E ((M.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (hirr : IrrGK M) (N : ℕ → Submodule ℂ M.V) (c : ℚ) (hN : ∀ m, FiniteDimensional ℂ (N m))
    (htop : (⨆ m, N m) = ⊤)
    (heig : ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = ((c : ℂ) + m) • x) :
    ∃ (σ : URep T) (j : M.V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), IrrU σ ∧ IsHCMod σ M j ∧
      Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ ∀ g y, J (σ.π g y) = πU.π g (J y) := by
  obtain ⟨σ, j, J, hd, hJ, hG, hD⟩ := GlobalTheory.T.exists_subrep_closure_analytic_vectors p q T (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hpq T).1 πU M.V M.act E hder hbd
  have hj : Function.Injective j := fun x y h => hE (by rw [← hJ, ← hJ, h])
  obtain ⟨k, hk, lam, hl, hlam⟩ := GlobalTheory.T.exists_central_circle_distinct_graded_eigen p q T σ M j hD N c heig
  exact ⟨σ, j, J, GlobalTheory.T.irreducible_completion_of_graded_irreducible_gK p q T σ M j hj hd hD hirr N k lam hN htop hk hl hlam,
    GlobalTheory.T.isHCModule_of_graded_dense_gK p q hpq T σ M j hj hd hD N k lam hN htop hk hl hlam, hd, hJ, hG⟩

theorem exists_fdeg (T : GrpData p q) (σ : URep T) (hσ : IrrU σ) (v : σ.H) (hv : v ≠ 0)
    (h : MemLp (fun g => inner ℂ v (σ.π g v)) 2 T.haar) :
    ∃ d : ℝ, 0 < d ∧ ∀ x y : σ.H, Integrable (fun g => ‖inner ℂ y (σ.π g x)‖ ^ 2) T.haar ∧
      ∫ g, ‖inner ℂ y (σ.π g x)‖ ^ 2 ∂T.haar = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  haveI : T2Space T.G := T.emb.t2Space
  haveI := (GlobalTheory.HolDS.haar_unimodular p q T).1
  obtain ⟨h1, d, hd, h2⟩ := GlobalTheory.Published.schurOrthogonalitySquareIntegrable' T.G T.haar σ.H σ.π σ.isom σ.cont
    hσ.2 ⟨v, v, hv, hv, h⟩
  refine ⟨d, hd, fun x y => ⟨(memLp_two_iff_integrable_sq_norm (h1 x y).1).1 (h1 x y), ?_⟩⟩
  have h3 := (h2 x y x y).2
  have e : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [e] at h3
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
  apply Complex.ofReal_injective
  rw [h3]
  simp

theorem pow_intw {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (i : V →ₗ[ℂ] V')
    (a : Module.End ℂ V) (b : Module.End ℂ V') (h : ∀ x, i (a x) = b (i x)) (k : ℕ) (x : V) :
    i ((a ^ k) x) = (b ^ k) (i x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

section Fock

variable {r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}

@[reducible] def repFst (F : FockData T0 T1 T2) : URep T1 where
  H := F.H
  π := F.π.comp (MonoidHom.inl _ _)
  isom _ x := F.isom _ x
  cont x := (F.cont x).comp ((GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).1.comp (continuous_id.prodMk continuous_const))

@[reducible] def repSnd (F : FockData T0 T1 T2) : URep T2 where
  H := F.H
  π := F.π.comp (MonoidHom.inr _ _)
  isom _ x := F.isom _ x
  cont x := (F.cont x).comp ((GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).1.comp (continuous_const.prodMk continuous_id))

@[reducible] def polFst (p q r s : ℕ) : GKMod p q where
  V := Pol p q r s
  act := fockAct1 p q r s
  lie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.1
  kfin P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 P).1
  wts P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 P).2

@[reducible] def polSnd (p q r s : ℕ) : GKMod r s where
  V := Pol p q r s
  act := fockAct2 p q r s
  lie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1
  kfin P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 P).1
  wts P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 P).2

theorem om_bound (F : FockData T0 T1 T2) (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) (Q : Pol p q r s) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ,
      ‖F.ι ((omAct p q r s Z ^ k) Q)‖ ≤ C * ρ ^ k * (k.factorial : ℝ) := by
  refine ⟨(2 : ℝ) ^ ((Q.totalDegree : ℝ) / 2 + 1) * ‖F.ι Q‖, 4 * (∑ l, ∑ l', ‖Z l l'‖) + 1,
    by positivity, by positivity, fun k => ?_⟩
  have h := (GlobalTheory.T.fockAction_pow_analyticVector_norm_le p q r s F.H F.ι (GlobalTheory.FockAlg.isFockIsometry_of_fockData F) Z Q.totalDegree k Q
    le_rfl).2
  refine h.trans ?_
  have h2 : (4 * ∑ l, ∑ l', ‖Z l l'‖) ^ k ≤ (4 * (∑ l, ∑ l', ‖Z l l'‖) + 1) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  calc _ = (2 : ℝ) ^ ((Q.totalDegree : ℝ) / 2 + 1) * ‖F.ι Q‖ * (4 * ∑ l, ∑ l', ‖Z l l'‖) ^ k *
        (k.factorial : ℝ) := by ring
    _ ≤ _ := by gcongr

theorem adj_fst (F : FockData T0 T1 T2) (Z : Mat p q) (x y : Pol p q r s) :
    inner ℂ (F.ι (fockAct1 p q r s Z x)) (F.ι y) = inner ℂ (F.ι x) (F.ι (fockAct1 p q r s (adjZ Z) y)) :=
  GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T1 (repFst F) (polFst p q r s) F.ι
    (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.1 Z x y

theorem adj_snd (F : FockData T0 T1 T2) (Z : Mat r s) (x y : Pol p q r s) :
    inner ℂ (F.ι (fockAct2 p q r s Z x)) (F.ι y) = inner ℂ (F.ι x) (F.ι (fockAct2 p q r s (adjZ Z) y)) :=
  GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint r s T2 (repSnd F) (polSnd p q r s) F.ι
    (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.2 Z x y

end Fock

section Transfer

variable {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {M : GKMod p q}
  {i : M.V →ₗ[ℂ] V}

theorem wt_iff (hi : Function.Injective i) (h : ∀ Z x, i (M.act Z x) = act Z (i x)) {μ : Ix p q → ℚ} {x : M.V} :
    x ∈ wtSub M.act μ ↔ i x ∈ wtSub act μ := by
  simp only [GlobalTheory.TensorHW.mem_wt, ← h, ← map_smul, hi.eq_iff]

theorem zero_iff (hi : Function.Injective i) (h : ∀ Z x, i (M.act Z x) = act Z (i x)) {Z : Mat p q} {x : M.V} :
    M.act Z x = 0 ↔ act Z (i x) = 0 := by
  rw [← h, map_eq_zero_iff i hi]

theorem hw_iff (hi : Function.Injective i) (h : ∀ Z x, i (M.act Z x) = act Z (i x)) {μ : Ix p q → ℚ} {x : M.V} :
    x ∈ hwSub M.act μ ↔ i x ∈ hwSub act μ := by
  simp only [GlobalTheory.TensorHW.mem_hw, ← h, ← map_smul, hi.eq_iff, map_eq_zero_iff i hi]

end Transfer

section Pair

variable {n : ℕ} {T0 : GrpData (p * n + q * 0) (p * 0 + q * n)} {T1 : GrpData p q} {T2 : GrpData n 0}

def rkCompact (n : ℕ) : Ix n 0 → ℕ := Sum.elim (fun c => c.1) (fun c => c.elim0)

theorem rkCompact_inj : Function.Injective (rkCompact n) := by
  rintro (a | a) (b | b) h
  · exact congrArg _ (Fin.ext h)
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

theorem rkCompact_lt {a b : Ix n 0} (h : rkCompact n a < rkCompact n b) : posC a b := by
  rcases a with a | a
  · rcases b with b | b
    · exact h
    · exact b.elim0
  · exact a.elim0

theorem exists_compact (F : FockData T0 T1 T2) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
    (hap : Antitone ap) (ham : Antitone am) :
    ∃ (M : GKMod n 0) (i : M.V →ₗ[ℂ] Pol p q n 0) (v : M.V), IrrGK M ∧ IsHW M.act (wtH n ap am) v ∧
      i v = delta hn ap am ∧ (∀ Z x, i (M.act Z x) = fockAct2 p q n 0 Z (i x)) ∧
      ∃ (τ : URep T2) (j : M.V →ₗ[ℂ] τ.H) (v0 : M.V), IsCompactType τ M j (wtH n ap am) v0 := by
  obtain ⟨M, i, v, hi, hv, he, hgen⟩ := exists_cyclic_sub (polSnd p q n 0) (delta hn ap am)
  have hΔ := GlobalTheory.T.harmonicMinorProductDelta_mem_highestWeight_second p q n hn ap am hap ham
  have hΔ0 := (GlobalTheory.T.harmonicMinorProductDelta_extremal_first_member p q n hn ap am hap ham).1
  have hv0 : v ≠ 0 := fun h => hΔ0 (by rw [← hv, h, map_zero])
  have hvw : v ∈ hwSub M.act (wtH n ap am) := (hw_iff hi he).2 (hv ▸ hΔ)
  have hE : Function.Injective (F.ι ∘ₗ i) := F.ι_inj.comp hi
  obtain ⟨hirr, -, W, hW1, hW2, hW3, hW4, -⟩ := cyclic M F.H (F.ι ∘ₗ i) hE
    (fun Z x y => by simpa only [LinearMap.comp_apply, he] using adj_snd F Z (i x) (i y))
    (rkCompact n) rkCompact_inj _ v hv0 hvw.1
    (fun a b h => (GlobalTheory.TensorHW.mem_hw.1 hvw).2 a b (rkCompact_lt h)) hgen
  obtain ⟨-, -, N, hN1, hN2, hN3⟩ := GlobalTheory.T.lowestKType_of_irreducible_generated_module n 0 M (wtH n ap am) W hirr hW2 hW3 hW4 ⟨v, hW1, hv0, hvw⟩
    (fun e _ a b => b.elim0)
    (eq_top_iff.2 (hgen ▸ genSub_le (by simpa using subset_genSub _ hW1) (genSub_stable _)))
  obtain ⟨τ, j, J, h1, h2, -, -, -⟩ := globalize (p := n) (q := 0) (by omega) T2 (repSnd F) M (F.ι ∘ₗ i) hE
    (fun Y hY x => by
      simp only [LinearMap.comp_apply, he]
      exact (GlobalTheory.T.fock_derived_actions_tensor_members p q n 0 T0 T1 T2 F).2.2 Y hY (i x))
    (fun Y _ y => by
      simp only [LinearMap.comp_apply, pow_intw i _ _ (he Y)]
      exact om_bound F _ (i y))
    hirr N _ hN1 hN2 hN3
  refine ⟨M, i, v, hirr, ⟨hv0, hvw⟩, hv, he, τ, j, ((‖j v‖⁻¹ : ℝ) : ℂ) • v, h1, h2, ?_⟩
  have h0 : ‖j v‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero_iff j h2.1).2 hv0)
  refine ⟨⟨smul_ne_zero (by simpa using h0) hv0, Submodule.smul_mem _ _ hvw⟩, ?_⟩
  rw [map_smul, norm_smul]
  simp [h0]

def rkExt (p q : ℕ) : Ix p q → ℕ := Sum.elim (fun i => q + i.1) (fun j => j.rev.1)

theorem rkExt_inj : Function.Injective (rkExt p q) := by
  rintro (a | a) (b | b) h <;> simp only [rkExt, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg _ (Fin.ext (by omega))
  · have := b.rev.2; omega
  · have := a.rev.2; omega
  · exact congrArg _ (Fin.rev_injective (Fin.ext h))

theorem exists_lowest (F : FockData T0 T1 T2) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
    (hap : Antitone ap) (ham : Antitone am) (hap1 : ∀ i, 1 ≤ ap i) (ham1 : ∀ i, 1 ≤ am i) :
    ∃ (M : GKMod p q) (i : M.V →ₗ[ℂ] Pol p q n 0) (v : M.V) (W : Submodule ℂ M.V), Function.Injective i ∧
      i v = delta hn ap am ∧ (∀ Z x, i (M.act Z x) = fockAct1 p q n 0 Z (i x)) ∧ v ∈ W ∧ v ≠ 0 ∧
      v ∈ wtSub M.act (wtExt n ap am) ∧ (∀ x ∈ wtSub M.act (wtExt n ap am), ∃ c : ℂ, x = c • v) ∧
      IsLowestType M (wtK n ap am) W ∧ Module.finrank ℂ ↥(hwSub M.act (wtK n ap am)) = 1 ∧
      (∀ x, casimir M.act x = (((normSq (hcParam n ap am) - rhoSq (p + q) : ℚ)) : ℂ) • x) ∧
      ConeTypes M (hcParam n ap am) ∧
      ∃ N : ℕ → Submodule ℂ M.V, (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = ⊤ ∧ ∀ m : ℕ, ∀ x ∈ N m,
        ∑ a : Fin p, M.act (Eab (Sum.inl a) (Sum.inl a)) x =
          (((∑ a : Fin p, wtK n ap am (Sum.inl a) : ℚ) : ℂ) + m) • x := by
  obtain ⟨M, i, v, hi, hv, he, hgen⟩ := exists_cyclic_sub (polFst p q n 0) (delta hn ap am)
  have hΔ2 := GlobalTheory.T.harmonicMinorProductDelta_mem_highestWeight_second p q n hn ap am hap ham
  obtain ⟨hΔ0, hΔw, hΔa, hΔb, hΔk⟩ := GlobalTheory.T.harmonicMinorProductDelta_extremal_first_member p q n hn ap am hap ham
  have hv0 : v ≠ 0 := fun h => hΔ0 (by rw [← hv, h, map_zero])
  have hvw : v ∈ wtSub M.act (wtExt n ap am) := (wt_iff hi he).2 (hv ▸ hΔw)
  have hE : Function.Injective (F.ι ∘ₗ i) := F.ι_inj.comp hi
  have hadj : ∀ Z x y, inner ℂ ((F.ι ∘ₗ i) (M.act Z x)) ((F.ι ∘ₗ i) y) =
      inner ℂ ((F.ι ∘ₗ i) x) ((F.ι ∘ₗ i) (M.act (adjZ Z) y)) :=
    fun Z x y => by simpa only [LinearMap.comp_apply, he] using adj_fst F Z (i x) (i y)
  have hvk : KilledByLower M.act v := fun a b => (zero_iff hi he).2 (hv ▸ hΔk a b)
  obtain ⟨hirr, hline, W, hW1, hW2, hW3, hW4, hW5⟩ := cyclic M F.H (F.ι ∘ₗ i) hE hadj
    (rkExt p q) rkExt_inj _ v hv0 hvw (by
      rintro (a | a) (b | b) h <;> simp only [rkExt, Sum.elim_inl, Sum.elim_inr] at h
      · exact (zero_iff hi he).2 (hv ▸ hΔa a b (by omega))
      · have := b.rev.2; omega
      · exact hvk b a
      · exact (zero_iff hi he).2 (hv ▸ hΔb b a (Fin.rev_lt_rev.1 h))) hgen
  have hWk : ∀ e ∈ W, KilledByLower M.act e := by
    let K : Submodule ℂ M.V := ⨅ a, ⨅ b, LinearMap.ker (M.act (Eab (Sum.inr b) (Sum.inl a)))
    have hK : ∀ x, x ∈ K ↔ KilledByLower M.act x := fun x => by
      simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, KilledByLower]
    exact fun e h => (hK e).1 (hW5 K ((hK v).2 hvk)
      (fun Z hZ x hx => (hK _).2 (GlobalTheory.T.isKilledByLowerNilradical_act_blockDiagonal p q M.V M.act M.lie Z hZ x ((hK x).1 hx))) h)
  have hcomm : ∀ Y Z (P : Pol p q n 0), fockAct2 p q n 0 Z (fockAct1 p q n 0 Y P) =
      fockAct1 p q n 0 Y (fockAct2 p q n 0 Z P) := fun Y Z P =>
    (LinearMap.congr_fun ((GlobalTheory.T.fockOperators_lie_representation_commute p q n 0).2.2.2 Y Z) P).symm
  have hW2' : ∀ e ∈ W, i e ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := fun e h =>
    hW5 ((hwSub (fockAct2 p q n 0) (wtH n ap am)).comap i) (by simpa [hv] using hΔ2) (fun Z _ x hx => by
      have hx' := GlobalTheory.TensorHW.mem_hw.1 (Submodule.mem_comap.1 hx)
      refine Submodule.mem_comap.2 (GlobalTheory.TensorHW.mem_hw.2 ⟨fun a => ?_, fun a b hab => ?_⟩)
      · rw [he]
        exact (hcomm _ _ _).trans (by rw [hx'.1 a, map_smul])
      · rw [he]
        exact (hcomm _ _ _).trans (by rw [hx'.2 a b hab, map_zero])) h
  obtain ⟨μ, e, heW, he0, heh⟩ := GlobalTheory.T.exists_highestWeight_vector_of_KStable p q M W hW2 hW3 fun h => hv0 (by simpa [h] using hW1)
  have hμ : μ = wtK n ap am := GlobalTheory.T.harmonic_highestWeight_eq_lowestKTypeHighestWeight p q n hn ap am μ (i e)
    ⟨(map_ne_zero_iff i hi).2 he0, (hw_iff hi he).1 heh⟩ (hW2' e heW)
    fun a b => (zero_iff hi he).1 (hWk e heW a b)
  subst hμ
  have hgW : genSub M.act (W : Set M.V) = ⊤ :=
    eq_top_iff.2 (hgen ▸ genSub_le (by simpa using subset_genSub _ hW1) (genSub_stable _))
  have hge : genSub M.act {e} = ⊤ := (hirr.2 _ (genSub_stable _)).resolve_left fun h =>
    he0 (by simpa [h] using subset_genSub (act := M.act) {e} rfl)
  obtain ⟨hlow, hone, hN⟩ := GlobalTheory.T.lowestKType_of_irreducible_generated_module p q M _ W hirr hW2 hW3 hW4 ⟨e, heW, he0, heh⟩ hWk hgW
  obtain ⟨-, hbl, hlt⟩ := GlobalTheory.T.centredHarishChandraParameter_isParam_blattner p q n hn ap am hap ham hap1 ham1
  refine ⟨M, i, v, W, hi, hv, he, hW1, hv0, hvw, hline, hlow, hone, fun x => ?_, fun ν u hu => ?_, hN⟩
  · rw [GlobalTheory.T.normSq_centredHarishChandraParameter_sub_rhoSq p q n ap am]
    exact GlobalTheory.T.casimir_scalar_on_module_generated_killedByLower p q M.V M.act M.lie _ e heh (hWk e heW) hge x
  · obtain ⟨m, hm1, hm2⟩ := GlobalTheory.T.kTypes_unitary_lowestWeight_in_cone p q M F.H _ hE hadj _ e heh (hWk e heW) hge ν u hu
    refine ⟨m, fun a b hab => ?_, hbl ▸ hm2⟩
    obtain ⟨a', b', rfl, rfl⟩ := hm1 a b hab
    exact hlt a' b'

end Pair

theorem inv_mem_Kset (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) : k⁻¹ ∈ T.Kset := by
  have h : Commute ((T.cov k : GL (Ix p q) ℂ) : Mat p q) (Jm p q) := (GlobalTheory.RealPar.KStabLie.isKC_iff _).1 hk
  refine (GlobalTheory.RealPar.KStabLie.isKC_iff _).2 ?_
  rw [map_inv]
  exact h.units_inv_left

theorem one_mem_Kset (T : GrpData p q) : (1 : T.G) ∈ T.Kset :=
  (GlobalTheory.RealPar.KStabLie.isKC_iff _).2 (by simp)

theorem exists_k_translate (hpq : 1 ≤ p + q) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H)
    (hder : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0)
    (W : Submodule ℂ M.V) [FiniteDimensional ℂ W] (hW : KStable M.act W) {k : T.G} (hk : k ∈ T.Kset) (e : W) :
    ∃ e' : W, σ.π k (j e) = j e' := by
  classical
  obtain ⟨e', h, -⟩ := GlobalTheory.RealPar.pair_kEquivariant_of_lie p q T (GlobalTheory.CoverKGen.kset_gen p q hpq T) σ σ W
    (fun Y => if h : IsKC Y then (M.act Y).restrict (hW Y h) else 0) (j ∘ₗ W.subtype) (j ∘ₗ W.subtype)
    (fun Y hY hK w => by
      simp only [dif_pos hK, and_self]
      exact hder Y hY w) k hk e
  exact ⟨e', h⟩

section Pair

variable {n : ℕ} {T0 : GrpData (p * n + q * 0) (p * 0 + q * n)} {T1 : GrpData p q} {T2 : GrpData n 0}

theorem coef_decay (hdec : GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.HarmonicDecay) (hpq : 1 ≤ p + q) (F : FockData T0 T1 T2) (σ : URep T1)
    (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H)
    (hder : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T1.expt (t • Y)) (j x)) (j (M.act Y x)) 0)
    (W : Submodule ℂ M.V) [FiniteDimensional ℂ W] (hW : KStable M.act W)
    (i : M.V →ₗ[ℂ] Pol p q n 0) (J : σ.H →ₗᵢ[ℂ] F.H) (hJ : ∀ x, J (j x) = F.ι (i x))
    (hG : ∀ g y, J (σ.π g y) = F.π (g, 1) (J y)) (hk : ∀ e ∈ W, KilledByLower (fockAct1 p q n 0) (i e)) :
    ∀ k₁ ∈ T1.Kset, ∀ k₂ ∈ T1.Kset, ∀ X ∈ pR p q, ∀ e e' : W,
      ‖inner ℂ (j e') (σ.π (k₁ * T1.expt X * k₂) (j e))‖ ≤ decay n X * ‖j e‖ * ‖j e'‖ := by
  intro k₁ h₁ k₂ h₂ X hX e e'
  obtain ⟨f, hf⟩ := exists_k_translate hpq T1 σ M j hder W hW h₂ e
  obtain ⟨f', hf'⟩ := exists_k_translate hpq T1 σ M j hder W hW (inv_mem_Kset T1 h₁) e'
  have hP : ∀ e ∈ W, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.KilledByPMinus (i e) := fun e he a b => by
    have := hk e he a b
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero] at this
  have h := hdec p q n T0 T1 T2 F X hX (i f) (i f') (hP f f.2) (hP f' f'.2)
  have e1 : inner ℂ (j e') (σ.π (k₁ * T1.expt X * k₂) (j e)) = GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.coef F X (i f) (i f') := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.coef, ← hJ, ← hJ, ← hG, J.inner_map_map, ← hf, ← hf', inner_pi_left, inv_inv,
      map_mul, map_mul]
    rfl
  have e2 : decay n X = ∏ i : Fin (min p q), Real.cosh (GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.singVal X i) ^ (-(n : ℤ)) := by
    rw [decay, Finset.prod_range]
    simp only [zpow_neg, zpow_natCast, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.singVal]
  rw [e1, e2]
  rwa [← hJ, ← hJ, J.norm_map, J.norm_map, ← hf, ← hf', σ.isom, σ.isom] at h

theorem harmonicMaps_of (hn : 1 ≤ n) (F : FockData T0 T1 T2) (D : DSRep T1) (W : Submodule ℂ D.HK.V)
    (Λ : Ix p q → ℚ) (hW : IsLowestType D.HK Λ W) (hd : Dense (Set.range D.ι)) (τ : URep T2)
    (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (Δ : Pol p q n 0) (hΔ : Δ ≠ 0) (e0 : W) (v0 : M.V) (hτ : IrrU τ)
    (hM : IsHCMod τ M j) (hirr : IrrGK M) (he0 : e0 ≠ 0) (hv0 : v0 ≠ 0)
    (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (hI : IsGIntw F D.HK M I) (h0 : I ((e0 : D.HK.V) ⊗ₜ v0) = Δ)
    (hip : ∀ (x x' : D.HK.V) (v v' : M.V), inner ℂ (F.ι (I (x' ⊗ₜ v'))) (F.ι (I (x ⊗ₜ v))) =
      ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι x') (D.ι x) * inner ℂ (j v') (j v))
    (hJ0 : ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v0))) ∧
      ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) :
    HarmonicMaps F D W τ M j Δ e0 v0 (I ∘ₗ TensorProduct.map W.subtype LinearMap.id) I := by
  obtain ⟨-, -, hWs, hWi, -, -, hWk, hWg, -⟩ := hW
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.T.fock_tensor_intertwiner_unique_and_range p q n T0 T1 T2 F D.HK W M I e0 v0 hWg hWs hWi hirr he0 hv0 hI
  obtain ⟨g1, g2⟩ := GlobalTheory.T.fock_intertwiner_commutes_unitary_and_extends p q n T0 T1 T2 F hn D τ M j I v0 hτ hM hv0 hI hJ0
  have hio : ∀ (e : W) (v : M.V), (I ∘ₗ TensorProduct.map W.subtype LinearMap.id) (e ⊗ₜ v) =
      I ((e : D.HK.V) ⊗ₜ v) := fun e v => by simp
  have hcoef : ∀ (g : T1.G) (x x' : D.HK.V) (v v' : M.V),
      inner ℂ (F.ι (I (x' ⊗ₜ v'))) (F.π (g, 1) (F.ι (I (x ⊗ₜ v)))) =
        ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι x') (D.U.π g (D.ι x)) * inner ℂ (j v') (j v) := by
    intro g x x' v v'
    obtain ⟨J, hJ1, hJ2⟩ := g2 v
    rw [← hJ1, hJ2]
    refine DenseRange.induction_on (p := fun y => inner ℂ (F.ι (I (x' ⊗ₜ v'))) (J y) =
      ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) * inner ℂ (D.ι x') y * inner ℂ (j v') (j v)) hd _
      (isClosed_eq (by fun_prop) (by fun_prop)) fun y => ?_
    rw [hJ1, hip]
  refine ⟨(hio _ _).trans h0, ⟨fun Z _ e e' v h => ?_, fun Y e v => ?_⟩, fun io' h h' => u1 io' h (h'.trans h0.symm),
    fun k _ h e e' v v' he hv => ?_, fun e e' v v' => ?_, fun y a b => ?_, fun e v => (hio e v).symm, hI,
    fun I' h h' => u2 I' h fun e v => (h' e v).trans (hio e v), fun v hv => ⟨fun x x' hx => ?_, ?_⟩, hip, g1, g2,
    fun g e e' v v' => ?_, fun e e' v he he' hv => ?_⟩
  · rw [hio, hio, hI.1, h]
  · rw [hio, hio, hI.2]
  · obtain ⟨J, hJ1, hJ2⟩ := g2 v'
    have : (k, h) = ((k, 1) : T1.G × T2.G) * (1, h) := by simp
    rw [hio, hio, this, map_mul, ContinuousLinearMap.mul_apply, g1 h e v v' hv, ← hJ1, hJ2, ← he, hJ1]
  · rw [hio, hio, hip]
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e v => rw [hio, hI.1, hWk e e.2 a b, TensorProduct.zero_tmul, map_zero]
    | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
  · have h1 := hip (x - x') (x - x') v v
    have h2 : I ((x - x') ⊗ₜ v) = 0 := by
      rw [TensorProduct.sub_tmul, map_sub]
      exact sub_eq_zero.2 hx
    rw [h2, map_zero, inner_zero_left] at h1
    have h3 : ((‖F.ι Δ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      simpa using (map_ne_zero_iff F.ι F.ι_inj).2 hΔ
    have h4 : inner ℂ (j v) (j v) ≠ 0 := inner_self_ne_zero.2 ((map_ne_zero_iff j hM.1).2 hv)
    have h5 := ((mul_eq_zero.1 ((mul_eq_zero.1 h1.symm).resolve_right h4)).resolve_left h3)
    exact sub_eq_zero.1 ((map_eq_zero_iff D.ι D.ι_inj).1 (inner_self_eq_zero.1 h5))
  · simp only [hio]
    exact u3 v
  · rw [hio, hio, hcoef]
  · have e1 : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e2 : inner ℂ (j v) (j v) = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; simp
    obtain ⟨s1, s2⟩ := D.schur (D.ι e) (D.ι e')
    simp only [hio, hcoef, e2, mul_one, mul_assoc, e1]
    refine ⟨(s1.ofReal (𝕜 := ℂ)).const_mul _, ?_⟩
    rw [integral_const_mul, integral_complex_ofReal, s2, he, he']
    push_cast
    ring

end Pair

theorem harmonicModule_of (hdec : GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.HarmonicDecay) (hint : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral) :
    HarmonicModule := by
  intro p q n hn hpq ap am hap ham hap1 ham1 T0 T1 T2 F
  obtain ⟨M₁, i, v, W, hi, hv, he, hvW, hv0, hvw, hline, hlow, hone, hcas, hcone, N, hN1, hN2, hN3⟩ :=
    exists_lowest F hn ap am hap ham hap1 ham1
  obtain ⟨σ, j₁, J, hσ, hHC, hd, hJ, hG⟩ := globalize hpq T1 (repFst F) M₁ (F.ι ∘ₗ i) (F.ι_inj.comp hi)
    (fun Y hY x => by
      simp only [LinearMap.comp_apply, he]
      exact (GlobalTheory.T.fock_derived_actions_tensor_members p q n 0 T0 T1 T2 F).2.1 Y hY (i x))
    (fun Y _ y => by
      simp only [LinearMap.comp_apply, pow_intw i _ _ (he Y)]
      exact om_bound F _ (i y))
    hlow.1 N _ hN1 hN2 hN3
  haveI := hlow.2.1
  have hdecay := coef_decay hdec hpq F σ M₁ j₁ hHC.2.2 W hlow.2.2.1 i J hJ hG
    fun e h a b => (zero_iff hi he).1 (hlow.2.2.2.2.2.2.1 e h a b)
  have hjv : j₁ v ≠ 0 := (map_ne_zero_iff j₁ hHC.1).2 hv0
  obtain ⟨d, hd0, hschur⟩ := exists_fdeg T1 σ hσ (j₁ v) hjv
    (GlobalTheory.T.memLp_two_of_cosh_decay_unitaryPQCover hint p q n hn T1 _ (‖j₁ v‖ * ‖j₁ v‖) (continuous_const.inner (σ.cont _)) fun k hk X hX => by
      have := hdecay k hk 1 (one_mem_Kset T1) X hX ⟨v, hvW⟩ ⟨v, hvW⟩
      rw [mul_one] at this
      exact this.trans_eq (by ring))
  let D : DSRep T1 :=
    { U := σ, nontriv := hσ.1, irred := hσ.2, fdeg := d, fdeg_pos := hd0, schur := hschur, HK := M₁, ι := j₁
      ι_inj := hHC.1, ι_range := hHC.2.1, der := hHC.2.2 }
  obtain ⟨hpar, hbl, -⟩ := GlobalTheory.T.centredHarishChandraParameter_isParam_blattner p q n hn ap am hap ham hap1 ham1
  obtain ⟨M₂, i₂, v₂, hirr₂, hv₂, hi₂, he₂, τ₀, j₀, w₀, hτ₀⟩ := exists_compact F hn ap am hap ham
  refine ⟨D, W, hlow, hbl, ⟨hpar, hbl ▸ hone, hcas, hcone⟩, hdecay, ?_, ⟨τ₀, M₂, j₀, w₀, hτ₀⟩, ?_⟩
  · have h0 : ‖j₁ v‖ ≠ 0 := norm_ne_zero_iff.2 hjv
    refine ⟨⟨((‖j₁ v‖⁻¹ : ℝ) : ℂ) • v, W.smul_mem _ hvW⟩, Submodule.smul_mem _ _ hvw, ?_⟩
    change ‖j₁ (((‖j₁ v‖⁻¹ : ℝ) : ℂ) • v)‖ = 1
    rw [map_smul, norm_smul]
    simp [h0]
  rintro τ M j v0 ⟨hτ, hM, hv0', hv1⟩ e0 he0w he01
  change ‖j₁ (e0 : M₁.V)‖ = 1 at he01
  have he0 : (e0 : M₁.V) ≠ 0 := fun h => by simp [h] at he01
  obtain ⟨-, hirr, -, -⟩ := GlobalTheory.T.compactCoverUn_hcModule_finiteDim_irreducible n (by omega) T2 τ M j hτ hM (nontrivial_of_ne v0 0 hv0'.1)
  obtain ⟨f, hf1, hf2⟩ := GlobalTheory.T.exists_intertwiner_map_highestWeightVector_compact n M M₂ _ v0 v₂ hirr hirr₂ hv0' hv₂
  obtain ⟨c, hc⟩ := hline _ he0w
  have hc0 : c ≠ 0 := fun h => he0 (by rw [hc, h, zero_smul])
  have hve : v = c⁻¹ • (e0 : M₁.V) := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have gen : ∀ {a b : ℕ} (A : GKMod a b), IrrGK A → ∀ x : A.V, x ≠ 0 → genSub A.act {x} = ⊤ :=
    fun A hA x hx => (hA.2 _ (genSub_stable _)).resolve_left fun h =>
      hx (by simpa [h] using subset_genSub (act := A.act) {x} rfl)
  have hg1 := gen M₁ hlow.1 _ he0
  have hg2 := gen M hirr _ hv0'.1
  have hΔ : (c⁻¹ • i) (e0 : M₁.V) = delta hn ap am := by
    rw [← hv, hve, map_smul, LinearMap.smul_apply]
  have hΔ' : (i₂ ∘ₗ f) v0 = delta hn ap am := by rw [LinearMap.comp_apply, hf1, hi₂]
  have he₂' : ∀ Z y, (i₂ ∘ₗ f) (M.act Z y) = fockAct2 p q n 0 Z ((i₂ ∘ₗ f) y) := fun Z y => by
    simp only [LinearMap.comp_apply, hf2, he₂]
  obtain ⟨I, hI1, hI2, hI3, hI4⟩ := GlobalTheory.T.exists_equivariant_tensor_map_of_cyclic_commuting p q n 0 (Pol p q n 0) _ _ (GlobalTheory.T.fockOperators_lie_representation_commute p q n 0).2.2.2 M₁ M
    (c⁻¹ • i) (i₂ ∘ₗ f) (fun Z x => by simp only [LinearMap.smul_apply, he, map_smul]) he₂' e0 v0 hg1 hg2
    (hΔ.trans hΔ'.symm)
  have hline2 : ∀ x ∈ wtSub M.act (wtH n ap am), ∃ c : ℂ, x = c • v0 :=
    (cyclic M τ.H j hM.1 (GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint n 0 T2 τ M j hM.2.2) (rkCompact n)
      rkCompact_inj _ v0 hv0'.1 hv0'.2.1
      (fun a b h => (GlobalTheory.TensorHW.mem_hw.1 hv0'.2).2 a b (rkCompact_lt h)) hg2).2.1
  have hf₂ := GlobalTheory.T.invariant_inner_forms_proportional_weight_line n 0 M τ.H F.H j (F.ι ∘ₗ i₂ ∘ₗ f) (F.ι ∘ₗ i₂ ∘ₗ f)
    (GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint n 0 T2 τ M j hM.2.2)
    (fun Z x y => by
      simp only [LinearMap.comp_apply (f := F.ι), he₂']
      exact adj_snd F Z _ _) _ v0 hv0'.2.1 hline2 hg2 hv1
  simp only [LinearMap.comp_apply (f := F.ι), hΔ'] at hf₂
  refine ⟨_, I, harmonicMaps_of (by omega) F D W _ hlow hd τ M j _ (fun h => hv0 (hi (by rw [hv, h, map_zero])))
    e0 v0 hτ hM hirr (fun h => he0 (by rw [h]; rfl)) hv0'.1 I ⟨hI1, hI2⟩ ((hI3 _).trans hΔ)
    (fun x x' w w' => ?_) ⟨c⁻¹ • J.toContinuousLinearMap, fun x => ?_, fun g y => ?_⟩⟩
  · have hf₁ := GlobalTheory.T.invariant_inner_forms_proportional_weight_line p q M₁ σ.H F.H j₁ (F.ι ∘ₗ I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip w')
      (F.ι ∘ₗ I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip w)
      (GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T1 σ M₁ j₁ hHC.2.2)
      (fun Z x y => by
        simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, ← hI1]
        exact adj_fst F Z _ _) _ e0 he0w
      (fun y hy => by
        obtain ⟨a, ha⟩ := hline y hy
        exact ⟨a * c⁻¹, by rw [ha, mul_smul, ← hve]⟩) hg1 he01 x' x
    simp only [LinearMap.comp_apply (f := F.ι), LinearMap.comp_apply (f := I), LinearMap.flip_apply,
      TensorProduct.mk_apply, hI4, hf₂] at hf₁
    refine hf₁.trans ?_
    rw [inner_self_eq_norm_sq_to_K, mul_right_comm]
    push_cast
    rfl
  · change c⁻¹ • J (j₁ x) = F.ι (I (x ⊗ₜ v0))
    rw [hI3, hJ, LinearMap.smul_apply, map_smul]
    rfl
  · change F.π (g, 1) (c⁻¹ • J y) = c⁻¹ • J (σ.π g y)
    rw [map_smul, hG]
    rfl

end GlobalTheory.HarmModule

end
end
