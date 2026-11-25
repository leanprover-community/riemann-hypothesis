module

public import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.SChain

@[expose] public section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem card_PsiA_index {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (A0 : AddSubgroup H) :
    (PsiA A0).card = 4 * A0.index := by
  classical
  let π : E0 × H →+ E0 × (H ⧸ A0) := (AddMonoidHom.id E0).prodMap (QuotientAddGroup.mk' A0)
  have hπ : Function.Surjective π := by
    rintro ⟨a, q⟩
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective A0 q
    exact ⟨(a, b), rfl⟩
  have inj := AddChar.compAddMonoidHom_injective_left (M := ℂ) π hπ
  have himg : PsiA A0 = Finset.univ.image (fun χ : AddChar (E0 × (H ⧸ A0)) ℂ => χ.compAddMonoidHom π) := by
    ext ψ
    simp only [PsiA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      have hker : π.ker ≤ ψ.toAddMonoidHom.ker := by
        rintro ⟨a, b⟩ hx
        rw [AddMonoidHom.mem_ker] at hx ⊢
        have ha : a = 0 := congrArg Prod.fst hx
        have hb : QuotientAddGroup.mk' A0 b = 0 := congrArg Prod.snd hx
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hb
        subst ha
        exact congrArg Additive.ofMul (h b hb)
      let e := QuotientAddGroup.quotientKerEquivOfSurjective π hπ
      refine ⟨AddChar.toAddMonoidHomEquiv.symm
        ((QuotientAddGroup.lift π.ker ψ.toAddMonoidHom hker).comp e.symm.toAddMonoidHom), ?_⟩
      ext x
      have he : e.symm (π x) = QuotientAddGroup.mk x := e.symm_apply_eq.2 rfl
      simp [he]
    · rintro ⟨χ, rfl⟩ s hs
      show χ (π (0, s)) = 1
      have : π (0, s) = 0 := by
        simp [π, QuotientAddGroup.eq_zero_iff, hs]
      rw [this, AddChar.map_zero_eq_one]
  rw [himg, Finset.card_image_of_injective _ inj, Finset.card_univ, AddChar.card_eq, Fintype.card_prod,
    AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  simp [E0]

theorem UpperTheory.Comparison₂.card_PsiA :
    ∀ φ : Frame, (PsiA φ.A0).card = 4 * φ.o := by
  intro φ
  rw [card_PsiA_index, φ.index_A0_eq_o]
