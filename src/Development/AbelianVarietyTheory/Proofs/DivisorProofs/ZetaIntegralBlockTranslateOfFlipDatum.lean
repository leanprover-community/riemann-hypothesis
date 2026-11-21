import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumVolShellInterTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

open GlobalTheory.OneSquareZeta

theorem GlobalTheory.LeftTranslateZeta.bigF_phiA_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (h : GL C k),
    IsUnif ϖ →
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z)) (X0 k σ * (invT h).val) *
      (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν ϖ n c Ψ g₀ h hϖ

  have hlat : latA ϖ n (diagLat c) = diagLat (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) := by
    rw [latA, dualLat_diagLat, smul_diagLat]
  have hrank : (X0 k σ * (invT h).val).rank = a := by
    rw [(rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ (X0 k σ * (invT h).val)).2 ⟨h, rfl⟩, Fintype.card_fin]

  obtain ⟨g₁, hg₁⟩ := exists_primFrame (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) _ hrank
  rw [← hlat] at hg₁
  have hκ : (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

  have hpt : ∀ g : GL (Fin a) k,
      phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
        apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)}.indicator
        (fun _ => fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
          ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))) g := by
    intro g
    have hgX : g₀.val * (g.val * (X0 k σ * (invT h).val)) = g₀.val * g.val * (X0 k σ * (invT h).val) :=
      (Matrix.mul_assoc _ _ _).symm
    rw [hgX]
    have key := fFun_mul_left (μ := μ) (σ := σ) (ν := ν) (Ψ := Ψ) (g := g₀ * g) (h := h)
    simp only [apow_mul, map_mul, Units.val_mul] at key
    by_cases hS : g₀ * g * g₁⁻¹ ∈ KO k (Fin a)
    · have hP : IsPrimFrame (latA ϖ n (diagLat c)) ((g₀ * g).val * (X0 k σ * (invT h).val)) :=
        (isPrimFrame_mul_iff hg₁ (g₀ * g)).2 hS
      rw [Units.val_mul] at hP
      rw [Set.indicator_of_mem (show g ∈ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)} from hS), phiA, if_pos hP,
        eq_div_iff hκ, ← key]
      ring
    · have hP : ¬ IsPrimFrame (latA ϖ n (diagLat c)) ((g₀ * g).val * (X0 k σ * (invT h).val)) :=
        fun hP => hS ((isPrimFrame_mul_iff hg₁ (g₀ * g)).1 hP)
      rw [Units.val_mul] at hP
      rw [Set.indicator_of_notMem (show g ∉ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)} from hS), phiA, if_neg hP]
      ring

  have hsum : (∑ᶠ m : {m : Fin a → ℤ // Antitone m}, ∫ g in shellSet ϖ m.1,
      phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
        apow (gdet g) ((Fintype.card C : ℂ) / 2) ∂haarVol (KO k (Fin a))) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
        ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2)) := by
    have hint : ∀ m : {m : Fin a → ℤ // Antitone m}, (∫ g in shellSet ϖ m.1,
        phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
          apow (gdet g) ((Fintype.card C : ℂ) / 2) ∂haarVol (KO k (Fin a))) =
        (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)}) •
          (fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
            ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))) := by
      intro m
      rw [integral_congr_ae (ae_of_all _ hpt)]
      refine (setIntegral_indicator ?_).trans (setIntegral_const (E := ℂ)
        (fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
          ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))))
      let : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
      exact (ShellVolume.isOpen_translate g₀ g₁⁻¹).measurableSet
    rw [finsum_congr hint, ← finsum_smul,
      ShellVolume.finsum_vol_shell_inter_translate k a ϖ g₀ g₁⁻¹ hϖ, one_smul]
  unfold bigF shellSum shell
  refine (congrArg (fun s => s * (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2)) hsum).trans ?_
  rw [mul_assoc]
  exact div_mul_cancel₀ _ hκ

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegral_leftTranslate_primitiveFrames : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (h : GL C k),
    IsUnif ϖ →
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z)) (X0 k σ * (invT h).val) *
      (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  atlas_forward_decl GlobalTheory.LeftTranslateZeta.bigF_phiA_left
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

theorem GlobalTheory.OneSquareZeta.bigZeta_phiA_twist_eq_smallZeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (N h : GL C k),
    IsUnif ϖ →
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) * (ν (gdet N) : ℂ) * apow (gdet N) ((Fintype.card C : ℂ) / 2) *
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z * N.val)) h =
      smallP μ σ ν (ν * β) (fun Y => Ψ (Y * (invT N).val)) h := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν β ϖ n c Ψ g₀ N h hϖ
  set h' : GL C k := h * invT N with hh'
  have hX : X0 k σ * (invT h).val * N.val = X0 k σ * (invT h').val := by
    rw [hh', map_mul, invT_invT, Units.val_mul, Matrix.mul_assoc]
  have hF : bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z * N.val))
      (X0 k σ * (invT h).val) =
      bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z))
      (X0 k σ * (invT h').val) := by
    rw [← hX]; simp only [bigF, Matrix.mul_assoc]
  have hL := GlobalTheory.T.zetaIntegral_leftTranslate_primitiveFrames k a A' C μ σ ν ϖ n c Ψ g₀ h' hϖ
  rw [splitTheta_fFun_frameFirstBlock_mul] at hL
  have hS : smallF μ ν Ψ (Y0 k σ * h'.val) = smallF μ ν (fun Y => Ψ (Y * (invT N).val)) (Y0 k σ * h.val) := by
    simp only [smallF, hh', Units.val_mul, Matrix.mul_assoc]
  have hdet : gdet h' = gdet h * (gdet N)⁻¹ := by rw [hh', gdet_mul, gdet_invT]
  rw [hS, hdet, map_mul ν, apow_mul, apow_inv, map_inv ν, Units.val_mul] at hL
  rw [bigZetaIntegral_eq, hF, smallP]
  have hC : (Fintype.card C : ℂ) = a + Fintype.card A' := by
    rw [← Fintype.card_congr σ, Fintype.card_sum, Fintype.card_fin]; push_cast; ring
  have e : apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) =
      apow (gdet h) ((Fintype.card A' : ℂ) / 2) := by
    rw [← apow_add, hC]; congr 1; ring
  have eN : apow (gdet N) ((Fintype.card C : ℂ) / 2) * apow (gdet N) (-((Fintype.card C : ℂ) / 2)) = 1 := by
    rw [apow_neg, mul_inv_cancel₀ (apow_ne_zero _ _)]
  have eν : (ν (gdet N) : ℂ) * ((ν (gdet N))⁻¹ : ℂˣ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [MonoidHom.mul_apply, Units.val_mul]
  linear_combination ((β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2) * (ν (gdet N) : ℂ) * apow (gdet N) ((Fintype.card C : ℂ) / 2)) * hL +
    ((β (gdet h) : ℂ) * (ν (gdet h) : ℂ) * smallF μ ν (fun Y => Ψ (Y * (invT N).val)) (Y0 k σ * h.val)) *
      (apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) * ((ν (gdet N) : ℂ) * ((ν (gdet N))⁻¹ : ℂˣ)) * eN +
        apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) * eν + e)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegral_twoSidedMovedDatum_eq_smallZeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (N h : GL C k),
    IsUnif ϖ →
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) * (ν (gdet N) : ℂ) * apow (gdet N) ((Fintype.card C : ℂ) / 2) *
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z * N.val)) h =
      smallP μ σ ν (ν * β) (fun Y => Ψ (Y * (invT N).val)) h := by
  atlas_forward_decl GlobalTheory.OneSquareZeta.bigZeta_phiA_twist_eq_smallZeta
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section
namespace GlobalTheory.ColumnRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]

def permGL (π : C ≃ C) : GL C k :=
  ⟨π.toPEquiv.toMatrix, π.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in

theorem frameMatrixFirstColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    X0 k σ' * (invT h).val = X0 k σ * (invT (permGL (σ.symm.trans σ') * h)).val := by
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply, invT_val, invT_val, _root_.mul_inv_rev]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul, Option.mem_def, Equiv.symm_apply_eq]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in

theorem frameMatrixSecondColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    Y0 k σ * (permGL (σ.symm.trans σ') * h).val = Y0 k σ' * h.val := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul]

variable [MeasurableSpace k] [BorelSpace k]

theorem fFun_renumber (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ)
    (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k) :
    fFun μ σ' ν Ψ X = ((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹ * fFun μ σ ν Ψ X := by
  set Q : GL C k := permGL (σ.symm.trans σ') with hQ
  by_cases hX : ∃ h : GL C k, X = X0 k σ' * (invT h).val
  · obtain ⟨h, rfl⟩ := hX
    have hc : (ν (gdet Q) : ℂ) * apow (gdet Q) ((Fintype.card C : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
    rw [splitTheta_fFun_frameFirstBlock_mul μ σ', frameMatrixFirstColumnBlock_renumber σ σ' h, splitTheta_fFun_frameFirstBlock_mul μ σ, ← hQ, frameMatrixSecondColumnBlock_renumber, gdet_mul, map_mul, apow_mul,
      Units.val_mul]
    have ha := apow_ne_zero (gdet Q) ((Fintype.card C : ℂ) / 2)
    have hn : (ν (gdet Q) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · have hX' : ¬ ∃ h : GL C k, X = X0 k σ * (invT h).val := fun H =>
      hX ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ' X).1 ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 H))
    rw [fFun, dif_neg hX, fFun, dif_neg hX', mul_zero]

end GlobalTheory.ColumnRenumber

open GlobalTheory.ColumnRenumber in

theorem GlobalTheory.ColumnRenumber.phiA_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (A A' C : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ),
    ∃ u : ℂ, u ≠ 0 ∧ ∀ (ϖ : kˣ) (n : ℕ) (Λ : Submodule 𝒪[k] (C → k)) (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k),
      phiA μ σ' ν ϖ n Λ Ψ X = u * phiA μ σ ν ϖ n Λ Ψ X := by
  intro k _ _ _ _ _ _ A A' C _ _ _ _ _ _ μ _ σ σ' ν
  refine ⟨((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹,
    inv_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)), fun ϖ n Λ Ψ X => ?_⟩
  unfold phiA
  split_ifs
  · exact fFun_renumber μ σ σ' ν Ψ X
  · rw [mul_zero]
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_primitiveFrameDatum_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (A A' C : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ),
    ∃ u : ℂ, u ≠ 0 ∧ ∀ (ϖ : kˣ) (n : ℕ) (Λ : Submodule 𝒪[k] (C → k)) (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k),
      phiA μ σ' ν ϖ n Λ Ψ X = u * phiA μ σ ν ϖ n Λ Ψ X := by
  atlas_forward_decl GlobalTheory.ColumnRenumber.phiA_renumber
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

namespace GlobalTheory.PurityDepth

theorem hasDepth_scaled : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (ϖ : kˣ) (P : Finset C) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ M : ℕ, ∀ n, 2 * M ≤ n →
      HasDepth ϖ n (blockLat ϖ n P) (fun Y => Ψ (Y * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)))) := by
  intro k _ _ _ _ A' C _ _ _ _ ϖ P Ψ hΨ hϖ
  have hΨ' : Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix A' C k) := hΨ
  have hϖ' : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := fun x => by rw [hϖ, le_uniformizer_iff]
  obtain ⟨Λ, hΛ, hinv⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k A' C Ψ hΨ'
  let f : (A' × C → k) → Matrix A' C k := fun z => Matrix.of fun i j => z (i, j)
  have hf : Continuous f := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_apply (i, j)
  have hΛn : f ⁻¹' (Λ : Set (Matrix A' C k)) ∈ nhds (0 : A' × C → k) :=
    (hΛ.preimage hf).mem_nhds (by
      show f 0 ∈ Λ
      exact (show f 0 = 0 from rfl) ▸ Λ.zero_mem)
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ q : A' × C, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix A' C k => x q.1 q.2) '' tsupport Ψ ⊆ GlobalTheory.SplitWeil.cball (ϖ ^ e)⁻¹ := fun q =>
    GlobalTheory.AdaptedExp.eventually_subset_cball hϖ' (hc.image (by fun_prop))
  obtain ⟨M, hM1, hM2⟩ := ((Filter.eventually_all.2 h1).and (GlobalTheory.AdaptedExp.eventually_box_subset hϖ' hΛn)).exists
  refine ⟨M, fun n hn => ?_⟩

  set w := valuation k (ϖ : k) with hw
  have hw1 : w ≤ 1 := hϖ.mem
  set u := valuation k ((ϖ ^ M : kˣ) : k) with hu
  have hu0 : 0 < u := zero_lt_iff.2 (by simp [hu])
  have huw : u = w ^ M := by rw [hu, Units.val_pow_eq_pow_val, map_pow]
  have hinvu : valuation k (((ϖ ^ M)⁻¹ : kˣ) : k) = u⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  have hn' : valuation k ((ϖ ^ n : kˣ) : k) ≤ u * u := by
    rw [Units.val_pow_eq_pow_val, map_pow, huw, ← pow_add, ← two_mul]
    exact pow_le_pow_right_of_le_one' hw1 hn
  have hd : ∀ (X : Matrix A' C k) i j, (X * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) i j = X i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)) :=
    fun X i j => mul_diagonal _ _ _ _
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · by_contra hne
    apply hY
    have hs := subset_tsupport _ hne
    have he : ∀ i j, valuation k (Y i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k))) ≤ u⁻¹ :=
      fun i j => by
        have := hM1 (i, j) ⟨_, hs, rfl⟩
        simpa only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, hd, hinvu] using this
    refine GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
    · have h := he i j
      rw [if_pos hj, map_mul, ← hu] at h
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ ^ n : kˣ) : k) * valuation k (Y i j) ≤ u * u * valuation k (Y i j) :=
            mul_le_mul_left hn' _
        _ = u * (valuation k (Y i j) * u) := by rw [mul_assoc, mul_comm u (valuation k (Y i j))]
        _ ≤ u * u⁻¹ := mul_le_mul_right h _
        _ = 1 := mul_inv_cancel₀ hu0.ne'
    · have h := he i j
      rw [if_neg hj, map_mul, hinvu] at h
      rw [Valuation.mem_integer_iff]
      have := mul_le_mul_left h u
      rwa [mul_assoc, inv_mul_cancel₀ hu0.ne', mul_one] at this
  · obtain ⟨h1, h2⟩ := GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.1 hZ
    show Ψ ((Y + Z) * _) = Ψ (Y * _)
    rw [Matrix.add_mul]
    refine hinv _ _ ?_
    refine hM2 (fun q => (Z * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) q.1 q.2) ?_
    unfold GlobalTheory.StepData.box
    intro q
    beta_reduce
    rw [hd, map_mul, ← hu]
    by_cases hj : q.2 ∈ P
    · rw [if_pos hj, ← hu]
      calc valuation k (Z q.1 q.2) * u ≤ 1 * u := mul_le_mul_left (h1 q.1 q.2 hj) _
        _ = u := one_mul u
    · rw [if_neg hj, hinvu]
      calc valuation k (Z q.1 q.2) * u⁻¹ ≤ u * u * u⁻¹ := mul_le_mul_left ((h2 q.1 q.2 hj).trans hn') _
        _ = u := by rw [mul_assoc, mul_inv_cancel₀ hu0.ne', mul_one]

end GlobalTheory.PurityDepth
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_blockScaled_hasLatticeDepth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (ϖ : kˣ) (P : Finset C) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ M : ℕ, ∀ n, 2 * M ≤ n →
      HasDepth ϖ n (blockLat ϖ n P) (fun Y => Ψ (Y * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)))) := by
  atlas_forward_decl GlobalTheory.PurityDepth.hasDepth_scaled
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

namespace GlobalTheory.PureMatch

theorem smallP_smul_measure_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {A A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) (c : NNReal) (z : ℂ) (σ : A ⊕ A' ≃ C) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ)
    (h : GL C k) : smallP (c • μ) σ ν α (fun Y => z * Ψ Y) h = (c : ℂ) * z * smallP μ σ ν α Ψ h := by
  simp only [smallP, smallF, mul_assoc, integral_const_mul, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]
  ring

theorem bigZetaIntegral_const_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {a : ℕ} {A' C : Type} [Fintype C] [DecidableEq C]
    (μ : @Measure (GL (Fin a) k) Units.instMeasurableSpace) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (z : ℂ)
    (Φ : Matrix (Fin a) C k → ℂ) (h : GL C k) :
    bigP μ ϖ σ ν β (fun Z => z * Φ Z) h = z * bigP μ ϖ σ ν β Φ h := by
  simp only [bigZetaIntegral_eq, bigF, shellSum_smul]
  ring

theorem exists_depth_bigP_eq_smallP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ₀ : Measure (GL A' k)) [μ₀.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (P : Finset C) (g₀ : GL (Fin a) k) (c₀ : GL C k) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ m : ℕ, ∀ n, 2 * m ≤ n →
      ∀ (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ' : Fin a ⊕ A' ≃ C) (r : ℂ), r ≠ 0 → ∃ Ξ : Matrix A' C k → ℂ,
        HasDepth ϖ n (blockLat ϖ n P) Ξ ∧
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => r * phiA μ σ' ν ϖ n (blockLat ϖ n P) Ξ
          (g₀.val * Z * (c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹)).val)) = smallP μ₀ σ ν (ν * β) Ψ := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ₀ _ σ ν β ϖ P g₀ c₀ Ψ hΨ hϖ
  have hΨ' : (fun Y : Matrix A' C k => Ψ (Y * c₀.valᵀ)) ∈ GlobalTheory.WeilM.SB (Matrix A' C k) := by
    have := comp_mul_mem_SB (1 : GL A' k) (invT c₀)⁻¹ hΨ
    simp only [invT_inv_val, Units.val_one, Matrix.one_mul] at this
    exact this
  obtain ⟨m, hm⟩ := GlobalTheory.T.schwartzBruhat_blockScaled_hasLatticeDepth k A' C ϖ P _ hΨ' hϖ
  refine ⟨m, fun n hn μ _ σ' r hr => ?_⟩
  obtain ⟨u, hu, hphi⟩ := GlobalTheory.T.exists_ne_zero_primitiveFrameDatum_renumber k (Fin a) A' C μ σ σ' ν
  obtain ⟨c, hc0, hc⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ = c • μ₀ :=
    ⟨Measure.haarScalarFactor μ μ₀, (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne',
      Measure.isMulLeftInvariant_eq_smul μ μ₀⟩
  set N : GL C k := c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹) with hN
  set κ : ℂ := (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) * (ν (gdet N) : ℂ) *
    apow (gdet N) ((Fintype.card C : ℂ) / 2) with hκ
  have hκ0 : κ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)) (Units.ne_zero _)) (apow_ne_zero _ _)
  have hc0' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  have hNT : ∀ Y : Matrix A' C k, Y * N.valᵀ =
      Y * diagonal (fun col => if col ∈ P then ((ϖ ^ m : kˣ) : k) else (((ϖ ^ m)⁻¹ : kˣ) : k)) * c₀.valᵀ := by
    intro Y
    rw [hN, Units.val_mul, transpose_mul, diagGL_val, diagonal_transpose, Matrix.mul_assoc]
    congr 3
    funext col
    split_ifs <;> rfl
  refine ⟨fun Y => (κ / (r * u * c)) * Ψ (Y * N.valᵀ), ?_, ?_⟩
  · have h1 := (depthSpace A' ϖ n (blockLat ϖ n P)).smul_mem (κ / (r * u * c)) (hm n hn)
    simp only [hNT]
    exact h1
  · funext h
    have h2 := GlobalTheory.T.zetaIntegral_twoSidedMovedDatum_eq_smallZeta k a A' C μ σ ν β ϖ n (blockUnits ϖ n P)
      (fun Y => (κ / (r * u * c)) * Ψ (Y * N.valᵀ)) g₀ N h hϖ
    have h3 : ∀ Y : Matrix A' C k, Y * (invT N).val * N.valᵀ = Y := fun Y => by
      rw [Matrix.mul_assoc, ← invT_inv_val, Units.mul_inv, Matrix.mul_one]
    simp only [h3] at h2
    have h4 := smallP_smul_measure_mul μ₀ c (κ / (r * u * c)) σ ν (ν * β) Ψ h
    rw [← hc, ← h2, ← hκ] at h4
    simp only [hphi, ← mul_assoc]
    rw [bigZetaIntegral_const_mul]
    apply mul_left_cancel₀ hκ0
    rw [mul_left_comm]
    refine (congrArg (fun x => r * u * x) h4).trans ?_
    field_simp

end GlobalTheory.PureMatch
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_depth_splitThetaBig_eq_small_blockTranslate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ₀ : Measure (GL A' k)) [μ₀.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (P : Finset C) (g₀ : GL (Fin a) k) (c₀ : GL C k) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ m : ℕ, ∀ n, 2 * m ≤ n →
      ∀ (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ' : Fin a ⊕ A' ≃ C) (r : ℂ), r ≠ 0 → ∃ Ξ : Matrix A' C k → ℂ,
        HasDepth ϖ n (blockLat ϖ n P) Ξ ∧
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => r * phiA μ σ' ν ϖ n (blockLat ϖ n P) Ξ
          (g₀.val * Z * (c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹)).val)) = smallP μ₀ σ ν (ν * β) Ψ := by
  atlas_forward_decl GlobalTheory.PureMatch.exists_depth_bigP_eq_smallP
end

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_smul {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type}
    (_hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (hΛ : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := by

  have key : ∀ a : k', valuation k' a ≤ 1 → ∀ y ∈ Λ₂, a • y ∈ Λ₂ := fun a ha y hy =>
    Λ₂.smul_mem (⟨a, (Valuation.mem_integer_iff _ _).2 ha⟩ : 𝒪[k']) hy
  have hc₂ : valuation k' (c₂ : k') ≠ 0 := by simp
  set u : k' := (c₂⁻¹ : k'ˣ) * j c with hu
  have hu1 : valuation k' u = 1 := by
    rw [hu, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hc, inv_mul_cancel₀ hc₂]
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  have hu1' : valuation k' u⁻¹ = 1 := by rw [map_inv₀, hu1, inv_one]
  intro x
  rw [mem_smul_lat, mem_smul_lat, ← hΛ]
  have heq : (c₂⁻¹ : k'ˣ) • (fun d => j (x (cD d))) = u • (fun d => j (((c⁻¹ : kˣ) • x) (cD d))) := by
    funext d
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, map_mul, hu, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
  rw [heq]
  constructor
  · intro h
    have := key u⁻¹ hu1'.le _ h
    rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul] at this
  · exact key u hu1.le _

end GlobalTheory.PureMatch.Transport
end
end

section
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport

theorem dualLat_latCorr {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
    {D D₂ : Type} [Fintype D] [Fintype D₂] (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  have key : ∀ y x : D → k, (fun c => j (y (cD c))) ⬝ᵥ (fun c => j (x (cD c))) = j (y ⬝ᵥ x) := by
    intro y x
    simp only [dotProduct, map_sum, map_mul]
    exact Fintype.sum_equiv cD _ _ fun c => rfl
  intro y
  rw [mem_dualLat, mem_dualLat]
  constructor
  · intro H x hx
    have := H _ ((h x).2 hx)
    rw [key] at this
    exact (hj.2.2 _).1 this
  · intro H x₂ hx₂
    set x : D → k := fun d => j.symm (x₂ (cD.symm d)) with hxdef
    have hx : (fun c => j (x (cD c))) = x₂ := by
      funext c; simp [x]
    rw [← hx] at hx₂ ⊢
    rw [key]
    exact (hj.2.2 _).2 (H x ((h x).1 hx₂))

end GlobalTheory.PureMatch.Transport
end

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_correspondingLattices : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [Fintype D] [Fintype D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  atlas_forward_decl GlobalTheory.PureMatch.Transport.dualLat_latCorr
end

section
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_blockLat : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [DecidableEq D] [DecidableEq D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ}, IsUnif ϖ → IsUnif ϖ₂ → ∀ (e : ℕ) (P : Finset D) (P₂ : Finset D₂), (∀ c, c ∈ P₂ ↔ cD c ∈ P) → LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := by
  intro k k' _ _ _ _ _ _ _ _ j D D₂ _ _ hj cD ϖ ϖ₂ hϖ hϖ₂ e P P₂ hP x
  have hu : valuation k' (j (ϖ : k)) = valuation k' (ϖ₂ : k') := by
    have h1 := isUnif_map hj hϖ
    exact h1.trans hϖ₂.symm
  have hb : ∀ c : D₂, valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k') =
      valuation k' (j (blockUnits ϖ e P (cD c) : kˣ)) := by
    intro c
    by_cases hc : c ∈ P₂
    · have hc' : cD c ∈ P := (hP c).1 hc
      simp only [blockUnits, if_pos hc, if_pos hc', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
        map_pow, hu]
    · have hc' : cD c ∉ P := fun h => hc ((hP c).2 h)
      simp [blockUnits, hc, hc']
  show (∀ c, valuation k' (j (x (cD c))) ≤ valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k')) ↔
    ∀ d, valuation k (x d) ≤ valuation k ((blockUnits ϖ e P d : kˣ) : k)
  simp only [hb, val_le_iff hj]
  exact ⟨fun h d => by simpa using h (cD.symm d), fun h c => h (cD c)⟩

end GlobalTheory.PureMatch.Transport
end
end

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.correspondingLattices_blockLattice : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [DecidableEq D] [DecidableEq D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ}, IsUnif ϖ → IsUnif ϖ₂ → ∀ (e : ℕ) (P : Finset D) (P₂ : Finset D₂), (∀ c, c ∈ P₂ ↔ cD c ∈ P) → LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := by
  atlas_forward_decl GlobalTheory.PureMatch.Transport.latCorr_blockLat
end

section
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport
namespace PrimFrameTr

section Fields
variable {k k' : Type} [Field k] [Field k']

theorem rank_map_le {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (f : k →+* k') (Z : Matrix A D k) :
    (Z.map f).rank ≤ Z.rank := by
  classical
  let M := LinearMap.range Z.mulVecLin
  let b := Module.finBasis k M
  have hc : ∀ y : D, (fun x => Z x y) ∈ M := fun y => ⟨Pi.single y 1, by ext x; simp⟩
  let P : Matrix A (Fin (Module.finrank k M)) k := Matrix.of fun x l => (b l : A → k) x
  let Q : Matrix (Fin (Module.finrank k M)) D k := Matrix.of fun l y => b.repr ⟨fun x => Z x y, hc y⟩ l
  have hPQ : Z = P * Q := by
    ext x y
    have h := congrArg (fun z : M => (z : A → k) x) (b.sum_repr ⟨fun x => Z x y, hc y⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [P, Q, Matrix.of_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have h : Z.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
  simp [Matrix.rank, M]

theorem rank_map_equiv {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (j : k ≃+* k') (Z : Matrix A D k) :
    (Z.map j).rank = Z.rank := by
  refine le_antisymm (rank_map_le (j : k →+* k') Z) ?_
  have := rank_map_le (j.symm : k' →+* k) (Z.map j)
  have e : (Z.map j).map (j.symm : k' →+* k) = Z := by ext; simp
  rwa [e] at this

theorem rank_trM {A D A₂ D₂ : Type} [Fintype A] [Fintype D] [DecidableEq D] [Fintype D₂]
    (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) : (trM j rA cD Z).rank = Z.rank := by
  have : trM j rA cD Z = (Z.map j).submatrix rA cD := by ext; rfl
  rw [this, Matrix.rank_submatrix, rank_map_equiv]

theorem row_trM {A D A₂ D₂ : Type} (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) (r : A₂) :
    (trM j rA cD Z).row r = fun c => j (Z.row (rA r) (cD c)) := rfl

theorem read_sum {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (c : A → k) :
    (fun d => j ((∑ a, c a • Z.row a) (cD d))) = ∑ r, j (c (rA r)) • (trM j rA cD Z).row r := by
  funext d
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, row_trM]
  exact (Fintype.sum_equiv rA _ _ fun r => rfl).symm

theorem mem_spanK_of {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span k (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
  rw [read_sum j rA cD Z c]
  exact (Submodule.mem_span_range_iff_exists_fun k').2 ⟨_, rfl⟩

end Fields

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}

theorem isLocIso_symm (hj : IsLocIso j) : IsLocIso j.symm :=
  ⟨hj.2.1, by simpa using hj.1, fun x => by rw [← hj.2.2 (j.symm x)]; simp⟩

theorem mem_spanO_of (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span 𝒪[k] (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 hx
  have h := read_sum j rA cD Z (fun a => (c a : k))
  have e : (∑ a, c a • Z.row a) = ∑ a, (c a : k) • Z.row a := Finset.sum_congr rfl fun a _ => rfl
  rw [e, h]
  exact (Submodule.mem_span_range_iff_exists_fun 𝒪[k']).2
    ⟨fun r => ⟨j (c (rA r)), (hj.2.2 _).2 (c (rA r)).2⟩, rfl⟩

theorem read_symm {D D₂ : Type} (cD : D₂ ≃ D) (x : D → k) :
    (fun d => j.symm ((fun c => j (x (cD c))) (cD.symm d))) = x := by
  funext d; simp

theorem trM_symm {A D A₂ D₂ : Type} (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) :
    trM j.symm rA.symm cD.symm (trM j rA cD Z) = Z := trM_symm_trM j rA cD Z

def readEquiv (j : k ≃+* k') {D D₂ : Type} (cD : D₂ ≃ D) : (D → k) ≃ (D₂ → k') where
  toFun x d := j (x (cD d))
  invFun y d := j.symm (y (cD.symm d))
  left_inv x := by funext d; simp
  right_inv y := by funext d; simp

theorem memK_iff {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span k (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanK_of j rA cD Z⟩
  have := mem_spanK_of j.symm rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

theorem memO_iff (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span 𝒪[k] (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanO_of hj rA cD Z⟩
  have := mem_spanO_of (isLocIso_symm hj) rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

end PrimFrameTr

open PrimFrameTr in

theorem isPrimFrame_trM_iff {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂]
    [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂] (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (hL : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  have hc : Fintype.card A₂ = Fintype.card A := Fintype.card_congr rA
  have hm : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
    rw [mem_matLat, mem_matLat]
    refine (forall_congr' fun r => ?_).trans (rA.forall_congr_right (q := fun a => Z.row a ∈ Λ))
    exact hL (Z.row (rA r))
  have hs : (Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) =
        (Submodule.span k' (Set.range (trM j rA cD Z).row)).restrictScalars 𝒪[k'] ⊓ Λ₂) ↔
      (Submodule.span 𝒪[k] (Set.range Z.row) =
        (Submodule.span k (Set.range Z.row)).restrictScalars 𝒪[k] ⊓ Λ) := by
    rw [SetLike.ext_iff, SetLike.ext_iff]
    refine ((readEquiv j cD).forall_congr_right).symm.trans (forall_congr' fun x => ?_)
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    change ((fun d => j (x (cD d))) ∈ _ ↔ (fun d => j (x (cD d))) ∈ _ ∧ (fun d => j (x (cD d))) ∈ Λ₂) ↔ _
    rw [memO_iff hj, memK_iff, hL]
  unfold IsPrimFrame
  rw [rank_trM, hc, hm, hs]
end GlobalTheory.PureMatch.Transport
end
end

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂], IsLocIso j → ∀ (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → ∀ (Z : Matrix A D k), IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  atlas_forward_decl GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff
end

section
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

section
variable {k k' : Type} [Field k] [Field k'] {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem gdet_glTrEquiv_ffun (j : k ≃+* k') (e : D₂ ≃ D) (g : GL D k) :
    gdet (glTrEquiv j e g) = Units.map (j : k →* k') (gdet g) := by
  apply Units.ext
  show (glTrEquiv j e g).val.det = j g.val.det
  rw [glTrEquiv_val, show trM j e e g.val = (g.val.map j).submatrix e e from rfl, det_submatrix_equiv_self]
  exact ((j : k →+* k').map_det g.val).symm

theorem invT_glTrEquiv_ffun (j : k ≃+* k') (e : D₂ ≃ D) (g : GL D k) :
    (invT (glTrEquiv j e g)).val = trM j e e (invT g).val := by
  have h1 : (invT (glTrEquiv j e g)).val = ((glTrEquiv j e g)⁻¹).valᵀ := rfl
  have h2 : (invT g).val = (g⁻¹).valᵀ := rfl
  rw [h1, h2, ← map_inv, glTrEquiv_val]
  rfl

end

theorem fFun_trM : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂] [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k'] (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D) (μ₂ : Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D), (∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) → ∀ (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ), (∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) → ∀ (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k), fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z := by
  intro k k' _ _ _ _ _ _ _ _ j A A' D A₂ A₂' D₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj rA rA' cD μ₂ _ σ₂ σ hσ ν₂ ν hν Ψ Z
  have hcard : Fintype.card D₂ = Fintype.card D := Fintype.card_congr cD
  have hX : ∀ M : Matrix D D k, trM j rA cD (X0 k σ * M) = X0 k' σ₂ * trM j cD cD M := fun M => by
    ext r c
    rw [trM_apply, frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply, trM_apply, hσ]; rfl
  have hY : ∀ M : Matrix D D k, trM j rA' cD (Y0 k σ * M) = Y0 k' σ₂ * trM j cD cD M := fun M => by
    ext r c
    rw [trM_apply, frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply, trM_apply, hσ]; rfl
  have hS : ∀ Y : Matrix A' D k, smallF μ₂ ν₂ Ψ (trM j rA' cD Y) =
      smallF (pullMeas hj rA' μ₂) ν (fun Y => Ψ (trM j rA' cD Y)) Y := fun Y => by
    conv_lhs => rw [← map_pullMeas hj rA' μ₂]
    unfold smallF
    have := integral_map_equiv (μ := pullMeas hj rA' μ₂) (glTr hj rA').toHomeomorph.toMeasurableEquiv
      (fun g => Ψ (g.val * trM j rA' cD Y) * (ν₂ (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D₂ : ℂ) / 2))
    refine Eq.trans this ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show Ψ ((glTrEquiv j rA' g).val * trM j rA' cD Y) * ν₂ (gdet (glTrEquiv j rA' g)) *
      apow (gdet (glTrEquiv j rA' g)) _ = _
    rw [gdet_glTrEquiv_ffun, apow_map hj, ← hν, glTrEquiv_val, ← trM_mul, hcard]
  by_cases h : ∃ h : GL D k, Z = X0 k σ * (invT h).val
  · obtain ⟨h, rfl⟩ := h
    rw [hX, ← invT_glTrEquiv_ffun, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, gdet_glTrEquiv_ffun, apow_map hj, ← hν,
      glTrEquiv_val, ← hY, hS, hcard]
  · have h' : ¬ ∃ h₂ : GL D₂ k', trM j rA cD Z = X0 k' σ₂ * (invT h₂).val := by
      rintro ⟨h₂, H⟩
      obtain ⟨g, rfl⟩ := (glTrEquiv j cD).surjective h₂
      rw [invT_glTrEquiv_ffun, ← hX] at H
      exact h ⟨g, trM_injective j rA cD H⟩
    rw [fFun, fFun, dif_neg h, dif_neg h']

end GlobalTheory.PureMatch.Transport
end
end

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaFunction_transport_localFieldIso : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂] [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k'] (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D) (μ₂ : Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D), (∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) → ∀ (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ), (∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) → ∀ (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k), fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z := by
  atlas_forward_decl GlobalTheory.PureMatch.Transport.fFun_trM
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem corr_smul_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := latCorr_smul hj cD h c c₂ hc

theorem corr_dual_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := GlobalTheory.T.dualLattice_correspondingLattices hj cD h

theorem primFrame_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff hj rA cD h Z

theorem corr_blockLat_of (hj : IsLocIso j) (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂)
    (e : ℕ) (P : Finset D) (P₂ : Finset D₂) (hP : ∀ c, c ∈ P₂ ↔ cD c ∈ P) :
    LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := GlobalTheory.T.correspondingLattices_blockLattice hj cD hϖ hϖ₂ e P P₂ hP

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem fFun_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z :=
  GlobalTheory.T.zetaFunction_transport_localFieldIso hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν Ψ Z

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem latCorr_latA (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ) :
    LatCorr j cD (latA ϖ e Λ) (latA ϖ₂ e Λ₂) := by
  refine corr_smul_of hj cD (corr_dual_of hj cD h) _ _ ?_
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow, h1]

theorem trM_mem_matLat (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
  rw [mem_matLat, mem_matLat]
  refine ⟨fun H a => ?_, fun H r => (h (Z.row (rA r))).2 (H _)⟩
  obtain ⟨r, rfl⟩ := rA.surjective a
  exact (h (Z.row (rA r))).1 (H r)

theorem hasDepth_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ)
    (hϖ₂ : IsUnif ϖ₂) (e : ℕ) (Ξ : Matrix A D k → ℂ) (hΞ : HasDepth ϖ e Λ Ξ) :
    HasDepth ϖ₂ e Λ₂ (fun Y => Ξ (trM j.symm rA.symm cD.symm Y)) := by
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  have hs : LatCorr j cD (ϖ ^ e • Λ) (ϖ₂ ^ e • Λ₂) := corr_smul_of hj cD h _ _ (by
    simp only [Units.val_pow_eq_pow_val, map_pow]; rw [h1])
  refine ⟨fun Y hY => hΞ.1 _ fun hZ => hY ?_, fun Y W hW => ?_⟩
  · rw [← trM_trM_symm j rA cD Y]; exact (trM_mem_matLat rA cD h _).2 hZ
  · have hW' : trM j.symm rA.symm cD.symm W ∈ matLat A (ϖ ^ e • Λ) := by
      rw [← trM_mem_matLat rA cD hs, trM_trM_symm]; exact hW
    show Ξ (trM j.symm rA.symm cD.symm (Y + W)) = Ξ (trM j.symm rA.symm cD.symm Y)
    rw [show trM j.symm rA.symm cD.symm (Y + W) = trM j.symm rA.symm cD.symm Y + trM j.symm rA.symm cD.symm W by
      ext r c; simp]
    exact hΞ.2 _ _ hW'

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem phiA_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂)
    (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    phiA μ₂ σ₂ ν₂ ϖ₂ e Λ₂ Ψ (trM j rA cD Z) =
      phiA (pullMeas hj rA' μ₂) σ ν ϖ e Λ (fun Y => Ψ (trM j rA' cD Y)) Z := by
  classical
  unfold phiA
  rw [primFrame_corr hj rA cD (latCorr_latA hj cD h hϖ hϖ₂ e), fFun_corr hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν]

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch
open GlobalTheory.PureMatch.Transport GlobalTheory.FlipMatch

theorem mem_one_block_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T)
    (w : Pl D.host.E) {i j : Fin D.R.m} (e : Num G i j) (c : (locGrid G t w).Cols i j) :
    c ∈ Assignment.one.block _ _ ↔ GlobalTheory.SquareFlipReach.colE t w e c ∈ blockV e := by
  rcases c with c | c
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]

theorem phiA_transport_split_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  intro D T L sc G μ₀ hL t i j e w hw v hv τ hτ n
  subst hτ
  have hjj := isLocIso_complEquiv τ hv
  have hO := GivenAdm.givenLevel_open (G := G) hL hw ((i : ℕ), (j : ℕ))
  have hO' := isOpen_map_invT hO.1 hO.2
  haveI := isHaarMeasure_haarVol hO'.1 hO'.2
  have hϖv : IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  have hc := corr_blockLat_of hjj (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hϖv (isUnif_unifAt _) n (blockV e)
      (Assignment.one.block _ _) (mem_one_block_iff t _ e)
  refine ⟨pullMeas hjj (rowB t (splitPrime τ) i j)
      (haarVol ((givenLevel G t (splitPrime τ) ((i : ℕ), (j : ℕ))).map invT)), inferInstance,
    (Equiv.sumCongr (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j).symm (rowB t (splitPrime τ) i j).symm).trans
      ((stdSplit ((locGrid G t (splitPrime τ)).rank_square i j)).trans (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e)),
    fun Ψ Z => ?_, fun Ξ hΞ => ?_⟩
  · exact phiA_trM hjj (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j) (rowB t (splitPrime τ) i j)
      (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) _ _ _ (fun s => by simp) _ _ (fun x => rfl) hϖv
      (isUnif_unifAt _) n hc Ψ Z
  · exact ⟨_, hasDepth_trM hjj (rowB t (splitPrime τ) i j) (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hc hϖv
      (isUnif_unifAt _) n Ξ hΞ, fun Y => by
        show Ξ (trM _ _ _ (trM (GlobalTheory.LFun.SplitTie.complEquiv τ hv) (rowB t (splitPrime τ) i j)
          (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) Y)) = Ξ Y
        rw [trM_symm_trM]⟩

end GlobalTheory.PureMatch
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumPhiA_splitPlace_transport_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  atlas_forward_decl GlobalTheory.PureMatch.phiA_transport_split_place
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

namespace GlobalTheory.PureMatch

open GlobalTheory.LFun

theorem chrW_triple_split_nu : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil)
    (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ (w : Pl D.host.E) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    splitPrime τ = w →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ = ((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α τ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β τ := by
  intro D T L sc G μ₀ hL W M t i j e Bs Γ X hX w v hv τ hw
  subst hw
  have e1 : X.ν = G.nu t i (j + 1) := by
    show X.α / X.β = _
    rw [hX.α, hX.β]
    exact mul_div_mul_right_eq_div _ _ _
  refine ⟨?_, ?_⟩
  · ext x
    show (locChar X.ν (splitPrime τ) (Units.map (complMap hv).toMonoidHom x) : ℂ) = _
    rw [e1, locChar_eq_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)]
    have hj : (j : ℕ) < D.R.m := j.2
    simp only [GlobalTheory.FunObj.SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply,
      Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, div_eq_mul_inv]
    rfl
  · ext x
    show (locChar X.α (splitPrime τ) _ : ℂ) =
      (locChar (X.α / X.β) (splitPrime τ) _ * locChar X.β (splitPrime τ) _ : ℂˣ)
    simp [locChar]

end GlobalTheory.PureMatch
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleSquare_splitPlace_character_eq_localGrid : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil)
    (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ (w : Pl D.host.E) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    splitPrime τ = w →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ = ((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α τ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν τ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β τ := by
  atlas_forward_decl GlobalTheory.PureMatch.chrW_triple_split_nu
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach in

theorem GlobalTheory.PureMatch.pure_match : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v (hv : w.under (𝓞 D.host.F) = v) (hP : v ∈ Bs.P),
    ∀ g₀ : GL (Fin (spW G i j).rank) (Fv D.host.F v), ∀ c₀ : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v),
    ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)),
    ∀ s : GL (Fin (spV G i j).rank) (Fv D.host.F v) → GL (Fin (spV₁ G i j).rank) (Fv D.host.F v) → ℂ, (∀ K₁ K₂, s K₁ K₂ ≠ 0) →
    ∃ n Φ K₁ K₂, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      bigP (haarVol (KO _ (Fin (spW G i j).rank))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β (Bs.τ ⟨v, hP⟩))
          (fun Z => s K₁ K₂ * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ
            (GlobalTheory.SquareFlipReach.trA t hv e (g₀.1 * Z * c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1))) =
        smallP (haarVol (KO _ (Fin (spW₁ G i j).rank))) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α (Bs.τ ⟨v, hP⟩)) Ψ := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h R Rf hM hT w hw v hv hP g₀ c₀ Ψ hΨ s hs
  have hτ : splitPrime (Bs.τ ⟨v, hP⟩) = w := hT.2.2.2 ⟨v, hP⟩ w hw hv
  have hb : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro hmem
    apply hst.2 w hw
    have hd : GlobalTheory.HalfCompare.badInt D ∣ D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK :=
      ⟨D.host.d, by unfold GlobalTheory.HalfCompare.badInt; ring⟩
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have hψ := Good.hasConductor_psiAt W hb
  have hϖv : IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  obtain ⟨hν, hα⟩ := GlobalTheory.T.thetaTripleSquare_splitPlace_character_eq_localGrid hL W M t i j e Bs Γ X h w v hv (Bs.τ ⟨v, hP⟩) hτ
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_depth_splitThetaBig_eq_small_blockTranslate (Fv D.host.F v) (spW G i j).rank (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank))
    (haarVol (KO _ (Fin (spW₁ G i j).rank))) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β (Bs.τ ⟨v, hP⟩)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (blockV e) g₀ c₀ Ψ hΨ hϖv
  obtain ⟨μ, hμ, σ', hphi, hdep⟩ := GlobalTheory.T.datumPhiA_splitPlace_transport_eq hL t i j e w hw v hv (Bs.τ ⟨v, hP⟩) hτ (max (2 * m) (depthAt G w))
  let K₁ : GL (Fin (spV G i j).rank) (Fv D.host.F v) := diagGL fun _ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m
  let K₂ : GL (Fin (spV₁ G i j).rank) (Fv D.host.F v) := diagGL fun _ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m)⁻¹
  obtain ⟨Ξ, hΞ, heq⟩ := hm _ (le_max_left _ _) μ σ' (s K₁ K₂) (hs K₁ K₂)
  obtain ⟨Ξ', hΞ', hΞΞ'⟩ := hdep Ξ hΞ
  refine ⟨max (2 * m) (depthAt G w), invFourierSum (psiAt W w) (unifAt w) (max (2 * m) (depthAt G w))
    (Assignment.one.block _ _) Ξ', K₁, K₂, le_max_right _ _,
    FourierDepth.isNatDatum_invFourierSum (isUnif_unifAt w) hψ _ _ hΞ', ?_⟩
  have hsq : ∀ Z, sqCore W t i j w (max (2 * m) (depthAt G w)) (invFourierSum (psiAt W w) (unifAt w)
      (max (2 * m) (depthAt G w)) (Assignment.one.block _ _) Ξ') (trA t hv e Z) =
      phiA μ σ' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (max (2 * m) (depthAt G w))
        (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (max (2 * m) (depthAt G w)) (blockV e)) Ξ Z := by
    intro Z
    unfold sqCore
    rw [GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum _ _ _ _ _ _ _ (isUnif_unifAt w) hψ _ hΞ', hphi, hν]
    congr 1
    exact funext hΞΞ'
  have hblk : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 = (diagGL (fun col => if col ∈ blockV e then GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m
      else (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m)⁻¹)).val := by
    ext a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rcases a with a | a <;> rcases b with b | b <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, K₁, K₂, diagGL_val, blockV, diagonal_apply]
  rw [hα, ← heq]
  congr 1
  funext Z
  rw [Matrix.mul_assoc _ c₀.1, hblk, ← Units.val_mul, hsq]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegral_block_translate_of_flip_datum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v (hv : w.under (𝓞 D.host.F) = v) (hP : v ∈ Bs.P),
    ∀ g₀ : GL (Fin (spW G i j).rank) (Fv D.host.F v), ∀ c₀ : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v),
    ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)),
    ∀ s : GL (Fin (spV G i j).rank) (Fv D.host.F v) → GL (Fin (spV₁ G i j).rank) (Fv D.host.F v) → ℂ, (∀ K₁ K₂, s K₁ K₂ ≠ 0) →
    ∃ n Φ K₁ K₂, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      bigP (haarVol (KO _ (Fin (spW G i j).rank))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β (Bs.τ ⟨v, hP⟩))
          (fun Z => s K₁ K₂ * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ
            (GlobalTheory.SquareFlipReach.trA t hv e (g₀.1 * Z * c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1))) =
        smallP (haarVol (KO _ (Fin (spW₁ G i j).rank))) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α (Bs.τ ⟨v, hP⟩)) Ψ := by
  atlas_forward_decl GlobalTheory.PureMatch.pure_match
end
