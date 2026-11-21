import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairedPointsFirstLevelLawStatementStatement

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLevel

theorem finE_cast_mem {D : D7} (X Y : LSp D) (e : X = Y) (K : Subgroup (GL (Fin X.sp.rank) (Lev.EAf D)))
    (K' : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))) (h : HEq K K') (g : GA D X.sp) (hg : Lev.finE X.sp g ∈ K) :
    Lev.finE Y.sp (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g) ∈ K' := by
  subst e
  cases h
  exact hg

theorem toXf_mem_of_is {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T) (k : FinPt G (.grid 0 D.R.m))
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) :
    toXf k ∈ (levEnv D.sp.X' L.βX (L.datXt t)).J := by

  have hU : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram :=
    ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  have hX := finE_cast_mem (columnBlock L D.R.m) ⟨D.sp.X', L.ΛX⟩ (colY_m L) _ _
    (GlobalTheory.T.gridRowLevel_zero_inf_unitary_eq_datumLevel W S hL t (Nat.zero_le _)) k.1 hU
  exact hX

theorem levRow_zero_le : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _
  exact fun t k hk => toXf_mem_of_is ch.W ch.S.toGridChoice hS.core.lev t k hk

end GlobalTheory.FirstRowLevel

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridBottomLevel_le_formLevel_largeDepth : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  atlas_forward_decl GlobalTheory.FirstRowLevel.levRow_zero_le
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLaw

section Gen
variable {Gg Γg : Type} [Group Gg] [Group Γg] {Wg : Type} [NormedAddCommGroup Wg] [InnerProductSpace ℂ Wg]

theorem adForms_law (ι : Γg →* Gg) (ρ : Γg →* Module.End ℂ Wg) (J : Subgroup Gg) (χ : J →* ℂˣ) {F : Gg → Wg}
    (hF : F ∈ Bridge.AdForms ι ρ J χ) (h : Gg) (k : J) : F (h * k) = (χ k : ℂ) • F h := by
  have e := hF 1 h k
  rwa [map_one, one_mul, map_one, Module.End.one_apply] at e

end Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} {W : G.Weil} {U : Set T}

theorem cast_mul_unitaryAdelicGroup_of_eq {X Y : LSp D} (h : X = Y) (a b : GA D X.sp) :
    cast (congrArg (fun X : LSp D => GA D X.sp) h) (a * b) =
      cast (congrArg (fun X : LSp D => GA D X.sp) h) a * cast (congrArg (fun X : LSp D => GA D X.sp) h) b := by
  subst h; rfl

theorem toXf_mul (y k : FinPt G (.grid 0 D.R.m)) : toXf (y * k) = toXf y * toXf k := by
  unfold toXf
  rw [← map_mul, Subgroup.coe_mul]
  exact congrArg _ (cast_mul_unitaryAdelicGroup_of_eq (colY_m R.toLevCh) _ _)

theorem formC_apply (S : SumChoice W U) (t : T) (u : (R.HX t).H) (y : FinPt G (.grid 0 D.R.m)) :
    S.formC t u y = S.co ((R.HX t).e u (toXf y)) := rfl

theorem formC_mul (S : SumChoice W U) (hHX : R.models_HX) (t : T) (u : (R.HX t).H) (y k : FinPt G (.grid 0 D.R.m))
    (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) :
    S.formC t u (y * k) = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.formC t u y := by
  have h : ∀ F, F ∈ LinearMap.range (R.HX t).e → F ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ
      (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ := fun F hF => (hHX t).2.1 ▸ hF
  have e : (R.HX t).e u (toXf y * toXf k) =
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y) :=
    adForms_law (Bridge.ratF D.sp.X') _ _ _ (h _ (LinearMap.mem_range_self (R.HX t).e u)) (toXf y) ⟨toXf k, hk⟩
  calc S.formC t u (y * k) = S.co ((R.HX t).e u (toXf (y * k))) := formC_apply S t u (y * k)
    _ = S.co ((R.HX t).e u (toXf y * toXf k)) := congrArg (fun z => S.co ((R.HX t).e u z)) (toXf_mul y k)
    _ = S.co ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y)) := congrArg S.co e
    _ = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.co ((R.HX t).e u (toXf y)) := S.co.map_smul _ _
    _ = _ := congrArg _ (formC_apply S t u y).symm

theorem first_level_invariance : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (u : (R.HX t).H) (v : VV ℂ (wt ch.G (.top 0))) (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m))
      (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v (ch.S.formC t u (y 0 * k)) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v (ch.S.formC t u (y 0)) := by
  intro hP hS
  obtain ⟨a, h1⟩ := GlobalTheory.T.gridBottomLevel_le_formLevel_largeDepth
  obtain ⟨b, h2⟩ := GlobalTheory.T.paired_points_first_level_law_statement hP hS
  refine ⟨max a b, fun ε CF hC => ?_⟩
  obtain ⟨x₁, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x₂, h2⟩ := h2 ε CF (le_of_max_le_right hC)
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ u v x y k hk0
  have hk := h1 D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t k hk0
  have hC := h2 D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ x y k hk0 hk v
  rw [formC_mul ch.S s.core.models.HX t u (y 0) k hk]
  exact hC _

end GlobalTheory.FirstRowLaw

end
end
