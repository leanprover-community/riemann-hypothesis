import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutAt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormRepChange
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RepAtTup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefDensTh
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcIntGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TargetFact
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFstar
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountHoldsAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefXiTyped
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerFix
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.VolumeNormalizedOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhaseG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjOfUnimod
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApprox
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerInCongruenceHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GaPlusThHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdSPow
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OrbitStabilizerIndexHolds

section
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Part

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def clsSet (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (u' : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (Z : PairVal.MatR D) : Set (Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) :=
  {O | ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z,
    O = {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''}}

theorem cntE_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : PairVal.MatR D) :
    CntLocal.cntE (CntLocal.Tn u') F0 Λ Z = (clsSet F0 u' Λ Z).encard := rfl

theorem pd_of_ez {Λ : Submodule (𝓞 D.host.E) (VS D).V} {Z : PairVal.MatR D}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (h : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) : PD D Λ (lf D F0) u' F' :=
  ⟨h.1.1, h.1.2.1, h.2.2.2.1⟩

def termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (h : PD D Λ (lf D F0) u' F') : TermDef.Term D u u' F0 what₂ :=
  ⟨Λ, hΛ, TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F', h⟩⟩

theorem n0rel_refl (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :
    CntLocal.NilradicalFlagMoved F0 Λ F' F' :=
  ⟨1, ⟨TermDef.one_mem_NLam Λ (lf D F0), fun _ => rfl, rfl⟩, fun _ => rfl, rfl⟩

theorem dcrel_of_n0rel {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (hl₁ : IsLift Λ F₁) (hl₂ : IsLift Λ F₂) (h : CntLocal.NilradicalFlagMoved F0 Λ F₁ F₂) : DCRel Λ (lf D F0) F₁ F₂ := by
  obtain ⟨n, hn, he, hz⟩ := h
  refine ⟨n, hn.1, 1, TermDef.one_mem_NLam Λ F₁, fun a => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [Formalism.L2.SG.Pf.frame_last_td, Formalism.L2.SG.Pf.frame_last_td]
      exact hz.symm
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td, Formalism.L2.SG.Pf.frame_castSucc_td]
      exact (he i).symm
  · rw [hl₂.2, hl₁.2]
    exact hz.symm

theorem orbT_disj {Z : PairVal.MatR D} {γ₁ γ₂ : TermDef.Term D u u' F0 what₂} (hl : γ₁.lam = γ₂.lam)
    {O : Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))}
    (h₁ : O ∈ PairVal.orbT D u u' F0 what₂ γ₁ Z) (h₂ : O ∈ PairVal.orbT D u u' F0 what₂ γ₂ Z) : γ₁ = γ₂ := by
  obtain ⟨Λ₁, m₁, c₁⟩ := γ₁
  obtain ⟨Λ₂, m₂, c₂⟩ := γ₂
  simp only at hl
  subst hl
  obtain ⟨F₁, hF₁, ⟨p₁, hc₁⟩, rfl⟩ := h₁
  obtain ⟨F₂, hF₂, ⟨p₂, hc₂⟩, hO⟩ := h₂
  have hmem := (Set.ext_iff.1 hO F₁).1 ⟨hF₁, n0rel_refl Λ₁ F₁⟩
  have hdc := dcrel_of_n0rel hF₂.1.1 hF₁.1.1 hmem.2
  have e : TermDef.mk Λ₁ (lf D F0) (PD D Λ₁ (lf D F0) u') ⟨F₂, p₂⟩ =
      TermDef.mk Λ₁ (lf D F0) (PD D Λ₁ (lf D F0) u') ⟨F₁, p₁⟩ := Quot.sound hdc
  have hcc : c₁ = c₂ := hc₁.symm.trans (e.symm.trans hc₂)
  subst hcc
  rfl

theorem mem_orbT_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''} ∈
      PairVal.orbT D u u' F0 what₂ (termOf Λ hΛ F' (pd_of_ez hF)) Z :=
  ⟨F', hF, ⟨pd_of_ez hF, rfl⟩, rfl⟩

theorem repIn_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    RepIn u u' F0 what₂ (termOf Λ hΛ F' (pd_of_ez hF)) Z :=
  ⟨F', hF, ⟨pd_of_ez hF, rfl⟩⟩

theorem eligAt_termOf (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) {Z : PairVal.MatR D}
    {w : Point D.host.E (D.R.rS + 1)} (hZ : AtMat w Z) {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (hF : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z) :
    EligAt (termOf Λ hΛ F' (pd_of_ez hF)) w := by
  refine ⟨⟨⟨F', ⟨pd_of_ez hF, rfl⟩, hF.2.2.1⟩, ?_⟩, ⟨F', ⟨pd_of_ez hF, rfl⟩, hF.1.2.2, ?_⟩⟩
  · show TermDef.Gt Λ (lf D F0) (PD D Λ (lf D F0) u') (TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F', _⟩) ≠ 0
    rw [TermDef.Gt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _)]
    exact hF.1.2.2
  · obtain ⟨L, U, hL, hU, he⟩ := hZ
    refine ⟨L, U, hL, hU, ?_⟩
    rw [← he]
    congr 1
    exact hF.2.2.2.2

end Part

end Formalism.L2.SG.Pf.FibPart
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem fibSum_of (hD : TupFun M δ u u' F0 what₂) (hC : RepAtTup M δ u u' F0 what₂) (hB : OrbZT M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.FCount.FibSum M δ u u' F0 what₂ := by
  intro hA hT hP hN hR hE w hG Z hZ hfin
  have hpre : Pre M δ u u' F0 what₂ := ⟨hA, hT, hP, hN, hR, hE⟩
  let S : Set (TermDef.Term D u u' F0 what₂) := {γ | EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z}
  have hrep : ∀ γ ∈ S, RepIn u u' F0 what₂ γ Z := fun γ hγ => hC hpre γ w hG Z hZ hγ.1 hγ.2
  have hclsFin : ∀ Λ ∈ what₂, (clsSet F0 u' Λ Z).Finite := fun Λ hΛ =>
    Set.encard_ne_top_iff.1 (by rw [← cntE_eq]; exact hfin Λ hΛ)
  have hsub : ∀ γ : TermDef.Term D u u' F0 what₂,
      PairVal.orbT D u u' F0 what₂ γ Z ⊆ clsSet F0 u' γ.lam Z := by
    rintro γ O ⟨F', hF', -, rfl⟩
    exact ⟨F', hF', rfl⟩
  have horbFin : ∀ γ : TermDef.Term D u u' F0 what₂, (PairVal.orbT D u u' F0 what₂ γ Z).Finite := fun γ =>
    (hclsFin γ.lam γ.mem).subset (hsub γ)
  have hne : ∀ γ ∈ S, (PairVal.orbT D u u' F0 what₂ γ Z).Nonempty := by
    intro γ hγ
    obtain ⟨F', hF', hr⟩ := hrep γ hγ
    exact ⟨_, F', hF', hr, rfl⟩
  have hnc : ∀ γ ∈ S, (PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard = (PairVal.orbT D u u' F0 what₂ γ Z).ncard := by
    intro γ hγ
    rw [Set.ncard_def, Set.ncard_def, hB hpre γ w Z hγ.1 hZ (hrep γ hγ)]

  have hSfin : S.Finite := by
    have hU : S ⊆ ⋃ Λ ∈ (what₂ : Set (Submodule (𝓞 D.host.E) (VS D).V)), ⋃ O ∈ clsSet F0 u' Λ Z,
        {γ : TermDef.Term D u u' F0 what₂ | γ.lam = Λ ∧ O ∈ PairVal.orbT D u u' F0 what₂ γ Z} := by
      intro γ hγ
      obtain ⟨O, hO⟩ := hne γ hγ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨γ.lam, γ.mem, O, hsub γ hO, rfl, hO⟩
    refine Set.Finite.subset ?_ hU
    refine Set.Finite.biUnion what₂.finite_toSet (fun Λ hΛ => Set.Finite.biUnion (hclsFin Λ hΛ) (fun O _ => ?_))
    refine Set.Subsingleton.finite (fun γ₁ h₁ γ₂ h₂ => ?_)
    exact orbT_disj (h₁.1.trans h₂.1.symm) h₁.2 h₂.2

  have hrow : ∀ Λ ∈ what₂, ∑ γ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
      ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) = ((clsSet F0 u' Λ Z).ncard : ℝ) := by
    intro Λ hΛ
    have hbU : (hclsFin Λ hΛ).toFinset =
        (hSfin.toFinset.filter (fun γ => γ.lam = Λ)).biUnion (fun γ => (horbFin γ).toFinset) := by
      ext O
      simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨F', hF', rfl⟩
        refine ⟨termOf Λ hΛ F' (pd_of_ez hF'), ⟨⟨eligAt_termOf Λ hΛ hZ hF', ?_⟩, rfl⟩,
          mem_orbT_termOf Λ hΛ hF'⟩
        exact hD hpre _ w Z (eligAt_termOf Λ hΛ hZ hF') hZ (repIn_termOf Λ hΛ hF')
      · rintro ⟨γ, ⟨-, hγΛ⟩, hO⟩
        have := hsub γ hO
        rw [hγΛ] at this
        exact this
    have hdisj : ∀ γ₁ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ), ∀ γ₂ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
        γ₁ ≠ γ₂ → Disjoint (horbFin γ₁).toFinset (horbFin γ₂).toFinset := by
      intro γ₁ h₁ γ₂ h₂ hne12
      rw [Finset.disjoint_left]
      intro O hO₁ hO₂
      rw [Set.Finite.mem_toFinset] at hO₁ hO₂
      exact hne12 (orbT_disj ((Finset.mem_filter.1 h₁).2.trans (Finset.mem_filter.1 h₂).2.symm) hO₁ hO₂)
    rw [Set.ncard_eq_toFinset_card _ (hclsFin Λ hΛ), hbU, Finset.card_biUnion hdisj]
    push_cast
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Set.ncard_eq_toFinset_card _ (horbFin γ)]

  have hreal : ∑ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) =
      CntLocal.nu (CntLocal.Tn u') F0 what₂ Z := by
    have e1 : ∀ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) =
        PairVal.massRow D F0 what₂ γ.lam * ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) := by
      intro γ hγ
      rw [hnc γ ((Set.Finite.mem_toFinset hSfin).1 hγ)]
      rfl
    rw [Finset.sum_congr rfl e1]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun γ : TermDef.Term D u u' F0 what₂ => γ.lam) (t := what₂)
      (fun γ _ => γ.mem)]
    have e2 : ∀ Λ ∈ what₂, ∑ γ ∈ hSfin.toFinset.filter (fun γ => γ.lam = Λ),
        PairVal.massRow D F0 what₂ γ.lam * ((PairVal.orbT D u u' F0 what₂ γ Z).ncard : ℝ) =
        PairVal.massRow D F0 what₂ Λ * ((clsSet F0 u' Λ Z).ncard : ℝ) := by
      intro Λ hΛ
      rw [← hrow Λ hΛ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun γ hγ => ?_)
      rw [(Finset.mem_filter.1 hγ).2]
    rw [Finset.sum_congr rfl e2]
    unfold CntLocal.nu PairVal.massRow
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun Λ _ => ?_)
    rw [Set.ncard_def, ← cntE_eq]
    unfold Formalism.MainNotions.S.Cnt.massRows
    ring
  haveI : Fintype {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} := hSfin.fintype
  have hs := hasSum_fintype (fun γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} =>
    (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
  have h1 : ∑ γ ∈ hSfin.toFinset, (PairVal.massTerm γ : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) =
      ∑ γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z},
        (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ) :=
    Finset.sum_subtype hSfin.toFinset (fun γ => Set.Finite.mem_toFinset hSfin) _
  have h2 : ((∑ γ ∈ hSfin.toFinset, PairVal.massTerm γ * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℝ) : ℝ) : ℂ) =
      ∑ γ ∈ hSfin.toFinset, (PairVal.massTerm γ : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) := by
    push_cast
    rfl
  have key := h1.symm.trans (h2.symm.trans (congrArg (fun x : ℝ => (x : ℂ)) hreal))
  exact Eq.mpr (congrArg (HasSum _) key.symm) hs

end Count

end Formalism.L2.SG.Pf.FibPart
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SumFr

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem lam_of_termScal {γ γ' : TermDef.Term D u u' F0 what₂} (h : Corank.TermScal D γ γ') : γ'.lam = γ.lam := by
  obtain ⟨p, h1, h2, -⟩ := h
  rw [← h1, ← h2]
  rfl

theorem sumFr_of (hD : TupFun M δ u u' F0 what₂) (hC : RepAtTup M δ u u' F0 what₂) (hB : OrbZT M δ u u' F0 what₂)
    (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hP : PrimeHyp D u (Tu D u'))
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hR : IsRowReps D F0 what₂)
    (hfin : ∀ Λ ∈ what₂, ∀ Z : PairVal.MatR D, CntLocal.cntE (CntLocal.Tn u') F0 Λ Z ≠ ⊤) :
    SumFr M δ u u' F0 what₂ := by
  intro γ w _ w' hG' _ Z hZ
  have hpre : Pre M δ u u' F0 what₂ := ⟨hA, hT, hP, hN, hR, eligRel_holds⟩
  have hclsFin : (clsSet F0 u' γ.lam Z).Finite :=
    Set.encard_ne_top_iff.1 (by rw [← cntE_eq]; exact hfin γ.lam γ.mem Z)
  have hfrSub : frPart γ Z ⊆ clsSet F0 u' γ.lam Z := by
    rintro O ⟨F', hF', -, rfl⟩
    exact ⟨F', hF', rfl⟩
  let S : Set (TermDef.Term D u u' F0 what₂) :=
    {γ' | (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z}
  have hlam : ∀ γ' ∈ S, γ'.lam = γ.lam := fun γ' h => lam_of_termScal h.1.1
  have hrep : ∀ γ' ∈ S, RepIn u u' F0 what₂ γ' Z := fun γ' h => hC hpre γ' w' hG' Z hZ h.1.2 h.2
  have hsub : ∀ γ' ∈ S, PairVal.orbT D u u' F0 what₂ γ' Z ⊆ frPart γ Z := by
    rintro γ' h O ⟨F', hF', hr, rfl⟩
    refine ⟨F', ?_, ⟨γ', h.1.1, hr⟩, ?_⟩
    · have e := hlam γ' h
      rw [e] at hF'
      exact hF'
    · have e := hlam γ' h
      ext F''
      simp only [Set.mem_setOf_eq]
      rw [e]
      exact Iff.rfl
  have horbFin : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' Z).Finite := fun γ' h =>
    (hclsFin.subset hfrSub).subset (hsub γ' h)
  have hne : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' Z).Nonempty := by
    intro γ' h
    obtain ⟨F', hF', hr⟩ := hrep γ' h
    exact ⟨_, F', hF', hr, rfl⟩
  have hnc : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard = (PairVal.orbT D u u' F0 what₂ γ' Z).ncard := by
    intro γ' h
    rw [Set.ncard_def, Set.ncard_def, hB hpre γ' w' Z h.1.2 hZ (hrep γ' h)]
  have hSfin : S.Finite := by
    have hU : S ⊆ ⋃ O ∈ frPart γ Z,
        {γ' : TermDef.Term D u u' F0 what₂ | γ'.lam = γ.lam ∧ O ∈ PairVal.orbT D u u' F0 what₂ γ' Z} := by
      intro γ' h
      obtain ⟨O, hO⟩ := hne γ' h
      simp only [Set.mem_iUnion]
      exact ⟨O, hsub γ' h hO, hlam γ' h, hO⟩
    refine Set.Finite.subset (Set.Finite.biUnion (hclsFin.subset hfrSub) (fun O _ => ?_)) hU
    refine Set.Subsingleton.finite (fun γ₁ h₁ γ₂ h₂ => ?_)
    exact orbT_disj (h₁.1.trans h₂.1.symm) h₁.2 h₂.2

  have hbU : (hclsFin.subset hfrSub).toFinset =
      hSfin.toFinset.biUnion (fun γ' => if h : γ' ∈ S then (horbFin γ' h).toFinset else ∅) := by
    ext O
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion]
    constructor
    · rintro ⟨F', hF', ⟨γ', hsc, hr⟩, rfl⟩
      have e := lam_of_termScal hsc
      obtain ⟨Λ, m, c⟩ := γ
      obtain ⟨Λ', m', c'⟩ := γ'
      simp only at e
      subst e
      obtain ⟨hpd, hc⟩ := hr
      have hγ' : (⟨Λ', m', c'⟩ : TermDef.Term D u u' F0 what₂) = termOf Λ' m' F' (pd_of_ez hF') := by
        simp only [termOf] at hc ⊢
        rw [← hc]
      have hS' : (⟨Λ', m', c'⟩ : TermDef.Term D u u' F0 what₂) ∈ S := by
        refine ⟨⟨hsc, ?_⟩, ?_⟩
        · rw [hγ']
          exact eligAt_termOf Λ' m' hZ hF'
        · rw [hγ']
          exact hD hpre _ w' Z (eligAt_termOf Λ' m' hZ hF') hZ (repIn_termOf Λ' m' hF')
      refine ⟨⟨Λ', m', c'⟩, hS', ?_⟩
      simp only [dif_pos hS', Set.Finite.mem_toFinset]
      exact ⟨F', hF', ⟨hpd, hc⟩, rfl⟩
    · rintro ⟨γ', hγ'S, hO⟩
      have hO' : O ∈ (horbFin γ' hγ'S).toFinset := by simpa only [dif_pos hγ'S] using hO
      exact hsub γ' hγ'S ((Set.Finite.mem_toFinset _).1 hO')
  have hdisj : ∀ γ₁ ∈ hSfin.toFinset, ∀ γ₂ ∈ hSfin.toFinset, γ₁ ≠ γ₂ →
      Disjoint (if h : γ₁ ∈ S then (horbFin γ₁ h).toFinset else ∅)
        (if h : γ₂ ∈ S then (horbFin γ₂ h).toFinset else ∅) := by
    intro γ₁ h₁ γ₂ h₂ hne12
    rw [Set.Finite.mem_toFinset] at h₁ h₂
    rw [dif_pos h₁, dif_pos h₂, Finset.disjoint_left]
    intro O hO₁ hO₂
    rw [Set.Finite.mem_toFinset] at hO₁ hO₂
    exact hne12 (orbT_disj ((hlam γ₁ h₁).trans (hlam γ₂ h₂).symm) hO₁ hO₂)
  have hcount : ((frPart γ Z).ncard : ℝ) =
      ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ (hclsFin.subset hfrSub), hbU, Finset.card_biUnion hdisj]
    push_cast
    refine Finset.sum_congr rfl (fun γ' hγ' => ?_)
    have h := (Set.Finite.mem_toFinset hSfin).1 hγ'
    rw [dif_pos h, hnc γ' h, Set.ncard_eq_toFinset_card _ (horbFin γ' h)]
  refine ⟨hclsFin.subset hfrSub, ?_⟩
  haveI : Fintype {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z} := hSfin.fintype
  have hs := hasSum_fintype (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z} =>
    ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
  have h1 : ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℂ) =
      ∑ γ' : {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z},
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) :=
    Finset.sum_subtype hSfin.toFinset (fun γ' => Set.Finite.mem_toFinset hSfin) _
  have h2 : (((frPart γ Z).ncard : ℝ) : ℂ) =
      ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℂ) := by
    rw [hcount]
    push_cast
    rfl
  have key := h1.symm.trans h2.symm
  have key' : ∑ γ' : {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z},
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) = ((frPart γ Z).ncard : ℂ) := by
    rw [key]
    push_cast
    rfl
  exact Eq.mpr (congrArg (HasSum _) key'.symm) hs

end SumFr

end Formalism.L2.SG.Pf.FibPart
end
end

section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MatAlg

variable {K : Type*} [Field K] {n : ℕ}

theorem lam_form {A Δ : Matrix (Fin n) (Fin n) K} (hA : IsLo A) (a : K) :
    (A + a • Δ) * A⁻¹ = 1 + a • (Δ * A⁻¹) := by
  have hu : IsUnit A.det := by rw [det_lo' hA]; exact isUnit_one
  rw [Matrix.add_mul, Matrix.mul_nonsing_inv A hu, Matrix.smul_mul]

theorem mu_form {B Δ : Matrix (Fin n) (Fin n) K} (hB : IsUp B) (a : K) :
    B⁻¹ * (B + a • Δ) = 1 + a • (B⁻¹ * Δ) := by
  have hu : IsUnit B.det := by rw [det_up' hB]; exact isUnit_one
  rw [Matrix.mul_add, Matrix.nonsing_inv_mul B hu, Matrix.mul_smul]

theorem one_smul_apply (a : K) (N : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (1 + a • N) i j = (if i = j then 1 else 0) + a * N i j := by
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

end MatAlg

section Typed

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem sgn_mem_O (p : PlF D) (k : ℕ) :
    (-1 : (D.s.atP p).Fp) ^ k ∈ (haveI := (D.s.atP p).lf; 𝒪[(D.s.atP p).Fp]) := by
  haveI := (D.s.atP p).lf
  exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) k

set_option maxHeartbeats 4000000 in

theorem locReal_typed (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (p : PlF D) (hMp : (M p).split ≠ none) :
    LocRealAt M δ u u' p := by
  intro w O hO
  obtain ⟨Y, -, ⟨w₀, -, ⟨ξ, η⟩, hYeq⟩, rfl⟩ := hO
  haveI := (D.s.atP p).lf
  have hAg := (hA p).2.2.2.2.2
  rcases hM' : (M p).split with _ | g
  · exact absurd hM' hMp
  rcases hR : (D.s.atP p).split with _ | sg
  · simp only [hM', hR] at hAg
  simp only [hM', hR] at hAg
  obtain ⟨hge, hgq⟩ := hAg
  set Zd : LocDat D := ⟨δ, M, hA⟩
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  set S := Sg (D.s.atP p).Fp D.R.rS with hS
  set s : Fin (D.R.rS + 1) → (D.s.atP p).Fp := fun a => (-1) ^ (D.R.rS - a.val) with hsdef
  have hSd : S = Matrix.diagonal s := rfl
  have hs : ∀ a, s a * s a = 1 := fun a => sgn_sq' D.R.rS a
  have hSS : S * S = 1 := sg_sq _
  set cfv := cf Zd p with hcfv
  set cfiv := cfi Zd p with hcfiv
  have hcc : ∀ a, cfv a * cfiv a = 1 := cf_cfi Zd p
  have hcc' : ∀ a, cfiv a * cfv a = 1 := cfi_cf Zd p
  have hdd : Matrix.diagonal cfv * Matrix.diagonal cfiv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp [hcc]
  have hdd' : Matrix.diagonal cfiv * Matrix.diagonal cfv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp [hcc']
  have conj1 : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp,
      Matrix.diagonal cfv * (Matrix.diagonal cfiv * X * Matrix.diagonal cfv) * Matrix.diagonal cfiv = X := by
    intro X
    rw [show Matrix.diagonal cfv * (Matrix.diagonal cfiv * X * Matrix.diagonal cfv) * Matrix.diagonal cfiv =
      (Matrix.diagonal cfv * Matrix.diagonal cfiv) * X * (Matrix.diagonal cfv * Matrix.diagonal cfiv) by
        simp only [Matrix.mul_assoc], hdd, Matrix.one_mul, Matrix.mul_one]
  have conj2 : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp,
      Matrix.diagonal cfiv * (Matrix.diagonal cfv * X * Matrix.diagonal cfiv) * Matrix.diagonal cfv = X := by
    intro X
    rw [show Matrix.diagonal cfiv * (Matrix.diagonal cfv * X * Matrix.diagonal cfiv) * Matrix.diagonal cfv =
      (Matrix.diagonal cfiv * Matrix.diagonal cfv) * X * (Matrix.diagonal cfiv * Matrix.diagonal cfv) by
        simp only [Matrix.mul_assoc], hdd', Matrix.one_mul, Matrix.mul_one]
  have hSt : S.transpose = S := Matrix.diagonal_transpose _
  have sconj : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp, S * (S * X * S) * S = X := by
    intro X
    rw [show S * (S * X * S) * S = (S * S) * X * (S * S) by simp only [Matrix.mul_assoc], hSS, Matrix.one_mul,
      Matrix.mul_one]

  obtain ⟨Gl, Gu, hGl, hGu, hM0⟩ := target_fact Zd p sg hR g hM' hge hgq u u' w
  have hGlu : IsUnit Gl.det := by rw [det_lo' hGl]; exact isUnit_one
  have hGuu : IsUnit Gu.det := by rw [det_up' hGu]; exact isUnit_one
  set Λ₀ := Loc.uLow ξ * Gl⁻¹ with hΛ₀
  set V₀ := Gu⁻¹ * Loc.uUp w₀ η with hV₀
  have hΛ₀lo : IsLo Λ₀ := isLo_mul (isLo_uLow ξ) (isLo_inv hGl)
  have hV₀up : IsUp V₀ := isUp_mul (isUp_inv hGu) (isUp_uUp w₀ η)
  have hY : Y = Λ₀ * (Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu) * V₀ := by
    rw [hYeq, hΛ₀, hV₀]
    rw [show Loc.uLow ξ * Gl⁻¹ * (Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu) * (Gu⁻¹ * Loc.uUp w₀ η) =
      Loc.uLow ξ * (Gl⁻¹ * Gl) * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * (Gu * Gu⁻¹) * Loc.uUp w₀ η by
        simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul Gl hGlu, Matrix.mul_nonsing_inv Gu hGuu, Matrix.mul_one,
      Matrix.mul_one]
  set A1 := Λ₀.map (p1 sg.e) with hA1
  set A2 := Λ₀.map (p2 sg.e) with hA2
  set B1 := V₀.map (p1 sg.e) with hB1
  set B2 := V₀.map (p2 sg.e) with hB2
  have hA1lo : IsLo A1 := isLo_map _ hΛ₀lo
  have hA2lo : IsLo A2 := isLo_map _ hΛ₀lo
  have hB1up : IsUp B1 := isUp_map _ hV₀up
  have hB2up : IsUp B2 := isUp_map _ hV₀up
  have hΛ₀glue : Λ₀ = glue sg.e A1 A2 := mat_eq sg.e (by rw [glue_map_fst]) (by rw [glue_map_snd])
  have hV₀glue : V₀ = glue sg.e B1 B2 := mat_eq sg.e (by rw [glue_map_fst]) (by rw [glue_map_snd])

  set Lp := glue sg.e (Matrix.diagonal cfiv * A1 * Matrix.diagonal cfv)
    (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S).transpose with hLp
  set Up := glue sg.e (Matrix.diagonal cfv * B1 * Matrix.diagonal cfiv)
    (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S).transpose with hUp
  have hLplo : IsLo Lp := isLo_glue sg.e (isLo_conj hA1lo cfiv cfv hcc')
    (isLo_transpose (isUp_sconj s cfv cfiv hSd hs hcc hB2up))
  have hUpup : IsUp Up := isUp_glue sg.e (isUp_conj hB1up cfv cfiv hcc)
    (isUp_transpose (isLo_sconj s cfiv cfv hSd hs hcc' hA2lo))

  obtain ⟨c', hc'0, hc'⟩ := clear_Fp p
    (ι := (Fin 2 × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ⊕
      (Fin 2 × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (Sum.elim (fun t => cfv t.2.1 * cfiv t.2.2.1 * (if t.1 = 0 then A1⁻¹ else A2⁻¹) t.2.2.1 t.2.2.2)
      (fun t => (if t.1 = 0 then B1⁻¹ else B2⁻¹) t.2.1 t.2.2.1 * cfiv t.2.2.1 * cfv t.2.2.2))
  haveI := (D.s.atP p).ellPrime
  set ℓ : 𝓞 D.host.F := ((Loc.resChar p : ℕ) : 𝓞 D.host.F) with hℓ
  have hℓ0 : ℓ ≠ 0 := by
    rw [hℓ, Ne, Nat.cast_eq_zero]; exact (Fact.out : (Loc.resChar p).Prime).ne_zero
  have hℓq : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F ℓ) = (sg.q : (D.s.atP p).Fp) := by
    rw [hℓ, map_natCast, map_natCast, sg.q_eq]
  refine ⟨Lp, Up, ℓ * c', mul_ne_zero hℓ0 hc'0, hLplo, hUpup, ?_⟩
  intro L B hL hB hLc hBc
  choose oL hoL hLeq using hLc
  choose oB hoB hBeq using hBc
  set a' := (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c') with ha'
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hq
  have ha : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F (ℓ * c')) = q * a' := by
    rw [map_mul, map_mul, hℓq]
  simp only [ha] at hLeq hBeq
  have hOc : ∀ x ∈ (D.s.atP p).O, p1 sg.e x ∈ 𝒪[(D.s.atP p).Fp] ∧ p2 sg.e x ∈ 𝒪[(D.s.atP p).Fp] := by
    intro x hx
    have hO : (M p).L.O = (D.s.atP p).O := (hA p).2.2.2.1
    rw [← hO] at hx
    have h1 := IntegralGeneration.fst_mem (g := g) hx
    have h2 := IntegralGeneration.snd_mem (g := g) hx
    rw [hge] at h1 h2
    exact ⟨h1, h2⟩
  set oL1 := (Matrix.of oL).map (p1 sg.e) with hoL1
  set oL2 := (Matrix.of oL).map (p2 sg.e) with hoL2
  set oB1 := (Matrix.of oB).map (p1 sg.e) with hoB1
  set oB2 := (Matrix.of oB).map (p2 sg.e) with hoB2
  have hcomp : ∀ (X : PairVal.MatR D) (Xp : MatP D p) (o : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) → (D.s.atP p).Ep),
      (∀ i j, (D.s.atP p).ιE (X i j) - Xp i j =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (q * a') * o i j) →
      X.map φ1 = Xp.map (p1 sg.e) + (q * a') • (Matrix.of o).map (p1 sg.e) ∧
      X.map φ2 = Xp.map (p2 sg.e) + (q * a') • (Matrix.of o).map (p2 sg.e) := by
    intro X Xp o h
    refine ⟨?_, ?_⟩
    · ext i j
      have h' := congrArg (p1 sg.e) (h i j)
      rw [map_sub, map_mul, fst_proj_algebraMap] at h'
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hφ1,
        RingHom.comp_apply]
      rw [← h']; ring
    · ext i j
      have h' := congrArg (p2 sg.e) (h i j)
      rw [map_sub, map_mul, snd_proj_algebraMap] at h'
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hφ2,
        RingHom.comp_apply]
      rw [← h']; ring
  obtain ⟨hL1, hL2⟩ := hcomp L Lp oL hLeq
  obtain ⟨hB1', hB2'⟩ := hcomp B Up oB hBeq
  have sS : ∀ X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp,
      S * (S * X * S) * S = X := sconj
  have hΛ1 : Matrix.diagonal cfv * L.map φ1 * Matrix.diagonal cfiv =
      A1 + (q * a') • (Matrix.diagonal cfv * oL1 * Matrix.diagonal cfiv) := by
    rw [hL1, hLp, glue_map_fst, Matrix.mul_add, Matrix.add_mul, conj1, Matrix.mul_smul, Matrix.smul_mul]
  have hV1 : Matrix.diagonal cfiv * B.map φ1 * Matrix.diagonal cfv =
      B1 + (q * a') • (Matrix.diagonal cfiv * oB1 * Matrix.diagonal cfv) := by
    rw [hB1', hUp, glue_map_fst, Matrix.mul_add, Matrix.add_mul, conj2, Matrix.mul_smul, Matrix.smul_mul]
  have hΛ2 : Matrix.diagonal cfv * (S * (B.map φ2).transpose * S) * Matrix.diagonal cfiv =
      A2 + (q * a') • (Matrix.diagonal cfv * (S * oB2.transpose * S) * Matrix.diagonal cfiv) := by
    rw [hB2', hUp, glue_map_snd, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [show S * (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S) * S =
      Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv by
        rw [show S * (S * Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv * S) * S =
          (S * S) * (Matrix.diagonal cfiv * A2 * Matrix.diagonal cfv) * (S * S) by simp only [Matrix.mul_assoc],
          hSS, Matrix.one_mul, Matrix.mul_one], conj1]
  have hV2 : Matrix.diagonal cfiv * (S * (L.map φ2).transpose * S) * Matrix.diagonal cfv =
      B2 + (q * a') • (Matrix.diagonal cfiv * (S * oL2.transpose * S) * Matrix.diagonal cfv) := by
    rw [hL2, hLp, glue_map_snd, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [show S * (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S) * S =
      Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv by
        rw [show S * (S * Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv * S) * S =
          (S * S) * (Matrix.diagonal cfv * B2 * Matrix.diagonal cfiv) * (S * S) by simp only [Matrix.mul_assoc],
          hSS, Matrix.one_mul, Matrix.mul_one], conj2]
  have hA1u : IsUnit A1.det := by rw [det_lo' hA1lo]; exact isUnit_one
  have hA2u : IsUnit A2.det := by rw [det_lo' hA2lo]; exact isUnit_one
  have hB1u : IsUnit B1.det := by rw [det_up' hB1up]; exact isUnit_one
  have hB2u : IsUnit B2.det := by rw [det_up' hB2up]; exact isUnit_one
  set Δ1 := Matrix.diagonal cfv * oL1 * Matrix.diagonal cfiv with hΔ1
  set Δ2 := Matrix.diagonal cfv * (S * oB2.transpose * S) * Matrix.diagonal cfiv with hΔ2
  set E1 := Matrix.diagonal cfiv * oB1 * Matrix.diagonal cfv with hE1
  set E2 := Matrix.diagonal cfiv * (S * oL2.transpose * S) * Matrix.diagonal cfv with hE2
  set lam := glue sg.e ((A1 + (q * a') • Δ1) * A1⁻¹) ((A2 + (q * a') • Δ2) * A2⁻¹) with hlam
  set mu := glue sg.e (B1⁻¹ * (B1 + (q * a') • E1)) (B2⁻¹ * (B2 + (q * a') • E2)) with hmu
  have hlamL : (glue sg.e (A1 + (q * a') • Δ1) (A2 + (q * a') • Δ2) : MatP D p) = lam * Λ₀ := by
    refine mat_eq sg.e ?_ ?_
    · rw [Matrix.map_mul, hlam, glue_map_fst, glue_map_fst]
      show A1 + (q * a') • Δ1 = (A1 + (q * a') • Δ1) * A1⁻¹ * A1
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A1 hA1u, Matrix.mul_one]
    · rw [Matrix.map_mul, hlam, glue_map_snd, glue_map_snd]
      show A2 + (q * a') • Δ2 = (A2 + (q * a') • Δ2) * A2⁻¹ * A2
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A2 hA2u, Matrix.mul_one]
  have hVmu : (glue sg.e (B1 + (q * a') • E1) (B2 + (q * a') • E2) : MatP D p) = V₀ * mu := by
    refine mat_eq sg.e ?_ ?_
    · rw [Matrix.map_mul, hmu, glue_map_fst, glue_map_fst]
      show B1 + (q * a') • E1 = B1 * (B1⁻¹ * (B1 + (q * a') • E1))
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv B1 hB1u, Matrix.one_mul]
    · rw [Matrix.map_mul, hmu, glue_map_snd, glue_map_snd]
      show B2 + (q * a') • E2 = B2 * (B2⁻¹ * (B2 + (q * a') • E2))
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv B2 hB2u, Matrix.one_mul]
  have h1 : CntLocal.ZZP (M := M) δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) * LsDatumB.sgnP p =
      lam * Y * mu := by
    have hZ := zz_fact Zd p sg hR g hM' hge hgq u u' w hL hB
    rw [hM0, hΛ1, hΛ2, hV1, hV2, hlamL, hVmu] at hZ
    rw [hZ, hY]
    simp only [Matrix.mul_assoc]

  have hqO : q ∈ 𝒪[(D.s.atP p).Fp] := sg.q.2
  have hR_of : ∀ x : (D.s.atP p).Ep, ∀ t1 t2 : (D.s.atP p).Fp, t1 ∈ 𝒪[(D.s.atP p).Fp] → t2 ∈ 𝒪[(D.s.atP p).Fp] →
      ∀ d : (D.s.atP p).Fp, d ∈ 𝒪[(D.s.atP p).Fp] → sg.e x = (d + q * t1, d + q * t2) → x ∈ (M p).R := by
    intro x t1 t2 ht1 ht2 d hd hx
    rw [IntegralGeneration.mem_R_of_split hM' x, hge, hx, hgq]
    refine ⟨Subring.add_mem _ hd (Subring.mul_mem _ hqO ht1), Subring.add_mem _ hd (Subring.mul_mem _ hqO ht2),
      t1 - t2, Subring.sub_mem _ ht1 ht2, by ring⟩
  have hδO : ∀ i j : Fin (D.R.rS + 1), (if i = j then (1 : (D.s.atP p).Fp) else 0) ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j; split_ifs; exact Subring.one_mem _; exact Subring.zero_mem _
  have hoL1 : ∀ i j, oL1 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoL i j)).1
  have hoL2 : ∀ i j, oL2 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoL i j)).2
  have hoB1 : ∀ i j, oB1 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoB i j)).1
  have hoB2 : ∀ i j, oB2 i j ∈ 𝒪[(D.s.atP p).Fp] := fun i j => (hOc _ (hoB i j)).2
  have hsO : ∀ a, s a ∈ 𝒪[(D.s.atP p).Fp] := fun a => sgn_mem_O p _
  have hSe : ∀ (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Fp) (i k : Fin (D.R.rS + 1)),
      (S * X.transpose * S) i k = s i * X k i * s k := by
    intro X i k
    rw [hSd, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have hT1 : ∀ i j, a' * (Δ1 * A1⁻¹) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hΔ1, conj_mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inl (0, i, k, j))
    simp only [Sum.elim_inl, if_true] at hz
    rw [show a' * (cfv i * oL1 i k * cfiv k * A1⁻¹ k j) = oL1 i k * (a' * (cfv i * cfiv k * A1⁻¹ k j)) by ring]
    exact Subring.mul_mem _ (hoL1 i k) hz
  have hT2 : ∀ i j, a' * (Δ2 * A2⁻¹) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hΔ2, conj_mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inl (1, i, k, j))
    simp only [Sum.elim_inl, Fin.one_eq_zero_iff, one_ne_zero, if_false] at hz
    rw [hSe, show a' * (cfv i * (s i * oB2 k i * s k) * cfiv k * A2⁻¹ k j) =
      (s i * oB2 k i * s k) * (a' * (cfv i * cfiv k * A2⁻¹ k j)) by ring]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (hsO i) (hoB2 k i)) (hsO k)) hz
  have hU1 : ∀ i j, a' * (B1⁻¹ * E1) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hE1, mul_conj_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inr (0, i, k, j))
    simp only [Sum.elim_inr, if_true] at hz
    rw [show a' * (B1⁻¹ i k * (cfiv k * oB1 k j * cfv j)) = oB1 k j * (a' * (B1⁻¹ i k * cfiv k * cfv j)) by ring]
    exact Subring.mul_mem _ (hoB1 k j) hz
  have hU2 : ∀ i j, a' * (B2⁻¹ * E2) i j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro i j
    rw [hE2, mul_conj_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hc' (Sum.inr (1, i, k, j))
    simp only [Sum.elim_inr, Fin.one_eq_zero_iff, one_ne_zero, if_false] at hz
    rw [hSe, show a' * (B2⁻¹ i k * (cfiv k * (s k * oL2 j k * s j) * cfv j)) =
      (s k * oL2 j k * s j) * (a' * (B2⁻¹ i k * cfiv k * cfv j)) by ring]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (hsO k) (hoL2 j k)) (hsO j)) hz
  have hlo1 : IsLo (A1 + (q * a') • Δ1) := by
    rw [← hΛ1]; exact isLo_conj (isLo_map φ1 hL) _ _ hcc
  have hlo2 : IsLo (A2 + (q * a') • Δ2) := by
    rw [← hΛ2]
    exact isLo_conj (isLo_conj (isLo_transpose (isUp_map φ2 hB)) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc
  have hup1 : IsUp (B1 + (q * a') • E1) := by
    rw [← hV1]; exact isUp_conj (isUp_map φ1 hB) _ _ hcc'
  have hup2 : IsUp (B2 + (q * a') • E2) := by
    rw [← hV2]
    exact isUp_conj (isUp_conj (isUp_transpose (isLo_map φ2 hL)) _ _ (fun a => sgn_sq' D.R.rS a)) _ _ hcc'
  have hlamI : TieN.IntLow (M p) lam := by
    have hlo : IsLo lam := isLo_glue sg.e (isLo_mul hlo1 (isLo_inv hA1lo)) (isLo_mul hlo2 (isLo_inv hA2lo))
    refine ⟨hlo.1, hlo.2, fun i j => ?_⟩
    refine hR_of (lam i j) (a' * (Δ1 * A1⁻¹) i j) (a' * (Δ2 * A2⁻¹) i j) (hT1 i j) (hT2 i j) _ (hδO i j) ?_
    rw [hlam, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, lam_form hA1lo, lam_form hA2lo, one_smul_apply,
      one_smul_apply]
    ring_nf
  have hmuI : TieN.IntUp (M p) mu := by
    have hup : IsUp mu := isUp_glue sg.e (isUp_mul (isUp_inv hB1up) hup1) (isUp_mul (isUp_inv hB2up) hup2)
    refine ⟨hup.1, fun i j hij => hup.2 j i hij, fun i j => ?_⟩
    refine hR_of (mu i j) (a' * (B1⁻¹ * E1) i j) (a' * (B2⁻¹ * E2) i j) (hU1 i j) (hU2 i j) _ (hδO i j) ?_
    rw [hmu, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply, mu_form hB1up, mu_form hB2up, one_smul_apply,
      one_smul_apply]
    ring_nf
  have hlamu : IsUnit lam.det := by rw [det_lo' ⟨hlamI.1, hlamI.2.1⟩]; exact isUnit_one
  have hmuu : IsUnit mu.det := by rw [det_up' ⟨hmuI.1, fun a b hab => hmuI.2.1 b a hab⟩]; exact isUnit_one
  have h2 : Y = lam⁻¹ * (lam * Y * mu) * mu⁻¹ := by
    rw [show lam⁻¹ * (lam * Y * mu) * mu⁻¹ = (lam⁻¹ * lam) * Y * (mu * mu⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul lam hlamu, Matrix.mul_nonsing_inv mu hmuu, Matrix.one_mul, Matrix.mul_one]
  unfold tupZ
  exact kkOrb_eq_of hlamI hmuI (intLow_inv hlamI) (intUp_inv hmuI) h1 (by rw [h1]; exact h2)

theorem exist_holds (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) : Exist M δ u u' :=
  exist_of u u' hA (fun p hp => locReal_typed hA u u' p hp)

end Typed

end Formalism.L2.SG.Pf.PCountEx
end
end

section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG3

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem lmat_up {l ρ : Formalism.L2.SG.LsDatumB.MatP D p} (hl0 : ∀ a b, a < b → l a b = 0) (hl1 : ∀ a, l a a = 1)
    (hρ0 : ∀ a b, b < a → ρ a b = 0) (hρ1 : ∀ a, ρ a a = 1) :
    (∀ a b, b < a → lmat Z p g ρ l a b = 0) ∧ ∀ a, lmat Z p g ρ l a a = 1 := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · simp only [lmat, Matrix.of_apply, hρ0 a b h, hl0 b a h, map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [show ((0 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) = 0 from rfl, map_zero]
  · simp only [lmat, Matrix.of_apply, hl1 a, hρ1 a, map_one, Prod.fst_one, Prod.snd_one]
    rw [show ((1 : (D.s.atP p).Fp), (1 : (D.s.atP p).Fp)) = 1 from rfl, map_one]

theorem modeG (hs : (Z.M p).split = some g) (u u' : D.what₂.Word)
    (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hNU : ∀ a b, b < a → N a b = 0) (hNd : ∀ a, N a a = 1) (hMU : ∀ a b, b < a → M a b = 0)
    (hMd : ∀ a, M a a = 1)
    (hNb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c)
    (hMb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * M c b ∈ aaF D c) (hrel : Nᴴ * Z₂ = Z₁ * M)
    (hcong : Cq Z p g (locU Z p N * locU Z p M - 1)) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Z.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Z.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * Formalism.L2.SG.LsDatumB.sgnP p) * ρ := by
  obtain ⟨hN1, hN0, hNO⟩ := locU_int Z p N hNU hNd hNb
  obtain ⟨hM1, hM0, hMO⟩ := locU_int Z p M hMU hMd hMb
  set Nl := locU Z p N with hNl
  set Ml := locU Z p M with hMl
  set K := (Nl.map (Z.M p).L.cj)ᵀ with hKdef
  have hK0 : ∀ a b, a < b → K a b = 0 := fun a b h => by
    simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]
  have hK1 : ∀ a, K a a = 1 := fun a => by
    simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]
  have hKO : IntM Z p K := fun i j => PI.LocCntLat.GC.cj_mem_O _ (hNO j i)
  have hKdet : K.det = 1 := det_lower p hK0 hK1
  have hKu : IsUnit K.det := by rw [hKdet]; exact isUnit_one
  have hNdet : Nl.det = 1 := det_upper p hN0 hN1
  have hNu : IsUnit Nl.det := by rw [hNdet]; exact isUnit_one
  have hl0O : IntM Z p K⁻¹ := Formalism.L2.SG.Pf.LocOrbCut.inv_int (Z.M p).L.O K hKO hKdet
  have hNiO : IntM Z p Nl⁻¹ := Formalism.L2.SG.Pf.LocOrbCut.inv_int (Z.M p).L.O Nl hNO hNdet
  have hl0low : (∀ a b, a < b → K⁻¹ a b = 0) ∧ ∀ a, K⁻¹ a a = 1 := by
    have h := Formalism.L2.SG.TermLoc.inv_unitri Kᵀ (fun a b h => by rw [Matrix.transpose_apply]; exact hK0 b a h)
      (fun a => by rw [Matrix.transpose_apply]; exact hK1 a)
    rw [← Matrix.transpose_nonsing_inv] at h
    exact ⟨fun a b hab => by have := h.1 b a hab; rwa [Matrix.transpose_apply] at this,
      fun a => by have := h.2 a; rwa [Matrix.transpose_apply] at this⟩
  have hK := key_rel Z p N M Z₁ Z₂ hrel
  have hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * Ml := by
    rw [Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKu, Matrix.one_mul]

  set Cm : Formalism.L2.SG.LsDatumB.MatP D p := Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
      g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
        (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)) else 0 with hCm
  have hZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p X =
      emap Z p g (Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X) - Cm := by
    intro X
    ext a b
    simp only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, emap, hCm, Matrix.sub_apply,
      Matrix.of_apply]
  obtain ⟨hL0, hL1⟩ := lmat_low Z p g hl0low.1 hl0low.2 hM0 hM1
  obtain ⟨hR0, hR1⟩ := lmat_up Z p g hl0low.1 hl0low.2 hM0 hM1
  have hcorner := corner_fix p hL0 hL1 hR0 hR1 (C := Cm) (fun a b h => by
    simp only [hCm, Matrix.of_apply]; rw [if_neg h])
  have hmain : Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ =
      lmat Z p g K⁻¹ Ml * Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * lmat Z p g Ml K⁻¹ := by
    rw [hZZ, hZZ, hY, emap_mul, Matrix.mul_sub, Matrix.sub_mul, hcorner]

  have hKc : K.map (Z.M p).L.cj = Nlᵀ := by
    ext i j
    simp [hKdef, (Z.M p).L.cj_cj]
  have hA : Cq Z p g (Ml - ((K⁻¹).map (Z.M p).L.cj)ᵀ) := by
    have e1 : ((K⁻¹).map (Z.M p).L.cj)ᵀ = Nl⁻¹ := by
      rw [map_cj_inv Z p K hKu, hKc, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    have e2 : Ml - Nl⁻¹ = Nl⁻¹ * (Nl * Ml - 1) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Nl hNu, Matrix.one_mul, Matrix.mul_one]
    rw [e1, e2]
    exact cq_mul_left Z p g hNiO hcong
  have hB : Cq Z p g (K⁻¹ - (Ml.map (Z.M p).L.cj)ᵀ) := by
    have e1 : Ml * Nl - 1 = Nl⁻¹ * (Nl * Ml - 1) * Nl := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Nl hNu, Matrix.one_mul,
        Matrix.mul_one, Matrix.nonsing_inv_mul Nl hNu]
    have h1 : Cq Z p g (Ml * Nl - 1) := by
      rw [e1]; exact cq_mul_right Z p g (cq_mul_left Z p g hNiO hcong) hNO
    have e2 : ((Ml * Nl - 1).map (Z.M p).L.cj)ᵀ = K * (Ml.map (Z.M p).L.cj)ᵀ - 1 := by
      have m1 : (Ml * Nl - 1).map (Z.M p).L.cj = (Ml * Nl).map (Z.M p).L.cj - 1 := by
        ext i j
        rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
        congr 1
        simp only [Matrix.one_apply]
        split_ifs <;> simp
      rw [m1, map_cj_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hKdef]
    have e3 : K⁻¹ - (Ml.map (Z.M p).L.cj)ᵀ = -(K⁻¹ * ((Ml * Nl - 1).map (Z.M p).L.cj)ᵀ) := by
      rw [e2, Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKu, Matrix.one_mul, Matrix.mul_one,
        neg_sub]
    rw [e3]
    exact cq_neg Z p g (cq_mul_left Z p g hl0O (cq_transpose Z p g (cq_map_cj Z p g h1)))
  have hLint : Formalism.MainNotions.S.TieN.IntLow (Z.M p) (lmat Z p g K⁻¹ Ml) := by
    refine ⟨hL1, hL0, fun a b => ?_⟩
    obtain ⟨o, ho, he⟩ := hB a b
    exact lmat_mem_R Z p g hs (hl0O a b) (hMO b a) ⟨o, ho, by
      rw [← he]; simp [Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply]⟩
  have hRint : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (lmat Z p g Ml K⁻¹) := by
    refine ⟨hR1, hR0, fun a b => ?_⟩
    obtain ⟨o, ho, he⟩ := hA a b
    exact lmat_mem_R Z p g hs (hMO a b) (hl0O b a) ⟨o, ho, by
      rw [← he]; simp [Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply]⟩
  refine ⟨lmat Z p g K⁻¹ Ml, Formalism.L2.SG.LsDatumB.sgnP p * lmat Z p g Ml K⁻¹ * Formalism.L2.SG.LsDatumB.sgnP p,
    hLint, sgn_conj_intUp Z p hRint, ?_⟩
  rw [hmain]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]

end ModeG3

end Formalism.L2.SG.Pf.FibQ
end
end

section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LocU

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem locU_mul (A B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A * locU Z p B = locU Z p (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, locU_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc _ = Ring.inverse (frFac Z.δ p i) * (D.s.atP p).ιE (A i k) *
        (frFac Z.δ p k * Ring.inverse (frFac Z.δ p k)) * (D.s.atP p).ιE (B k j) * frFac Z.δ p j := by ring
    _ = _ := by rw [frFac_mul_inv, mul_one]; ring

theorem locU_sub_one (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    locU Z p A - 1 = locU Z p (A - 1) := by
  ext i j
  simp only [Matrix.sub_apply, locU_apply, map_sub, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [map_one, mul_sub, sub_mul, mul_one, frFac_inv_mul]
  · simp only [map_zero, sub_zero]

end LocU

end Formalism.L2.SG.Pf.FibQ
end
end

section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneDir

variable {D : D7} (Zd : LocDat D)

theorem typed_split (p : PlF D) {g : Formalism.MainNotions.S.Loc.SplitG (Zd.M p).L} (hs : (Zd.M p).split = some g) :
    ∃ sg, (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
  have h := (Zd.agree p).2.2.2.2.2
  rw [hs] at h
  cases hsg : (D.s.atP p).split with
  | none => rw [hsg] at h; exact h.elim
  | some sg => rw [hsg] at h; exact ⟨sg, rfl, h.1, h.2⟩

theorem gS_mem_of_split (p : PlF D) {sg} (hsg : (D.s.atP p).split = some sg) :
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := fun P hP =>
  (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P hP).2 (by rw [← D.s_split p, hsg]; rfl)

end OneDir

end Formalism.L2.SG.Pf.FibQ
end
end

section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneDir2

variable {D : D7} (Zd : LocDat D)

theorem nm_last (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (VS D) D.R.rS T)
    (G₁ : LFlag (VS D) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (b : Fin (D.R.rS + 1)) :
    (fmat D G n * fmat D G₁ m - 1) (Fin.last D.R.rS) b = 0 := by
  have hNU := (stepExp D Λ G n hn).1
  have hMU := (stepExp D Λ G₁ m hm).1
  rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.last D.R.rS)]
  · rw [(hNU _ _).2 rfl, one_mul, Matrix.one_apply]
    by_cases hb : Fin.last D.R.rS = b
    · rw [(hMU _ _).2 hb, if_pos hb, sub_self]
    · have hlt : b < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last b) (Ne.symm hb)
      rw [(hMU _ _).1 hlt, if_neg hb, sub_self]
  · intro c _ hc
    have hlt : c < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last c) hc
    rw [(hNU _ _).1 hlt, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem one_dir {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hRL : IsRowLat D F0 Λ)
    (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hP₁ : Formalism.L2.SG.TermDef.PD D Λ (lf D F0) u' F₁) (hA₁ : AdmWit Λ (gS D) (lf D F0) F₁ 1)
    (hA₂ : AdmWit Λ (gS D) (lf D F0) F₂ 1) (hdc : Formalism.L2.SG.TermDef.DCRel Λ (lf D F0) F₁ F₂) (p : PlF D) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Zd.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Zd.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatL (lf D F0) F₂) * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatL (lf D F0) F₁) * Formalism.L2.SG.LsDatumB.sgnP p) *
          ρ := by
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hdc
  have hEn := stepExp D Λ (lf D F0) n hn
  have hEm := stepExp D Λ F₁ m hm
  have hrel := stepGram D (lf D F0) F₁ F₂ n m (fmat D (lf D F0) n) (fmat D F₁ m) hn.1.1 hEn.2 hEm.2 hfr
  have hXS : XLam Λ (lf D F0) = XS D (lf D F0).fl := hRL.2.2
  have hz : (lf D F0).fl.z ∈ Λ := hRL.2.1.2.2.1.1
  have hNb := entry_mem D Λ (lf D F0) n hn hXS hz
  have hMb := entry_mem D Λ F₁ m hm hP₁.2.2.2 hP₁.1.1
  have hNU : ∀ a b, b < a → fmat D (lf D F0) n a b = 0 := fun a b h => (hEn.1 a b).1 h
  have hNd : ∀ a, fmat D (lf D F0) n a a = 1 := fun a => (hEn.1 a a).2 rfl
  have hMU : ∀ a b, b < a → fmat D F₁ m a b = 0 := fun a b h => (hEm.1 a b).1 h
  have hMd : ∀ a, fmat D F₁ m a a = 1 := fun a => (hEm.1 a a).2 rfl
  cases hs : (Zd.M p).split with
  | none => exact modeL Zd p hs u u' _ _ _ _ hNU hNd hMU hMd hNb hMb hrel
  | some g =>
    refine modeG Zd p g hs u u' _ _ _ _ hNU hNd hMU hMd hNb hMb hrel ?_
    obtain ⟨sg, hsg, -, hq⟩ := typed_split Zd p hs
    have hgP := gS_mem_of_split p hsg
    have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by
      have : gS D ≠ 0 := by
        unfold Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact_mod_cast this
    have hφ := fun a => Formalism.L2.SG.Pf.BBTie.bt_typed_frFac Zd (Formalism.L2.SG.Pf.locEqC_holds D Zd)
      (Formalism.L2.SG.Pf.locDiffC_holds D Zd) p F0 Λ hRL.2.1.1.fg hRL.2.2 hRL.2.1.2.2.2 hgP a
    have hκ := (Formalism.L2.SG.Pf.BBTie.bt_kappa Zd p sg hsg).1
    have hq0 : (sg.q : (D.s.atP p).Fp) ≠ 0 := by
      intro h
      exact sg.q_irr.ne_zero (Subtype.ext h)
    have hOO : (Zd.M p).L.O = (D.s.atP p).O := (Zd.agree p).2.2.2.1
    rw [locU_mul, locU_sub_one]
    intro i j
    rw [locU_apply]
    obtain ⟨w, hwO, hw⟩ := (hφ i).2
    have hinv : Ring.inverse (frFac Zd.δ p i) = w := by
      calc Ring.inverse (frFac Zd.δ p i) = (w * frFac Zd.δ p i) * Ring.inverse (frFac Zd.δ p i) := by
            rw [hw, one_mul]
        _ = w := by rw [mul_assoc, frFac_mul_inv, mul_one]
    induction i using Fin.lastCases with
    | last =>
      rw [nm_last Λ (lf D F0) F₁ n m hn hm j, map_zero, mul_zero, zero_mul]
      exact ⟨0, Subring.zero_mem _, by rw [mul_zero]⟩
    | cast d =>
      set x := (fmat D (lf D F0) n * fmat D F₁ m - 1) d.castSucc j with hxdef
      have hint : (D.s.atP p).ιE (x / (gS D : D.host.E)) ∈ (Zd.M p).L.O := by
        rw [hOO]
        exact iota_mem_O p _ (fun P hP => cong_at D Λ (lf D F0) F₁ F₂ n m hn hm hfr hRL.2.1.2.2.2 hP₁.2.2.1
          hA₁ hA₂ hP₁.1.1 P (hgP P hP) hg d j)
      have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) *
          ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
            (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) * (D.s.atP p).ιE (x / (gS D : D.host.E))) := by
        rw [← mul_assoc, ← mul_assoc, ← map_mul (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), mul_inv_cancel₀ hq0,
          map_one, one_mul, ← map_mul, mul_div_cancel₀ x hg]
      refine ⟨w * ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
          (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) * (D.s.atP p).ιE (x / (gS D : D.host.E))) * frFac Zd.δ p j,
        Subring.mul_mem _ (Subring.mul_mem _ hwO (Subring.mul_mem _ hκ hint)) (hφ j).1, ?_⟩
      rw [hinv, hx, hq]
      ring

end OneDir2

end Formalism.L2.SG.Pf.FibQ
end
end

section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tupFun_holds {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.Pf.FibPart.TupFun M δ u u' F0 what₂ := by
  intro hpre γ w Z hel hZ hrep
  obtain ⟨hAg, -, -, hN, hR, hE⟩ := hpre
  let Zd : LocDat D := ⟨δ, M, hAg⟩
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
      Formalism.L2.SG.PairVal.MatR D × Formalism.L2.SG.PairVal.MatR D,
      Formalism.L2.SG.PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    obtain ⟨y, hy⟩ := hN γ w hel.2 (hE γ w hel) hel.1.1
    exact ⟨(w, y), hy⟩
  have hzT : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dif_pos hex]
  obtain ⟨⟨hPD₁, hmk₁⟩, hA₁, -⟩ := hex.choose_spec
  obtain ⟨F₂, hF₂, hPD₂, hmk₂⟩ := hrep
  have hRL : IsRowLat D F0 γ.lam := hR.1 γ.lam γ.mem
  have hdc : Formalism.L2.SG.TermDef.DCRel γ.lam (lf D F0) hex.choose.2.1 F₂ :=
    (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (Formalism.L2.SG.TermDef.PD D γ.lam (lf D F0) u') ⟨_, hPD₁⟩
      ⟨F₂, hPD₂⟩).1 (hmk₁.trans hmk₂.symm)
  have hZ2 : ZhatL (lf D F0) F₂ = Z := hF₂.2.2.2.2
  funext p
  obtain ⟨l, ρ, hl, hρ, h1⟩ := one_dir Zd hRL _ F₂ hPD₁ hA₁ hF₂.2.1 hdc p
  obtain ⟨l', ρ', hl', hρ', h2⟩ := one_dir Zd hRL F₂ _ hPD₂ hF₂.2.1 hA₁
    (Formalism.L2.SG.Pf.dcrel_symm γ.lam (lf D F0) hdc) p
  have key := kkOrb_eq_of hl' hρ' hl hρ h2 h1
  show kkOrb M p (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p) =
    kkOrb M p (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z * sgnP p)
  rw [hzT, ← hZ2]
  exact key

end Formalism.L2.SG.Pf.FibQ
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem bOf_unique (a : Formalism.L2.SG.PairVal.GLR D) (b : Formalism.L2.SG.PairVal.MatR D)
    (hW : (a : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b = ptMat w) : VolPinAsm.bOf w a = b := by
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  unfold VolPinAsm.bOf
  have h1 : (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * (a : Formalism.L2.SG.PairVal.MatR D) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (ptMat w)⁻¹ * (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * ptMat w
      = (ptMat w)⁻¹ * (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) *
          ((a : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b) := by rw [hW]
    _ = (ptMat w)⁻¹ * ((((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * (a : Formalism.L2.SG.PairVal.MatR D)) *
          ptMat w * b := by simp only [Matrix.mul_assoc]
    _ = b := by rw [h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul]

theorem mem_stabInt_glob (hA : ∀ p, Agree δ M p) (g : VolPinAsm.StG w) :
    ((g : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' δ M w) ↔
      ∀ p, πP M δ u u' w (hA p) g ∈ AP M δ u u' w p := by
  have hset : ∀ a : VolPinAsm.StG w, (a : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabIntSet D u u' δ M w ↔
      ∀ p, πP M δ u u' w (hA p) a ∈ AP M δ u u' w p := by
    intro a
    obtain ⟨ha, hb, hW⟩ := bOf_spec w a
    rw [mem_stabIntSet_iff δ M u u' hA w]
    refine ⟨fun h p => ?_, fun hp => ⟨ha, _, hb, hW, hp⟩⟩
    obtain ⟨-, b, -, hW', hp⟩ := h
    have e := bOf_unique w (a : Formalism.L2.SG.PairVal.GLR D) b hW'
    rw [← e] at hp
    exact hp p
  constructor
  · intro hg

    set K : Subgroup (Formalism.L2.SG.PairVal.GLR D) :=
      (Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => AP M δ u u' w p)).map
        (VolPinAsm.StG w).subtype with hK
    have hle : Formalism.L2.SG.PairVal.stabInt D u u' δ M w ≤ K := by
      unfold Formalism.L2.SG.PairVal.stabInt
      rw [Subgroup.closure_le]
      intro a ha
      have haSt : a ∈ VolPinAsm.StG w := by
        obtain ⟨h1, b, hb, hW, -⟩ := ha
        exact ⟨h1, b, hb, hW⟩
      refine ⟨⟨a, haSt⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Formalism.L2.SG.Pf.ProdE.mem_glob]
      exact (hset ⟨a, haSt⟩).1 ha
    obtain ⟨g', hg', e⟩ := hle hg
    have : g' = g := Subtype.ext e
    rw [this, SetLike.mem_coe, Formalism.L2.SG.Pf.ProdE.mem_glob] at hg'
    exact hg'
  · intro hp
    exact Subgroup.subset_closure ((hset g).2 hp)

theorem lOf_conj {p : PlF D} (hA : Agree δ M p) (L U g b : Formalism.L2.SG.PairVal.MatR D) :
    lOf δ M p (L * g * L⁻¹) (U⁻¹ * b * U) = lOf δ M p L U * lOf δ M p g b * lOf δ M p L⁻¹ U⁻¹ := by
  rw [Matrix.mul_assoc L g, lOf_mul δ M hA L U (g * L⁻¹) (U⁻¹ * b), lOf_mul δ M hA g b L⁻¹ U⁻¹, Matrix.mul_assoc]

theorem ρOf_conj {p : PlF D} (hA : Agree δ M p) (L U g b : Formalism.L2.SG.PairVal.MatR D) :
    ρOf δ M p (L * g * L⁻¹) (U⁻¹ * b * U) = ρOf δ M p L⁻¹ U⁻¹ * ρOf δ M p g b * ρOf δ M p L U := by
  rw [Matrix.mul_assoc L g, ρOf_mul δ M hA L U (g * L⁻¹) (U⁻¹ * b), ρOf_mul δ M hA g b L⁻¹ U⁻¹]

theorem mem_CZ_glob (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (Zh : Formalism.L2.SG.PairVal.MatR D) (hZ : ZhatOM Zh = L * ptMat w * U) (g : VolPinAsm.StG w) :
    ((g : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' Zh L) ↔
      ∀ p, πP M δ u u' w (hA p) g ∈ CPL M δ u u' w (hA p) L U hL hU := by
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLdet : IsUnit L.det := by rw [ZsVolGrp.det_lo (fun a => (hL a a).2 rfl) (fun a b h => (hL a b).1 h)]; exact isUnit_one
  rw [ZsVolGrp.mem_CZ M δ u u' Zh L hLdet]
  obtain ⟨ha, hb, hW⟩ := bOf_spec w g
  set gm : Formalism.L2.SG.PairVal.MatR D := ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) with hgm
  set b := VolPinAsm.bOf w (g : Formalism.L2.SG.PairVal.GLR D) with hb'
  have hmemC : ∀ p, πP M δ u u' w (hA p) g ∈ CPL M δ u u' w (hA p) L U hL hU ↔
      Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p (L * gm * L⁻¹) (U⁻¹ * b * U)) ∧
        Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p (L * gm * L⁻¹) (U⁻¹ * b * U)) := by
    intro p
    rw [lOf_conj M δ (hA p), ρOf_conj M δ (hA p)]
    rfl
  simp only [hmemC]
  constructor
  · rintro ⟨a', ha'eq, ha'lo, b', hb'up, hZ', hloc⟩ p
    have ea' : ((a' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = L * gm * L⁻¹ := by
      have h := ha'eq
      rw [← hgm] at h
      rw [h]
      calc ((a' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)
          = (L * L⁻¹) * (a' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) := by rw [hLi.2.2]; simp
        _ = L * (L⁻¹ * (a' : Formalism.L2.SG.PairVal.MatR D) * L) * L⁻¹ := by simp only [Matrix.mul_assoc]
    have eb' : b' = U⁻¹ * b * U := by
      have h1 : gm * ptMat w * (U * b' * U⁻¹) = ptMat w := by
        have := hZ'
        rw [hZ, ea'] at this
        have h2 : L⁻¹ * (L * gm * L⁻¹ * (L * ptMat w * U) * b') * U⁻¹ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := by rw [this]
        calc gm * ptMat w * (U * b' * U⁻¹) = (L⁻¹ * L) * gm * (L⁻¹ * L) * ptMat w * U * b' * U⁻¹ := by
              rw [hLi.2.1]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
          _ = L⁻¹ * (L * gm * L⁻¹ * (L * ptMat w * U) * b') * U⁻¹ := by simp only [Matrix.mul_assoc]
          _ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := h2
          _ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
          _ = ptMat w := by rw [hLi.2.1, hUi.2.2, Matrix.one_mul, Matrix.mul_one]
      have e := bOf_unique w (g : Formalism.L2.SG.PairVal.GLR D) _ h1
      rw [← hb'] at e
      rw [e]
      calc b' = (U⁻¹ * U) * b' * (U⁻¹ * U) := by rw [hUi.2.1]; simp
        _ = U⁻¹ * (U * b' * U⁻¹) * U := by simp only [Matrix.mul_assoc]
    obtain ⟨l, ρ, hl, hρ, hZl⟩ := hloc p
    obtain ⟨el, eρ⟩ := uniq δ M u u' (hA p) _ b' ha'lo hb'up l ρ (fun i => hl.1 i) (fun i => hρ.1 i) hZl
    rw [← ea', ← eb', ← el, ← eρ]
    exact ⟨hl, hρ⟩
  · intro hp
    set a'm := L * gm * L⁻¹ with ha'm
    have ha'lo : IsLoUni a'm := ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hL ha) hLi.1
    have hb'up : IsUpUni (U⁻¹ * b * U) := ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hUi.1 hb) hU
    have hginv : ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * gm = 1 := by
      rw [hgm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hginv' : gm * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = 1 := by
      rw [hgm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    let a' : Formalism.L2.SG.PairVal.GLR D :=
      ⟨a'm, L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹,
        by
          calc a'm * (L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹)
              = L * gm * (L⁻¹ * L) * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹ := by
                simp only [ha'm, Matrix.mul_assoc]
            _ = 1 := by rw [hLi.2.1, Matrix.mul_one, Matrix.mul_assoc L, hginv', Matrix.mul_one, hLi.2.2],
        by
          calc (L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹) * a'm
              = L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * (L⁻¹ * L) * gm * L⁻¹ := by
                simp only [ha'm, Matrix.mul_assoc]
            _ = 1 := by rw [hLi.2.1, Matrix.mul_one, Matrix.mul_assoc L, hginv, Matrix.mul_one, hLi.2.2]⟩
    refine ⟨a', ?_, ha'lo, U⁻¹ * b * U, hb'up, ?_, fun p => ⟨_, _, (hp p).1, (hp p).2,
      move δ M u u' (hA p) a'm (U⁻¹ * b * U) ha'lo hb'up⟩⟩
    · show gm = L⁻¹ * a'm * L
      calc gm = (L⁻¹ * L) * gm * (L⁻¹ * L) := by rw [hLi.2.1]; simp
        _ = L⁻¹ * a'm * L := by simp only [ha'm, Matrix.mul_assoc]
    · show a'm * ZhatOM Zh * (U⁻¹ * b * U) = ZhatOM Zh
      rw [hZ]
      calc a'm * (L * ptMat w * U) * (U⁻¹ * b * U) = L * gm * (L⁻¹ * L) * ptMat w * (U * U⁻¹) * b * U := by
            simp only [ha'm, Matrix.mul_assoc]
        _ = L * (gm * ptMat w * b) * U := by
            rw [hLi.2.1, hUi.2.2, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = L * ptMat w * U := by rw [hW]

theorem idxRatio_self {G : Type} [Group G] (A : Subgroup G) : Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A A = 1 := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio; simp [Subgroup.relIndex_self]

theorem idxRatio_subgroupOf {G : Type} [Group G] (A B K : Subgroup G) (hA : A ≤ K) (hB : B ≤ K) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A.subgroupOf K) (B.subgroupOf K) = Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A B := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [Subgroup.relIndex_subgroupOf hA, Subgroup.relIndex_subgroupOf hB]

theorem cz_le (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (Zh : Formalism.L2.SG.PairVal.MatR D) (hZ : ZhatOM Zh = L * ptMat w * U) :
    Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' Zh L ≤ VolPinAsm.StG w := by
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLdet : IsUnit L.det := by rw [ZsVolGrp.det_lo (fun a => (hL a a).2 rfl) (fun a b h => (hL a b).1 h)]; exact isUnit_one
  intro a ha
  rw [ZsVolGrp.mem_CZ M δ u u' Zh L hLdet] at ha
  obtain ⟨a', ha'eq, ha'lo, b', hb'up, hZ', -⟩ := ha
  refine ⟨?_, U * b' * U⁻¹, ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hU hb'up) hUi.1, ?_⟩
  · rw [ha'eq]; exact ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hLi.1 ha'lo) hL
  · rw [ha'eq]
    rw [hZ] at hZ'
    calc L⁻¹ * (a' : Formalism.L2.SG.PairVal.MatR D) * L * ptMat w * (U * b' * U⁻¹)
        = L⁻¹ * ((a' : Formalism.L2.SG.PairVal.MatR D) * (L * ptMat w * U) * b') * U⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := by rw [hZ']
      _ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hLi.2.1, hUi.2.2, Matrix.one_mul, Matrix.mul_one]

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem prodE_of (hap : ApproxC M δ u u' F0 what₂) (hloc : LocIdxC M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.ZsVolCut.ProdE M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') := by
  intro γ w F' L U hE
  obtain ⟨S, hS, hfin, happrox⟩ := hap γ w F' L U hE
  have hA := hE.1
  have hL : IsLoUni L := hE.2.2.2.2.2.2.2.1
  have hU : IsUpUni U := hE.2.2.2.2.2.2.2.2.1
  have hZ : ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U := hE.2.2.2.2.2.2.2.2.2
  have hset : Formalism.L2.SG.PairVal.stabIntSet D u u' δ M w ⊆ Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w) := by
    intro a ha
    obtain ⟨h1, b, hb, hW, -⟩ := ha
    exact ⟨h1, b, hb, hW⟩
  have hAle : Formalism.L2.SG.PairVal.stabInt D u u' δ M w ≤ VolPinAsm.StG w := fun x hx =>
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.closure_subset_StSet Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed _ _ hset hx
  have hCle := cz_le M δ u u' w L U hL hU _ hZ
  rw [← idxRatio_subgroupOf _ _ _ hAle hCle]
  have e1 : (Formalism.L2.SG.PairVal.stabInt D u u' δ M w).subgroupOf (VolPinAsm.StG w) =
      Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => AP M δ u u' w p) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Formalism.L2.SG.Pf.ProdE.mem_glob]
    exact mem_stabInt_glob M δ u u' w hA g
  have e2 : (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' (ZhatL (lf D F0) F') L).subgroupOf (VolPinAsm.StG w) =
      Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => CPL M δ u u' w (hA p) L U hL hU) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Formalism.L2.SG.Pf.ProdE.mem_glob]
    exact mem_CZ_glob M δ u u' w hA L U hL hU _ hZ g
  rw [e1, e2, Formalism.L2.SG.Pf.ProdE.idxRatio_glob _ _ _ S hS (fun p => (hfin p).1) (fun p => (hfin p).2) happrox]
  have hl := fun p => hloc γ w F' L U hE p
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  · exact Finset.prod_congr rfl fun p _ => hl p
  · intro p hp
    by_contra hpS
    apply hp
    show Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
      (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p) = 1
    rw [← hl p, hS p hpS, idxRatio_self]

end Formalism.L2.SG.Pf.ProdE
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.ProdE

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem prodE_CZ_of_approxC (hap : ApproxC M δ u u' F0 what₂) (hst : Formalism.L2.SG.Pf.ProdEP2Cut.StepsU M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.ZsVolCut.ProdE M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') :=
  prodE_of M δ u u' F0 what₂ hap (Formalism.L2.SG.Pf.ProdEP2Cut.locIdxC_of_count M δ u u' F0 what₂ hst)


end Formalism.L2.SG.Pf.ProdE
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.TupFinal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG

theorem repAtTup_of_stab {D : D7} (Zd : TermLoc.LocDat D) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))
    (hS : Pf.TupGlob.StabApprox Zd u u') : Pf.FibPart.RepAtTup Zd.M Zd.δ u u' F0 what₂ :=
  Pf.TupOnto.repAtTup_of_glob Zd.M Zd.δ u u' F0 what₂ (Pf.TupGlob.globMove_of u u' hS (Pf.FibD.dict_holds Zd))

end Formalism.L2.SG.Pf.TupFinal
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_deep {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hsig : (VS D).SigOK) (hA : ∀ p, Agree δ M p) (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hP : PrimeHyp D u (Tu D u')) (hrows : IsRowReps D F0 what₂)
    (hst : ProdEP2Cut.StepsU M δ u u' F0 what₂)
    (hSA : TupGlob.StabApprox ⟨δ, M, hA⟩ u u')
    (hFS : FrameGlobalPatching.FStarC ⟨δ, M, hA⟩ u u' F0 what₂) :
    CutAt M δ L u u' F0 what₂ := by
  have hRA : FibPart.RepAtTup M δ u u' F0 what₂ := TupFinal.repAtTup_of_stab ⟨δ, M, hA⟩ u u' F0 what₂ hSA
  have hTF := FibQ.tupFun_holds M δ u u' F0 what₂
  have hOZ := TupOrb.orbZT_holds M δ u u' F0 what₂
  have hfin : ∀ Λ ∈ what₂, ∀ Z : PairVal.MatR D, CntLocal.cntE (CntLocal.Tn u') F0 Λ Z ≠ ⊤ :=
    fun Λ hΛ Z => ZsVolFin.finR D u u' F0 what₂ hrows Z Λ hΛ
  have hN : PairVal.NormRepExists D u u' F0 what₂ := PCount.normRepExists_ctx ⟨hc, hrows, hP⟩
  have hM : Formalism.L2.SG.Pf.NormRepMove D u u' :=
    norm_representative_move D u u' (Formalism.L2.SG.Closed.TermStable_holds D u u') (Formalism.L2.SG.Closed.TermEqIff_holds D u u')
      (Formalism.L2.SG.Closed.TermFun_holds D u u') hP hsig
  exact cutAt_of_leaves hA hc hP hrows hN hM (local_phase_typed_places hA) (ZsVolAsm.volIdxProd_of_prodE M δ u u' F0 what₂ hP
      (ProdE.prodE_CZ_of_approxC M δ u u' F0 what₂ (ProdEApprox.approxC M δ u u' F0 what₂) hst))
    (fun _ => PCountEx.exist_holds hA u u')
    (fun _ => FibPart.sumFr_of M δ hTF hRA hOZ hA hc hP hN hrows hfin)
    (fun _ => FrameGlobalPatching.frGlob_of_fstar hFS) (PCount.intGenP_holds ⟨δ, M, hA⟩) PCount.tau_one_holds
    (PCount.partnerCount_holds_all ⟨δ, M, hA⟩)
    (FibPart.fibSum_of M δ hTF hRA hOZ) (densTh_of_ga (SplitCoefficientComponents.GaPlusTh_holds M δ u u'))

def CutLeavesDeep (D : Formalism.BasicNotions.D7) : Prop :=
  (VS D).SigOK →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (_L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      ProdEP2Cut.StepsU M δ u u' F0 what₂ ∧
      TupGlob.StabApprox ⟨δ, M, hA⟩ u u' ∧
      FrameGlobalPatching.FStarC ⟨δ, M, hA⟩ u u' F0 what₂

theorem rowsDatumP_of_deep {D : Formalism.BasicNotions.D7} (h : CutLeavesDeep D) : RowsDatumP D := by
  unfold CutLeavesDeep at h
  unfold RowsDatumP
  intro hsig δ M hA L u u' hc hP F0 what₂ hrows ϖ hϖ nc hnc
  obtain ⟨hst, hSA, hFS⟩ := h hsig δ M hA L u u' hc hP F0 what₂ hrows
  exact rowsDatum_at (cutAt_of_deep (L := L) hsig hA hc hP hrows hst hSA hFS)
    (eligFinite_of (Formalism.L2.SG.Closed.TermsAtFinite_holds D u u') hsig hrows) hrows ϖ hϖ nc hnc



end Formalism.L2.SG.Pf.Coef
end
end
