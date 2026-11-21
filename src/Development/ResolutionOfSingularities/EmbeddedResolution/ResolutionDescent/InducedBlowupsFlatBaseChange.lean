import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedCenterFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.BinaryCoproductBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrictTransformTower
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange

section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

namespace EmbeddedBlowupSequence

theorem detachedToCoprod_detachedCoprodInl_detachedCoprodMapOfLE (S : EmbeddedBlowupSequence k Y pY) (s a b : ℕ)
    (hsa : s < a) (hab : a + 1 ≤ b) :
    S.detachedToCoprod s a hsa ≫ S.detachedCoprodInl a ≫ S.detachedCoprodMapOfLE hab =
      S.detachedToCoprod s b (lt_of_lt_of_le hsa (le_trans (Nat.le_succ a) hab)) := by
  rw [← Category.assoc, ← S.detachedToCoprod_succ_of_lt s a hsa, S.detachedToCoprod_detachedCoprodMapOfLE]

theorem detachedCoprodInr_detachedCoprodMapOfLE (S : EmbeddedBlowupSequence k Y pY) (a b : ℕ) (hab : a + 1 ≤ b) :
    S.detachedCoprodInr a ≫ S.detachedCoprodMapOfLE hab =
      S.detachedToCoprod a b (lt_of_lt_of_le (Nat.lt_succ_self a) hab) := by
  rw [← S.detachedToCoprod_self a, S.detachedToCoprod_detachedCoprodMapOfLE]

def inactiveTotalToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (i : ℕ) :
    S.detachedCoprod i ⟶ Y :=
  (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ (S.inducedBlowups h).projectionToBase i

theorem detachedToCoprod_inactiveTotalToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (s i : ℕ)
    (hs : s < i) :
    S.detachedToCoprod s i hs ≫ S.inactiveTotalToBase h i = S.detachedι s ≫ S.strictTransformToBase s :=
  detachedToCoprod_inr_inducedBlowups_projectionToBase S h s i hs

theorem coprodDesc_strictTransformToBase_inactiveTotalToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (i : ℕ) :
    coprod.desc (S.strictTransformToBase i) (S.inactiveTotalToBase h i) = (S.inducedBlowups h).projectionToBase i := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc]
    exact (inl_inducedBlowups_projectionToBase S h i).symm
  · rw [coprod.inr_desc]
    rfl

end EmbeddedBlowupSequence

namespace ChartFlatBaseChange

variable {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [AlgebraicGeometry.IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [AlgebraicGeometry.LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

theorem reindex_lt_reindex (F : ChartFlatBaseChange S S') {s j : ℕ} (hsj : s < j)
    (hj : j ≤ S'.length) : F.reindex s < F.reindex j :=
  F.reindex_lt_reindex_of_lt hsj hj

private theorem reindex_le_reindex_succ (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j + 1 ≤ S'.length) :
    F.reindex j ≤ F.reindex (j + 1) :=
  (F.reindex_lt_succ j (by omega)).le

private theorem reindex_lt_reindex_succ (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j + 1 ≤ S'.length) :
    F.reindex j < F.reindex (j + 1) :=
  F.reindex_lt_succ j (by omega)

theorem strictTransformComparison_comp_strictTransformToBase (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j) = S'.strictTransformToBase j ≫ F.baseMap := by
  have : CategoryTheory.Mono S.emb := inferInstance
  have key : (F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j)) ≫ S.emb
      = (S'.strictTransformToBase j ≫ F.baseMap) ≫ S.emb := by
    calc (F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j)) ≫ S.emb
        = F.strictTransformComparison j hj ≫ (S.strictTransformToBase (F.reindex j) ≫ S.emb) := Category.assoc _ _ _
      _ = F.strictTransformComparison j hj ≫
            (S.strictTransformι (F.reindex j) ≫ S.ambientSeq.projectionToBase (F.reindex j)) := by
            rw [S.strictTransformToBase_emb (F.reindex j)]
      _ = (F.strictTransformComparison j hj ≫ S.strictTransformι (F.reindex j)) ≫
            S.ambientSeq.projectionToBase (F.reindex j) := (Category.assoc _ _ _).symm
      _ = (S'.strictTransformι j ≫ F.levelMap j hj) ≫ S.ambientSeq.projectionToBase (F.reindex j) := by
            rw [F.strictTransformComparison_comp_strictTransformι j hj]
      _ = S'.strictTransformι j ≫ (F.levelMap j hj ≫ S.ambientSeq.projectionToBase (F.reindex j)) :=
            Category.assoc _ _ _
      _ = S'.strictTransformι j ≫ (S'.ambientSeq.projectionToBase j ≫ F.ambientMap) := by
            rw [(F.isPullback_level j hj).w]
      _ = (S'.strictTransformι j ≫ S'.ambientSeq.projectionToBase j) ≫ F.ambientMap :=
            (Category.assoc _ _ _).symm
      _ = (S'.strictTransformToBase j ≫ S'.emb) ≫ F.ambientMap := by rw [S'.strictTransformToBase_emb j]
      _ = S'.strictTransformToBase j ≫ (S'.emb ≫ F.ambientMap) := Category.assoc _ _ _
      _ = S'.strictTransformToBase j ≫ (F.baseMap ≫ S.emb) := by rw [F.isPullback_emb.w]
      _ = (S'.strictTransformToBase j ≫ F.baseMap) ≫ S.emb := (Category.assoc _ _ _).symm
  exact (cancel_mono S.emb).mp key

theorem isPullback_strictTransformComparison_strictTransformToBase (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.strictTransformComparison j hj) (S'.strictTransformToBase j) (S.strictTransformToBase (F.reindex j))
      F.baseMap := by
  have h1 := (F.isPullback_strictTransformComparison_strictTransformι j hj).paste_vert (F.isPullback_level j hj)
  have h2 : IsPullback (F.strictTransformComparison j hj) (S'.strictTransformToBase j ≫ S'.emb)
      (S.strictTransformToBase (F.reindex j) ≫ S.emb) F.ambientMap := by
    rw [S'.strictTransformToBase_emb j, S.strictTransformToBase_emb (F.reindex j)]
    exact h1
  exact h2.of_bot (F.strictTransformComparison_comp_strictTransformToBase j hj) F.isPullback_emb

theorem isEmpty_of_comm_detachedScheme_of_not_mem_range (F : ChartFlatBaseChange S S') (s : ℕ) (hs : s < S.length)
    (hskip : ∀ j, j < S'.length → F.reindex j ≠ s) (Q : Scheme.{u}) (q : Q ⟶ S.detachedScheme s)
    (p : Q ⟶ Y') (hcomm : q ≫ S.detachedι s ≫ S.strictTransformToBase s = p ≫ F.baseMap) :
    IsEmpty ↥Q := by
  refine F.isEmpty_of_forall_reindex_ne s hs hskip Q q (p ≫ S'.emb) ?_
  calc q ≫ S.detachedι s ≫ S.strictTransformι s ≫ S.ambientSeq.projectionToBase s
      = q ≫ S.detachedι s ≫ S.strictTransformToBase s ≫ S.emb := by rw [S.strictTransformToBase_emb s]
    _ = (q ≫ S.detachedι s ≫ S.strictTransformToBase s) ≫ S.emb := by simp only [Category.assoc]
    _ = (p ≫ F.baseMap) ≫ S.emb := by rw [hcomm]
    _ = p ≫ (F.baseMap ≫ S.emb) := Category.assoc _ _ _
    _ = p ≫ (S'.emb ≫ F.ambientMap) := by rw [F.isPullback_emb.w]
    _ = (p ≫ S'.emb) ≫ F.ambientMap := (Category.assoc _ _ _).symm

private theorem isEmpty_of_hom_to_initial {P : Scheme.{u}}
    (f : P ⟶ ⊥_ Scheme.{u}) : IsEmpty ↥P :=
  Function.isEmpty f.base

private theorem inactiveTotalToBase_succ_eq_desc (T : EmbeddedBlowupSequence k Y pY)
    (hT : T.TransitionsAreBlowups) (i : ℕ) :
    T.inactiveTotalToBase hT (i + 1) =
      coprod.desc (T.inactiveTotalToBase hT i) (T.detachedι i ≫ T.strictTransformToBase i) := by
  have hl : T.detachedCoprodInl i ≫ T.inactiveTotalToBase hT (i + 1) = T.inactiveTotalToBase hT i := by
    refine T.detachedCoprod_hom_ext i ?_
    intro s hs
    calc T.detachedToCoprod s i hs ≫ T.detachedCoprodInl i ≫ T.inactiveTotalToBase hT (i + 1)
        = (T.detachedToCoprod s i hs ≫ T.detachedCoprodInl i) ≫ T.inactiveTotalToBase hT (i + 1) :=
          (Category.assoc _ _ _).symm
      _ = T.detachedToCoprod s (i + 1) (Nat.lt_succ_of_lt hs) ≫ T.inactiveTotalToBase hT (i + 1) := by
          rw [T.detachedToCoprod_succ_of_lt s i hs]
      _ = T.detachedι s ≫ T.strictTransformToBase s :=
          T.detachedToCoprod_inactiveTotalToBase hT s (i + 1) (Nat.lt_succ_of_lt hs)
      _ = T.detachedToCoprod s i hs ≫ T.inactiveTotalToBase hT i :=
          (T.detachedToCoprod_inactiveTotalToBase hT s i hs).symm
  have hr : T.detachedCoprodInr i ≫ T.inactiveTotalToBase hT (i + 1) = T.detachedι i ≫ T.strictTransformToBase i := by
    calc T.detachedCoprodInr i ≫ T.inactiveTotalToBase hT (i + 1)
        = T.detachedToCoprod i (i + 1) (Nat.lt_succ_self i) ≫ T.inactiveTotalToBase hT (i + 1) := by
          rw [T.detachedToCoprod_self i]
      _ = T.detachedι i ≫ T.strictTransformToBase i :=
          T.detachedToCoprod_inactiveTotalToBase hT i (i + 1) (Nat.lt_succ_self i)
  refine T.detachedCoprod_succ_hom_ext i ?_ ?_
  · exact hl.trans (coprod.inl_desc _ _).symm
  · exact hr.trans (coprod.inr_desc _ _).symm

private theorem forall_isEmpty_of_comm_inactiveTotalToBase (F : ChartFlatBaseChange S S')
    (h : S.TransitionsAreBlowups) :
    ∀ (i : ℕ), (∀ s, s < i → s < S.length) →
      (∀ s, s < i → ∀ j, j < S'.length → F.reindex j ≠ s) →
      ∀ (P : Scheme.{u}) (q : P ⟶ S.detachedCoprod i) (p : P ⟶ Y'),
        q ≫ S.inactiveTotalToBase h i = p ≫ F.baseMap → IsEmpty ↥P := by
  intro i
  induction i with
  | zero =>
      intro _ _ P q _ _
      exact isEmpty_of_hom_to_initial q
  | succ n ih =>
      intro hlt hskip P q p hcomm
      have h1 : IsPullback (initial.to (S.detachedCoprod n)) (initial.to Y')
          (S.inactiveTotalToBase h n) F.baseMap :=
        isPullback_initial_of_isEmpty (S.inactiveTotalToBase h n) F.baseMap
          (fun Q a b hab =>
            ih (fun s hs => hlt s (Nat.lt_succ_of_lt hs))
              (fun s hs => hskip s (Nat.lt_succ_of_lt hs)) Q a b hab)
      have h2 : IsPullback (initial.to (S.detachedScheme n)) (initial.to Y')
          (S.detachedι n ≫ S.strictTransformToBase n) F.baseMap :=
        isPullback_initial_of_isEmpty (S.detachedι n ≫ S.strictTransformToBase n) F.baseMap
          (fun Q c d hcd =>
            F.isEmpty_of_comm_detachedScheme_of_not_mem_range n (hlt n (Nat.lt_succ_self n))
              (hskip n (Nat.lt_succ_self n)) Q c d hcd)
      have h3 := isPullback_coprodMap_coprodDesc (initial.to (S.detachedCoprod n))
        (initial.to (S.detachedScheme n)) (initial.to Y') (initial.to Y')
        (S.inactiveTotalToBase h n) (S.detachedι n ≫ S.strictTransformToBase n) F.baseMap h1 h2
      have hcomm' : q ≫ coprod.desc (S.inactiveTotalToBase h n) (S.detachedι n ≫ S.strictTransformToBase n)
          = p ≫ F.baseMap :=
        (congrArg (fun t : S.detachedCoprod (n + 1) ⟶ Y => q ≫ t)
          (inactiveTotalToBase_succ_eq_desc S h n)).symm.trans hcomm
      exact isEmpty_of_hom_to_initial
        (h3.lift q p hcomm' ≫ coprod.desc (𝟙 (⊥_ Scheme.{u})) (𝟙 (⊥_ Scheme.{u})))

theorem isEmpty_of_comm_inactiveTotalToBase_of_not_mem_range (F : ChartFlatBaseChange S S') (h : S.TransitionsAreBlowups)
    (i : ℕ) (hlt : ∀ s, s < i → s < S.length)
    (hskip : ∀ s, s < i → ∀ j, j < S'.length → F.reindex j ≠ s) (P : Scheme.{u})
    (q : P ⟶ S.detachedCoprod i) (p : P ⟶ Y')
    (hcomm : q ≫ S.inactiveTotalToBase h i = p ≫ F.baseMap) : IsEmpty ↥P :=
  forall_isEmpty_of_comm_inactiveTotalToBase F h i hlt hskip P q p hcomm

theorem isPullback_detachedCoprodMapOfLE_inactiveTotalToBase (F : ChartFlatBaseChange S S') (h : S.TransitionsAreBlowups)
    {a b : ℕ} (hab : a ≤ b) (hlt : ∀ s, a ≤ s → s < b → s < S.length)
    (hskip : ∀ s, a ≤ s → s < b → ∀ j, j < S'.length → F.reindex j ≠ s) {P : Scheme.{u}}
    (q : P ⟶ S.detachedCoprod a) (p : P ⟶ Y')
    (hsq : IsPullback q p (S.inactiveTotalToBase h a) F.baseMap) :
    IsPullback (q ≫ S.detachedCoprodMapOfLE hab) p (S.inactiveTotalToBase h b) F.baseMap := by
  have main : ∀ (c : ℕ) (hac : a ≤ c),
      (∀ s, a ≤ s → s < c → s < S.length) →
      (∀ s, a ≤ s → s < c → ∀ j, j < S'.length → F.reindex j ≠ s) →
      IsPullback (q ≫ S.detachedCoprodMapOfLE hac) p (S.inactiveTotalToBase h c) F.baseMap := by
    intro c hac
    induction c, hac using Nat.le_induction with
    | base =>
        intro _ _
        have hself : S.detachedCoprodMapOfLE (Nat.le_refl a) = 𝟙 (S.detachedCoprod a) := S.detachedCoprodMapOfLE_self a
        have hpbRefl : IsPullback (q ≫ S.detachedCoprodMapOfLE (Nat.le_refl a)) p
            (S.inactiveTotalToBase h a) F.baseMap := by
          rw [hself, Category.comp_id]
          exact hsq
        exact hpbRefl
    | succ c hac ih =>
        intro hlt1 hskip1
        have ih' := ih (fun s h1 h2 => hlt1 s h1 (Nat.lt_succ_of_lt h2))
          (fun s h1 h2 => hskip1 s h1 (Nat.lt_succ_of_lt h2))
        have hc : c < S.length := hlt1 c hac (Nat.lt_succ_self c)
        have hsk : ∀ j, j < S'.length → F.reindex j ≠ c := hskip1 c hac (Nat.lt_succ_self c)
        have hF : ∀ (Q : Scheme.{u}) (cc : Q ⟶ S.detachedScheme c) (d : Q ⟶ Y'),
            cc ≫ S.detachedι c ≫ S.strictTransformToBase c = d ≫ F.baseMap → IsEmpty Q :=
          fun Q cc d hcomm => F.isEmpty_of_comm_detachedScheme_of_not_mem_range c hc hsk Q cc d hcomm
        have hinl : S.detachedCoprodInl c ≫ S.inactiveTotalToBase h (c + 1) = S.inactiveTotalToBase h c := by
          show S.detachedCoprodInl c ≫ (coprod.inr : S.detachedCoprod (c + 1) ⟶ S.totalSpace (c + 1)) ≫
              (S.inducedBlowups h).projectionToBase (c + 1) = S.inactiveTotalToBase h c
          rw [SequenceOfBlowups.projectionToBase_succ, inducedBlowups_blowupMorphism]
          exact S.detachedCoprodInl_inr_totalTransition_assoc c ((S.inducedBlowups h).projectionToBase c)
        have hinr : S.detachedCoprodInr c ≫ S.inactiveTotalToBase h (c + 1) =
            S.detachedι c ≫ S.strictTransformToBase c := by
          have hkey := S.detachedToCoprod_inactiveTotalToBase h c (c + 1) (Nat.lt_succ_self c)
          rw [S.detachedToCoprod_self c] at hkey
          exact hkey
        have hdesc : (coprod.desc (S.inactiveTotalToBase h c) (S.detachedι c ≫ S.strictTransformToBase c) :
            S.detachedCoprod c ⨿ S.detachedScheme c ⟶ Y) = S.inactiveTotalToBase h (c + 1) := by
          apply coprod.hom_ext
          · rw [coprod.inl_desc]
            exact hinl.symm
          · rw [coprod.inr_desc]
            exact hinr.symm
        have key1 : IsPullback ((q ≫ S.detachedCoprodMapOfLE hac) ≫ S.detachedCoprodInl c) p
            (S.inactiveTotalToBase h (c + 1)) F.baseMap := by
          have key0 := isPullback_comp_inl_coprodDesc (q ≫ S.detachedCoprodMapOfLE hac) p
            (S.inactiveTotalToBase h c) F.baseMap (S.detachedι c ≫ S.strictTransformToBase c) ih' hF
          rw [hdesc] at key0
          exact key0
        have hup : S.detachedCoprodMapOfLE (Nat.le_succ_of_le hac) = S.detachedCoprodMapOfLE hac ≫ S.detachedCoprodInl c :=
          S.detachedCoprodMapOfLE_succ hac
        have hpbSucc : IsPullback (q ≫ S.detachedCoprodMapOfLE (Nat.le_succ_of_le hac)) p
            (S.inactiveTotalToBase h (c + 1)) F.baseMap := by
          rw [hup, ← Category.assoc]
          exact key1
        exact hpbSucc
  exact main b hab hlt hskip

theorem isPullback_inactiveSchemeMap_baseMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    IsPullback (F.detachedSchemeComparison j hj) (S'.detachedι j ≫ S'.strictTransformToBase j)
      (S.detachedι (F.reindex j) ≫ S.strictTransformToBase (F.reindex j)) F.baseMap :=
  (F.isPullback_detachedSchemeComparison j hj).paste_vert (F.isPullback_strictTransformComparison_strictTransformToBase j hj.le)

def inactiveTotalMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] :
    ∀ (j : ℕ), j ≤ S'.length → (S'.detachedCoprod j ⟶ S.detachedCoprod (F.reindex j))
  | 0, _ => eqToHom S'.detachedCoprod_zero ≫ initial.to (S.detachedCoprod (F.reindex 0))
  | (j + 1), hj =>
      eqToHom (S'.detachedCoprod_succ j) ≫
        coprod.desc
          (inactiveTotalMap F j (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ j hj))
          (F.detachedSchemeComparison j (by omega) ≫
            S.detachedToCoprod (F.reindex j) (F.reindex (j + 1)) (F.reindex_lt_reindex_succ j hj))

private theorem inactiveTotalMap_succ_eq_desc (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (n : ℕ)
    (hj : n + 1 ≤ S'.length) :
    F.inactiveTotalMap (n + 1) hj =
      coprod.desc
        (F.inactiveTotalMap n (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ n hj))
        (F.detachedSchemeComparison n (lt_of_lt_of_le (Nat.lt_succ_self n) hj) ≫
          S.detachedToCoprod (F.reindex n) (F.reindex (n + 1)) (F.reindex_lt_reindex_succ n hj)) := by
  have h0 : F.inactiveTotalMap (n + 1) hj =
      eqToHom (S'.detachedCoprod_succ n) ≫
        coprod.desc
          (F.inactiveTotalMap n (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ n hj))
          (F.detachedSchemeComparison n (lt_of_lt_of_le (Nat.lt_succ_self n) hj) ≫
            S.detachedToCoprod (F.reindex n) (F.reindex (n + 1)) (F.reindex_lt_reindex_succ n hj)) := rfl
  have hid : eqToHom (S'.detachedCoprod_succ n) = 𝟙 (S'.detachedCoprod (n + 1)) := eqToHom_refl _ _
  rw [h0, hid]
  exact Category.id_comp _

private theorem detachedCoprodInl_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (n : ℕ)
    (hj : n + 1 ≤ S'.length) :
    S'.detachedCoprodInl n ≫ F.inactiveTotalMap (n + 1) hj =
      F.inactiveTotalMap n (Nat.le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ n hj) := by
  rw [inactiveTotalMap_succ_eq_desc F n hj]
  exact coprod.inl_desc _ _

private theorem detachedCoprodInr_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (n : ℕ)
    (hj : n + 1 ≤ S'.length) :
    S'.detachedCoprodInr n ≫ F.inactiveTotalMap (n + 1) hj =
      F.detachedSchemeComparison n (lt_of_lt_of_le (Nat.lt_succ_self n) hj) ≫
        S.detachedToCoprod (F.reindex n) (F.reindex (n + 1)) (F.reindex_lt_reindex_succ n hj) := by
  rw [inactiveTotalMap_succ_eq_desc F n hj]
  exact coprod.inr_desc _ _

private theorem forall_detachedToCoprod_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] :
    ∀ (j : ℕ) (hj : j ≤ S'.length) (s : ℕ) (hs : s < j),
      S'.detachedToCoprod s j hs ≫ F.inactiveTotalMap j hj =
        F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
          S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) := by
  intro j
  induction j with
  | zero =>
      intro hj s hs
      exact absurd hs (Nat.not_lt_zero s)
  | succ n ih =>
      intro hj s hs
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with hlt | heq
      · rw [S'.detachedToCoprod_succ_of_lt s n hlt, Category.assoc,
          detachedCoprodInl_inactiveTotalMap F n hj, ← Category.assoc,
          ih (Nat.le_of_succ_le hj) s hlt, Category.assoc, S.detachedToCoprod_detachedCoprodMapOfLE]
      · subst heq
        rw [S'.detachedToCoprod_self s, detachedCoprodInr_inactiveTotalMap F s hj]

theorem detachedToCoprod_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length)
    (s : ℕ) (hs : s < j) :
    S'.detachedToCoprod s j hs ≫ F.inactiveTotalMap j hj =
      F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
        S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) :=
  forall_detachedToCoprod_inactiveTotalMap F j hj s hs

private theorem inl_detachedCoprodMapOfLE (T : EmbeddedBlowupSequence k Y pY) {c b : ℕ}
    (hcb : c + 1 ≤ b) :
    (coprod.inl : T.detachedCoprod c ⟶ T.detachedCoprod c ⨿ T.detachedScheme c) ≫ T.detachedCoprodMapOfLE hcb =
      T.detachedCoprodMapOfLE (Nat.le_of_succ_le hcb) := by
  refine T.detachedCoprod_hom_ext c (fun s hs => ?_)
  have h1 := T.detachedToCoprod_detachedCoprodInl_detachedCoprodMapOfLE s c b hs hcb
  have h2 := T.detachedToCoprod_detachedCoprodMapOfLE hs (Nat.le_of_succ_le hcb)
  exact h1.trans h2.symm

private theorem inr_detachedCoprodMapOfLE (T : EmbeddedBlowupSequence k Y pY) {c b : ℕ}
    (hcb : c + 1 ≤ b) :
    (coprod.inr : T.detachedScheme c ⟶ T.detachedCoprod c ⨿ T.detachedScheme c) ≫ T.detachedCoprodMapOfLE hcb =
      T.detachedToCoprod c b hcb :=
  T.detachedCoprodInr_detachedCoprodMapOfLE c b hcb

private theorem isPullback_of_fst_eq {P X Z W : Scheme.{u}} {f f' : P ⟶ X} {g : P ⟶ Z}
    {q : X ⟶ W} {u : Z ⟶ W} (hf : f = f') (hp : IsPullback f' g q u) : IsPullback f g q u := by
  subst hf
  exact hp

private theorem isPullback_of_fst_eq_of_snd_eq {P X Z W : Scheme.{u}} {f f' : P ⟶ X}
    {g g' : P ⟶ Z} {q : X ⟶ W} {u : Z ⟶ W} (hf : f = f') (hg : g = g')
    (hp : IsPullback f' g' q u) : IsPullback f g q u := by
  subst hf
  subst hg
  exact hp

private theorem isPullback_of_snd_eq_of_map_eq {P X Z W : Scheme.{u}} {f : P ⟶ X} {g g' : P ⟶ Z}
    {q q' : X ⟶ W} {u : Z ⟶ W} (hg : g = g') (hq : q = q')
    (hp : IsPullback f g' q' u) : IsPullback f g q u := by
  subst hg
  subst hq
  exact hp

theorem isPullback_inactiveTotalMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y']
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.inactiveTotalMap j hj) (S'.inactiveTotalToBase h' j)
      (S.inactiveTotalToBase h (F.reindex j)) F.baseMap := by
  have main : ∀ (m : ℕ) (hm : m ≤ S'.length),
      IsPullback (F.inactiveTotalMap m hm) (S'.inactiveTotalToBase h' m)
        (S.inactiveTotalToBase h (F.reindex m)) F.baseMap := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hI : IsInitial (S'.detachedCoprod 0) := initialIsInitial
        have hlen : F.reindex 0 ≤ S.length := F.reindex_le_length (Nat.zero_le S'.length)
        have hempty : ∀ (P : Scheme.{u}) (a : P ⟶ S.detachedCoprod (F.reindex 0)) (b : P ⟶ Y'),
            a ≫ S.inactiveTotalToBase h (F.reindex 0) = b ≫ F.baseMap → IsEmpty ↥P := by
          intro P a b hcomm
          exact F.isEmpty_of_comm_inactiveTotalToBase_of_not_mem_range h (F.reindex 0)
            (fun s hs => lt_of_lt_of_le hs hlen)
            (fun s hs j' hj' => F.reindex_ne_of_lt_reindex_zero s hs j' hj') P a b hcomm
        have hpb :=
          isPullback_initial_of_isEmpty (S.inactiveTotalToBase h (F.reindex 0)) F.baseMap hempty
        have e1 : F.inactiveTotalMap 0 hm = initial.to (S.detachedCoprod (F.reindex 0)) :=
          hI.hom_ext _ _
        have e2 : S'.inactiveTotalToBase h' 0 = initial.to Y' := hI.hom_ext _ _
        exact isPullback_of_fst_eq_of_snd_eq e1 e2 hpb
    | succ n ih =>
        intro hm
        have hn : n ≤ S'.length := Nat.le_of_succ_le hm
        have hnlt : n < S'.length := hm
        have hab : F.reindex n + 1 ≤ F.reindex (n + 1) := F.reindex_lt_succ n hnlt
        have hlen : F.reindex (n + 1) ≤ S.length := F.reindex_le_length hm
        have hcop := isPullback_coprodMap_coprodDesc (F.inactiveTotalMap n hn)
          (F.detachedSchemeComparison n hnlt) (S'.inactiveTotalToBase h' n) (S'.detachedι n ≫ S'.strictTransformToBase n)
          (S.inactiveTotalToBase h (F.reindex n))
          (S.detachedι (F.reindex n) ≫ S.strictTransformToBase (F.reindex n)) F.baseMap (ih hn)
          (F.isPullback_inactiveSchemeMap_baseMap n hnlt)
        have hcop2 : IsPullback
            (coprod.map (F.inactiveTotalMap n hn) (F.detachedSchemeComparison n hnlt))
            (S'.inactiveTotalToBase h' (n + 1)) (S.inactiveTotalToBase h (F.reindex n + 1)) F.baseMap :=
          isPullback_of_snd_eq_of_map_eq (inactiveTotalToBase_succ_eq_desc S' h' n)
            (inactiveTotalToBase_succ_eq_desc S h (F.reindex n)) hcop
        have hstep := F.isPullback_detachedCoprodMapOfLE_inactiveTotalToBase h hab
          (fun s _ hs2 => lt_of_lt_of_le hs2 hlen)
          (fun s hs1 hs2 j' hj' => F.reindex_ne_of_reindex_lt_of_lt_reindex_succ n hnlt s (by omega) hs2 j' hj')
          (coprod.map (F.inactiveTotalMap n hn) (F.detachedSchemeComparison n hnlt))
          (S'.inactiveTotalToBase h' (n + 1)) hcop2
        have hE : F.inactiveTotalMap (n + 1) hm =
            coprod.map (F.inactiveTotalMap n hn) (F.detachedSchemeComparison n hnlt) ≫
              S.detachedCoprodMapOfLE hab := by
          refine S'.detachedCoprod_succ_hom_ext n ?_ ?_
          · exact (detachedCoprodInl_inactiveTotalMap F n hm).trans
              ((coprod.inl_map_assoc (F.inactiveTotalMap n hn)
                  (F.detachedSchemeComparison n hnlt) (S.detachedCoprodMapOfLE hab)).trans
                (congrArg
                  (fun t : (S.detachedCoprod (F.reindex n) ⟶ S.detachedCoprod (F.reindex (n + 1))) =>
                    F.inactiveTotalMap n hn ≫ t)
                  (inl_detachedCoprodMapOfLE S hab))).symm
          · exact (detachedCoprodInr_inactiveTotalMap F n hm).trans
              ((coprod.inr_map_assoc (F.inactiveTotalMap n hn)
                  (F.detachedSchemeComparison n hnlt) (S.detachedCoprodMapOfLE hab)).trans
                (congrArg
                  (fun t : (S.detachedScheme (F.reindex n) ⟶ S.detachedCoprod (F.reindex (n + 1))) =>
                    F.detachedSchemeComparison n hnlt ≫ t)
                  (inr_detachedCoprodMapOfLE S hab))).symm
        exact isPullback_of_fst_eq hE hstep
  exact main j hj

def totalSpaceMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    S'.totalSpace j ⟶ S.totalSpace (F.reindex j) :=
  coprod.map (F.strictTransformComparison j hj) (F.inactiveTotalMap j hj)

theorem totalSpaceMap_eq_coprodMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    F.totalSpaceMap j hj = coprod.map (F.strictTransformComparison j hj) (F.inactiveTotalMap j hj) := rfl

theorem inl_totalSpaceMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    (coprod.inl : S'.strictTransform j ⟶ S'.totalSpace j) ≫ F.totalSpaceMap j hj =
      F.strictTransformComparison j hj ≫
        (coprod.inl : S.strictTransform (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  simp [ChartFlatBaseChange.totalSpaceMap]

theorem detachedToCoprod_inr_totalSpaceMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length)
    (s : ℕ) (hs : s < j) :
    S'.detachedToCoprod s j hs ≫ (coprod.inr : S'.detachedCoprod j ⟶ S'.totalSpace j) ≫
        F.totalSpaceMap j hj =
      F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
        S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) ≫
          (coprod.inr : S.detachedCoprod (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  rw [F.totalSpaceMap_eq_coprodMap j hj, coprod.inr_map, ← Category.assoc,
    F.detachedToCoprod_inactiveTotalMap j hj s hs, Category.assoc]

theorem isPullback_totalSpaceMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.totalSpaceMap j hj) ((S'.inducedBlowups h').projectionToBase j)
      ((S.inducedBlowups h).projectionToBase (F.reindex j)) F.baseMap := by
  have key := isPullback_coprodMap_coprodDesc (F.strictTransformComparison j hj)
    (F.inactiveTotalMap j hj) (S'.strictTransformToBase j) (S'.inactiveTotalToBase h' j)
    (S.strictTransformToBase (F.reindex j)) (S.inactiveTotalToBase h (F.reindex j)) F.baseMap
    (F.isPullback_strictTransformComparison_strictTransformToBase j hj) (F.isPullback_inactiveTotalMap h h' j hj)
  rw [S'.coprodDesc_strictTransformToBase_inactiveTotalToBase h' j, S.coprodDesc_strictTransformToBase_inactiveTotalToBase h (F.reindex j)] at key
  rw [F.totalSpaceMap_eq_coprodMap j hj]
  exact key

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
end

section
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

namespace FunctorialResolution.EmbeddedResolution

def IsPullbackUpToEmptyCenters {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) : Prop :=
  ∃ (r : ℕ → ℕ) (e : ∀ i, i ≤ s'.length → (s'.schemeAt i ≅ pullback φ (s.projectionToBase (r i)))),
    (∀ i < s'.length, r i < s.length) ∧
    (∀ i j : ℕ, j ≤ s'.length → i < j → r i < r j) ∧
    r s'.length = s.length ∧
    (∀ i < s.length, (¬ ∃ j < s'.length, r j = i) →
      ¬ ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support) ∧
    (∀ (i : ℕ) (hi : i ≤ s'.length),
      (e i hi).hom ≫ pullback.fst φ (s.projectionToBase (r i)) = s'.projectionToBase i) ∧
    (∀ (i : ℕ) (hi : i < s'.length) (hr : r i ≤ r (i + 1)),
      s'.transitionMapSucc i ≫ (e i (Nat.le_of_lt hi)).hom =
        (e (i + 1) (Nat.succ_le_of_lt hi)).hom ≫ s.pullbackTransitionMap φ hr) ∧
    (∀ (i : ℕ) (hi : i < s'.length),
      s'.center i =
        (s.center (r i)).comap
          ((e i (Nat.le_of_lt hi)).hom ≫ pullback.snd φ (s.projectionToBase (r i))))

private theorem ne_top_iff_exists_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) :
    I ≠ ⊤ ↔ ∃ x, x ∈ I.support := by
  have hiff : I.support = ⊥ ↔ I = ⊤ := by simp
  constructor
  · intro hne
    by_contra hx
    refine hne (hiff.mp (SetLike.ext fun y => ⟨fun hy => ?_, fun hy => (hy : False).elim⟩))
    exact absurd (⟨y, hy⟩ : ∃ x, x ∈ I.support) hx
  · rintro ⟨x, hx⟩ hI
    rw [hiff.mpr hI] at hx
    exact hx

private theorem comap_iso_hom_ne_top {X Y : Scheme.{u}} (E : X ≅ Y) (J : Y.IdealSheafData)
    (h : J ≠ ⊤) : J.comap E.hom ≠ ⊤ := by
  intro hc
  apply h
  have hJ : J = (J.comap E.hom).comap E.inv := by
    rw [← Scheme.IdealSheafData.comap_comp, E.inv_hom_id, Scheme.IdealSheafData.comap_id]
  rw [hJ, hc, Scheme.IdealSheafData.comap_top]

private theorem comp_eq_of_eq_of_comp_eq {A B C : Scheme.{u}} (u : A ⟶ B) {f g : B ⟶ C} (hfg : f = g)
    {k : A ⟶ C} (hk : u ≫ g = k) : u ≫ f = k := by
  rw [hfg]
  exact hk

private theorem comp_comp_eq_of_comp_eq {A B C D : Scheme.{u}} {u : A ⟶ B} {v : B ⟶ C} {w : A ⟶ C}
    (h : u ≫ v = w) (k : C ⟶ D) : u ≫ v ≫ k = w ≫ k := by
  rw [← Category.assoc, h]

private theorem comap_congr_morphism {A B : Scheme.{u}} {u v : A ⟶ B} (h : u = v) (I : B.IdealSheafData) :
    I.comap u = I.comap v := by
  rw [h]

private theorem comap_congr_idealSheaf {A B : Scheme.{u}} (u : A ⟶ B) {I J : B.IdealSheafData}
    (h : I = J) : I.comap u = J.comap u := by
  rw [h]

private noncomputable def pullbackCongrRightHom {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) : pullback φ f ⟶ pullback φ g :=
  pullback.lift (pullback.fst φ f) (pullback.snd φ f ≫ θ.hom)
    (by rw [Category.assoc, hθ]; exact pullback.condition)

private theorem pullbackCongrRightHom_fst {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    pullbackCongrRightHom φ f g θ hθ ≫ pullback.fst φ g = pullback.fst φ f :=
  pullback.lift_fst _ _ _

private theorem pullbackCongrRightHom_snd {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    pullbackCongrRightHom φ f g θ hθ ≫ pullback.snd φ g = pullback.snd φ f ≫ θ.hom :=
  pullback.lift_snd _ _ _

private noncomputable def pullbackCongrRightIso {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) : pullback φ f ≅ pullback φ g where
  hom := pullbackCongrRightHom φ f g θ hθ
  inv := pullbackCongrRightHom φ g f θ.symm (by rw [← hθ, Iso.symm_hom, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackCongrRightHom_fst, pullbackCongrRightHom_fst, Category.id_comp]
    · rw [Category.assoc, pullbackCongrRightHom_snd, ← Category.assoc, pullbackCongrRightHom_snd, Category.assoc, Iso.symm_hom,
        θ.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackCongrRightHom_fst, pullbackCongrRightHom_fst, Category.id_comp]
    · rw [Category.assoc, pullbackCongrRightHom_snd, ← Category.assoc, pullbackCongrRightHom_snd, Category.assoc, Iso.symm_hom,
        θ.inv_hom_id, Category.comp_id, Category.id_comp]

private theorem pullbackCongrRightIso_hom_fst {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    (pullbackCongrRightIso φ f g θ hθ).hom ≫ pullback.fst φ g = pullback.fst φ f :=
  pullbackCongrRightHom_fst φ f g θ hθ

private theorem pullbackCongrRightIso_hom_snd {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    (pullbackCongrRightIso φ f g θ hθ).hom ≫ pullback.snd φ g = pullback.snd φ f ≫ θ.hom :=
  pullbackCongrRightHom_snd φ f g θ hθ

private theorem exists_pullbackIso_of_iso {X X' A Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (u : A ≅ pullback φ f) (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    ∃ v : A ≅ pullback φ g,
      v.hom ≫ pullback.fst φ g = u.hom ≫ pullback.fst φ f ∧
      v.hom ≫ pullback.snd φ g = u.hom ≫ pullback.snd φ f ≫ θ.hom := by
  refine ⟨u ≪≫ pullbackCongrRightIso φ f g θ hθ, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, pullbackCongrRightIso_hom_fst]
  · rw [Iso.trans_hom, Category.assoc, pullbackCongrRightIso_hom_snd]

private theorem comap_pullback_snd_ne_top_iff_of_iso {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X)
    (g : Z' ⟶ X) (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) (I : Z.IdealSheafData)
    (J : Z'.IdealSheafData) (hIJ : J.comap θ.hom = I) :
    (I.comap (pullback.snd φ f) ≠ ⊤) ↔ (J.comap (pullback.snd φ g) ≠ ⊤) := by
  have hkey : (J.comap (pullback.snd φ g)).comap (pullbackCongrRightIso φ f g θ hθ).hom
      = I.comap (pullback.snd φ f) := by
    rw [← Scheme.IdealSheafData.comap_comp, pullbackCongrRightIso_hom_snd, Scheme.IdealSheafData.comap_comp, hIJ]
  constructor
  · intro h hc
    apply h
    rw [← hkey, hc, Scheme.IdealSheafData.comap_top]
  · intro h
    rw [← hkey]
    exact comap_iso_hom_ne_top (pullbackCongrRightIso φ f g θ hθ) _ h

private theorem nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    (i : ℕ) :
    ((s.center (s.nontrivialIndex i)).comap (pullback.snd φ (s.projectionToBase (s.nontrivialIndex i))) ≠ ⊤) ↔
      ((s.withoutIsoBlowups.center i).comap (pullback.snd φ (s.withoutIsoBlowups.projectionToBase i)) ≠ ⊤) :=
  comap_pullback_snd_ne_top_iff_of_iso φ (s.projectionToBase (s.nontrivialIndex i)) (s.withoutIsoBlowups.projectionToBase i) (Iso.refl _)
    ((Category.id_comp (s.withoutIsoBlowups.projectionToBase i)).trans (s.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex i))
    (s.center (s.nontrivialIndex i)) (s.withoutIsoBlowups.center i) (Scheme.IdealSheafData.comap_id _)

private theorem eqToIso_hom_comp_projectionToBase {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (hab : a = b) :
    (eqToIso (congrArg s.schemeAt hab)).hom ≫ s.projectionToBase b = s.projectionToBase a := by
  subst hab
  simp

private theorem center_comap_eqToIso_hom {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (hab : a = b) :
    (s.center b).comap (eqToIso (congrArg s.schemeAt hab)).hom = s.center a := by
  subst hab
  simp

private theorem transitionMap_comp_eqToIso {X : Scheme.{u}} (s : SequenceOfBlowups X) {p q p' q' : ℕ}
    (hp : p = p') (hq : q = q') (hpq : p ≤ q) (hpq' : p' ≤ q') :
    s.transitionMap hpq ≫ (eqToIso (congrArg s.schemeAt hp)).hom
      = (eqToIso (congrArg s.schemeAt hq)).hom ≫ s.transitionMap hpq' := by
  subst hp
  subst hq
  simp

private theorem center_comap_pullback_snd_ne_top_congr {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    {a b : ℕ} (hab : a = b)
    (h : (s.center b).comap (pullback.snd φ (s.projectionToBase b)) ≠ ⊤) :
    (s.center a).comap (pullback.snd φ (s.projectionToBase a)) ≠ ⊤ := by
  subst hab
  exact h

private theorem pullbackTransitionMap_self {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X) {i : ℕ}
    (h : i ≤ i) : s.pullbackTransitionMap φ h = 𝟙 (pullback φ (s.projectionToBase i)) := by
  refine pullback.hom_ext ?_ ?_
  · rw [s.pullbackTransitionMap_fst, Category.id_comp]
  · rw [s.pullbackTransitionMap_snd, s.transitionMap_self, Category.comp_id, Category.id_comp]

private theorem pullbackTransitionMap_comp {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    s.pullbackTransitionMap φ hbc ≫ s.pullbackTransitionMap φ hab = s.pullbackTransitionMap φ (hab.trans hbc) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
  · rw [Category.assoc, s.pullbackTransitionMap_snd, ← Category.assoc, s.pullbackTransitionMap_snd, Category.assoc,
      s.transitionMap_trans, s.pullbackTransitionMap_snd]

private theorem pullbackTransitionMap_comp_assoc {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) {W : Scheme.{u}}
    (k : pullback φ (s.projectionToBase a) ⟶ W) :
    s.pullbackTransitionMap φ hbc ≫ s.pullbackTransitionMap φ hab ≫ k
      = s.pullbackTransitionMap φ (hab.trans hbc) ≫ k := by
  rw [← Category.assoc, pullbackTransitionMap_comp]

private theorem pullbackTransitionMap_snd_assoc {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X)
    {i i' : ℕ} (h : i ≤ i') {W : Scheme.{u}} (k : s.schemeAt i ⟶ W) :
    s.pullbackTransitionMap φ h ≫ pullback.snd φ (s.projectionToBase i) ≫ k
      = pullback.snd φ (s.projectionToBase i') ≫ s.transitionMap h ≫ k := by
  rw [← Category.assoc, s.pullbackTransitionMap_snd, Category.assoc]

namespace IsPullbackUpToEmptyCenters

theorem isPullbackSequenceOfBlowups_withoutIsoBlowups {X X' : Scheme.{u}} {φ : X' ⟶ X} {s' : SequenceOfBlowups X'}
    {s : SequenceOfBlowups X} (h : IsPullbackUpToEmptyCenters φ s' s) :
    IsPullbackBlowupSequence φ s'.withoutIsoBlowups s.withoutIsoBlowups := by
  obtain ⟨r, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hle : ∀ j : ℕ, j ≤ s'.lengthWithoutIsoBlowups → s'.nontrivialIndex j ≤ s'.length := fun j hj =>
    s'.nontrivialIndex_le_length hj
  have hrmono : ∀ i i' : ℕ, i ≤ i' → i' ≤ s'.length → r i ≤ r i' := by
    intro i i' hii hi'
    rcases eq_or_lt_of_le hii with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (h2 i i' hi' hlt)
  have hdown : ∀ (i i' : ℕ) (hii' : i ≤ i') (hi' : i' ≤ s'.length) {W : Scheme.{u}}
      (k : pullback φ (s.projectionToBase (r i)) ⟶ W),
      s'.transitionMap hii' ≫ (e i (hii'.trans hi')).hom ≫ k
        = (e i' hi').hom ≫ s.pullbackTransitionMap φ (hrmono i i' hii' hi') ≫ k := by
    intro i i' hii'
    induction i', hii' using Nat.le_induction with
    | base =>
      intro hi W k
      rw [s'.transitionMap_self, Category.id_comp, pullbackTransitionMap_self, Category.id_comp]
    | succ m hm ih =>
      intro hi W k
      have hm' : m ≤ s'.length := le_trans (Nat.le_succ m) hi
      have hmlt : m < s'.length := lt_of_lt_of_le (Nat.lt_succ_self m) hi
      have hrstep : r m ≤ r (m + 1) := hrmono m (m + 1) (Nat.le_succ m) hi
      have hstep : s'.transitionMapSucc m ≫ (e m hm').hom
          = (e (m + 1) hi).hom ≫ s.pullbackTransitionMap φ hrstep := h6 m hmlt hrstep
      have hdec : s'.transitionMap (hm.trans (Nat.le_succ m)) = s'.transitionMapSucc m ≫ s'.transitionMap hm := by
        rw [s'.blowupMorphism_eq_transitionMap]
        exact (s'.transitionMap_trans hm (Nat.le_succ m)).symm
      rw [hdec, Category.assoc, ih hm' k, ← Category.assoc, hstep, Category.assoc,
        pullbackTransitionMap_comp_assoc]
  have key : ∀ j : ℕ, ∃ k : ℕ, j ≤ s'.lengthWithoutIsoBlowups → s.nontrivialIndex k = r (s'.nontrivialIndex j) := by
    intro j
    rcases lt_trichotomy j s'.lengthWithoutIsoBlowups with hj | hj | hj
    · have ha : s'.nontrivialIndex j < s'.length := s'.nontrivialIndex_lt_length hj
      have hc : s'.center (s'.nontrivialIndex j) ≠ ⊤ := s'.center_nontrivialIndex_ne_top hj
      have hc2 : s.center (r (s'.nontrivialIndex j)) ≠ ⊤ := by
        intro hcc
        apply hc
        rw [h7 (s'.nontrivialIndex j) ha, hcc, Scheme.IdealSheafData.comap_top]
      obtain ⟨k, _, hk2⟩ := s.exists_nontrivialIndex_eq_of_center_ne_top (h1 _ ha) hc2
      exact ⟨k, fun _ => hk2⟩
    · refine ⟨s.lengthWithoutIsoBlowups, fun _ => ?_⟩
      rw [s.nontrivialIndex_lengthWithoutIsoBlowups, hj, s'.nontrivialIndex_lengthWithoutIsoBlowups, h3]
    · exact ⟨0, fun hle' => absurd hle' (not_le.mpr hj)⟩
  choose μ hμ using key
  have hθ : ∀ (j : ℕ) (hj : j ≤ s'.lengthWithoutIsoBlowups),
      (eqToIso (congrArg s.schemeAt (hμ j hj).symm)).hom ≫ s.withoutIsoBlowups.projectionToBase (μ j)
        = s.projectionToBase (r (s'.nontrivialIndex j)) := by
    intro j hj
    exact comp_eq_of_eq_of_comp_eq ((eqToIso (congrArg s.schemeAt (hμ j hj).symm)).hom)
      (s.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex (μ j)) (eqToIso_hom_comp_projectionToBase s (hμ j hj).symm)
  have hEx : ∀ (j : ℕ) (hj : j ≤ s'.lengthWithoutIsoBlowups),
      ∃ v : s'.withoutIsoBlowups.schemeAt j ≅ pullback φ (s.withoutIsoBlowups.projectionToBase (μ j)),
        v.hom ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j))
            = (e (s'.nontrivialIndex j) (hle j hj)).hom ≫
                pullback.fst φ (s.projectionToBase (r (s'.nontrivialIndex j))) ∧
        v.hom ≫ pullback.snd φ (s.withoutIsoBlowups.projectionToBase (μ j))
            = (e (s'.nontrivialIndex j) (hle j hj)).hom ≫
                pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
                  (eqToIso (congrArg s.schemeAt (hμ j hj).symm)).hom := by
    intro j hj
    exact exists_pullbackIso_of_iso φ (s.projectionToBase (r (s'.nontrivialIndex j))) (s.withoutIsoBlowups.projectionToBase (μ j))
      (e (s'.nontrivialIndex j) (hle j hj)) (eqToIso (congrArg s.schemeAt (hμ j hj).symm)) (hθ j hj)
  choose E hEfst0 hEsnd0 using hEx
  have hEfst : ∀ (j : ℕ) (hj : j ≤ s'.lengthWithoutIsoBlowups),
      (E j hj).hom ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j)) = s'.withoutIsoBlowups.projectionToBase j := by
    intro j hj
    exact ((hEfst0 j hj).trans (h5 (s'.nontrivialIndex j) (hle j hj))).trans
      (s'.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex j).symm
  unfold IsPullbackBlowupSequence
  refine ⟨μ, E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hh := hμ j (le_of_lt hj)
    have hlt : s.nontrivialIndex (μ j) < s.nontrivialIndex s.lengthWithoutIsoBlowups := by
      rw [hh, s.nontrivialIndex_lengthWithoutIsoBlowups]
      exact h1 (s'.nontrivialIndex j) (s'.nontrivialIndex_lt_length hj)
    exact s.nontrivialIndex_strictMono.lt_iff_lt.mp hlt
  · intro j k hk hjk
    have hj1 : j ≤ s'.lengthWithoutIsoBlowups := le_of_lt (lt_of_lt_of_le hjk hk)
    have hlt : s.nontrivialIndex (μ j) < s.nontrivialIndex (μ k) := by
      rw [hμ j hj1, hμ k hk]
      exact h2 (s'.nontrivialIndex j) (s'.nontrivialIndex k) (hle k hk) (s'.nontrivialIndex_strictMono hjk)
    exact s.nontrivialIndex_strictMono.lt_iff_lt.mp hlt
  · have hh : s.nontrivialIndex (μ s'.lengthWithoutIsoBlowups) = s.nontrivialIndex s.lengthWithoutIsoBlowups := by
      rw [hμ s'.lengthWithoutIsoBlowups le_rfl, s'.nontrivialIndex_lengthWithoutIsoBlowups, h3, s.nontrivialIndex_lengthWithoutIsoBlowups]
    exact s.nontrivialIndex_strictMono.injective hh
  · intro i hi
    have hi' : i < s.lengthWithoutIsoBlowups := hi
    have hiL : s.nontrivialIndex i < s.length := s.nontrivialIndex_lt_length hi'
    constructor
    · intro hx
      have hne : (s.center (s.nontrivialIndex i)).comap
          (pullback.snd φ (s.projectionToBase (s.nontrivialIndex i))) ≠ ⊤ :=
        (nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups φ s i).mpr ((ne_top_iff_exists_mem_support _).mpr hx)
      obtain ⟨j0, hj0, hrj0⟩ : ∃ j < s'.length, r j = s.nontrivialIndex i := by
        by_contra hcon
        exact h4 (s.nontrivialIndex i) hiL hcon ((ne_top_iff_exists_mem_support _).mp hne)
      have hK : (s.center (r j0)).comap (pullback.snd φ (s.projectionToBase (r j0))) ≠ ⊤ :=
        center_comap_pullback_snd_ne_top_congr φ s hrj0 hne
      have hcen : s'.center j0 ≠ ⊤ := by
        rw [h7 j0 hj0, Scheme.IdealSheafData.comap_comp]
        exact comap_iso_hom_ne_top (e j0 (le_of_lt hj0)) _ hK
      obtain ⟨k, hk1, hk2⟩ := s'.exists_nontrivialIndex_eq_of_center_ne_top hj0 hcen
      refine ⟨k, hk1, ?_⟩
      apply s.nontrivialIndex_strictMono.injective
      rw [hμ k (le_of_lt hk1), hk2]
      exact hrj0
    · rintro ⟨j, hj, rfl⟩
      refine (ne_top_iff_exists_mem_support _).mp ((nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups φ s (μ j)).mp ?_)
      refine center_comap_pullback_snd_ne_top_congr φ s (hμ j (le_of_lt hj)) ?_
      intro hcc
      refine s'.center_nontrivialIndex_ne_top hj ?_
      rw [h7 (s'.nontrivialIndex j) (s'.nontrivialIndex_lt_length hj), Scheme.IdealSheafData.comap_comp, hcc,
        Scheme.IdealSheafData.comap_top]
  · exact fun i hi => hEfst i hi
  · intro j hj hr
    have hj1 : j ≤ s'.lengthWithoutIsoBlowups := le_of_lt hj
    have hj2 : j + 1 ≤ s'.lengthWithoutIsoBlowups := hj
    have haj1 : s'.nontrivialIndex (j + 1) ≤ s'.length := hle (j + 1) hj2
    have hstep : s'.nontrivialIndex j ≤ s'.nontrivialIndex (j + 1) := le_of_lt (s'.nontrivialIndex_lt_succ j)
    have hrr : r (s'.nontrivialIndex j) ≤ r (s'.nontrivialIndex (j + 1)) :=
      hrmono (s'.nontrivialIndex j) (s'.nontrivialIndex (j + 1)) hstep haj1
    refine pullback.hom_ext ?_ ?_
    · have hL : (s'.withoutIsoBlowups.transitionMapSucc j ≫ (E j hj1).hom)
          ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j)) = s'.withoutIsoBlowups.projectionToBase (j + 1) := by
        rw [Category.assoc, hEfst j hj1]
        exact (s'.withoutIsoBlowups.projectionToBase_succ j).symm
      have hR : ((E (j + 1) hj2).hom ≫ s.withoutIsoBlowups.pullbackTransitionMap φ hr)
          ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j)) = s'.withoutIsoBlowups.projectionToBase (j + 1) := by
        rw [Category.assoc, SequenceOfBlowups.pullbackTransitionMap_fst, hEfst (j + 1) hj2]
      exact hL.trans hR.symm
    · have hL := (Category.assoc (s'.withoutIsoBlowups.transitionMapSucc j) (E j hj1).hom
            (pullback.snd φ (s.withoutIsoBlowups.projectionToBase (μ j)))).trans
          (((whisker_eq (s'.withoutIsoBlowups.transitionMapSucc j) (hEsnd0 j hj1)).trans
              (eq_whisker (s'.withoutIsoBlowups_blowupMorphism j) _)).trans
            ((hdown (s'.nontrivialIndex j) (s'.nontrivialIndex (j + 1)) hstep haj1 _).trans
              ((whisker_eq _ (pullbackTransitionMap_snd_assoc s φ hrr _)).trans
                (whisker_eq _ (whisker_eq _
                  (transitionMap_comp_eqToIso s (hμ j hj1).symm (hμ (j + 1) hj2).symm hrr
                    (s.nontrivialIndex_monotone hr)))))))
      have hR := (Category.assoc (E (j + 1) hj2).hom (s.withoutIsoBlowups.pullbackTransitionMap φ hr)
            (pullback.snd φ (s.withoutIsoBlowups.projectionToBase (μ j)))).trans
          ((whisker_eq (E (j + 1) hj2).hom
              (SequenceOfBlowups.pullbackTransitionMap_snd s.withoutIsoBlowups φ hr)).trans
            ((comp_comp_eq_of_comp_eq (hEsnd0 (j + 1) hj2) (s.withoutIsoBlowups.transitionMap hr)).trans
              ((Category.assoc _ _ _).trans
                ((whisker_eq _ (Category.assoc _ _ _)).trans
                  (whisker_eq _ (whisker_eq _
                    (whisker_eq _ (s.withoutIsoBlowups_transitionMap hr))))))))
      exact hL.trans hR.symm
  · intro j hj
    have hj1 : j ≤ s'.lengthWithoutIsoBlowups := le_of_lt hj
    have haj : s'.nontrivialIndex j < s'.length := s'.nontrivialIndex_lt_length hj
    refine Eq.trans ?_ (comap_congr_morphism (hEsnd0 j hj1) (s.center (s.nontrivialIndex (μ j)))).symm
    have hA := (center_comap_eqToIso_hom s (hμ j hj1).symm).symm
    have hB := comap_congr_idealSheaf (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j)))) hA
    have hC := comap_congr_idealSheaf (e (s'.nontrivialIndex j) (hle j hj1)).hom hB
    have hD : (s.center (r (s'.nontrivialIndex j))).comap
          ((e (s'.nontrivialIndex j) (hle j hj1)).hom ≫
            pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))))
        = ((s.center (r (s'.nontrivialIndex j))).comap
            (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))))).comap
              (e (s'.nontrivialIndex j) (hle j hj1)).hom := by
      simp [Scheme.IdealSheafData.comap_comp]
    have hE2 : (s.center (s.nontrivialIndex (μ j))).comap
          ((e (s'.nontrivialIndex j) (hle j hj1)).hom ≫
            pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
              (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom)
        = ((s.center (s.nontrivialIndex (μ j))).comap
            (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
              (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom)).comap
                (e (s'.nontrivialIndex j) (hle j hj1)).hom := by
      simp [Scheme.IdealSheafData.comap_comp]
    have hF2 : ((s.center (s.nontrivialIndex (μ j))).comap
          (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
            (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom)).comap
              (e (s'.nontrivialIndex j) (hle j hj1)).hom
        = (((s.center (s.nontrivialIndex (μ j))).comap
            (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom).comap
              (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))))).comap
                (e (s'.nontrivialIndex j) (hle j hj1)).hom := by
      simp [Scheme.IdealSheafData.comap_comp]
    exact (((h7 (s'.nontrivialIndex j) haj).trans hD).trans hC).trans (hE2.trans hF2).symm

end IsPullbackUpToEmptyCenters

end FunctorialResolution.EmbeddedResolution
end

section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace ChartFlatBaseChange

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [AlgebraicGeometry.IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [AlgebraicGeometry.LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

private theorem congr_hom_apply {A B : Scheme.{u}} {f g : A ⟶ B} (e : f = g) (a : A) :
    f a = g a := by
  subst e
  rfl

@[reassoc]
theorem levelMap_succ_comp_transitionMap (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)
    (hσ : F.reindex j ≤ F.reindex (j + 1)) :
    F.levelMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.ambientSeq.transitionMap hσ =
      S'.blowdown j ≫ F.levelMap j (le_of_lt hj) := by
  have hσ' : F.reindex j + 1 ≤ F.reindex (j + 1) := F.reindex_lt_succ j hj
  have key : S.ambientSeq.transitionMap hσ' ≫ S.blowdown (F.reindex j) = S.ambientSeq.transitionMap hσ := by
    rw [show S.blowdown (F.reindex j) = S.ambientSeq.transitionMap (Nat.le_succ (F.reindex j)) from
        S.ambientSeq.blowupMorphism_eq_transitionMap _, S.ambientSeq.transitionMap_trans]
  have hw := (F.isPullback_step j hj hσ').w
  rw [Category.assoc, key] at hw
  exact hw

@[reassoc]
theorem strictTransformComparison_succ_comp_strictTransformMapOfLE (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)
    (hσ : F.reindex j ≤ F.reindex (j + 1)) :
    F.strictTransformComparison (j + 1) (Nat.succ_le_of_lt hj) ≫ S.strictTransformMapOfLE hσ =
      S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) := by
  have : Mono (S.strictTransformι (F.reindex j)) := inferInstance
  rw [← cancel_mono (S.strictTransformι (F.reindex j))]
  have e1 : (F.strictTransformComparison (j + 1) (Nat.succ_le_of_lt hj) ≫ S.strictTransformMapOfLE hσ) ≫
        S.strictTransformι (F.reindex j)
      = S'.strictTransformι (j + 1) ≫ (S'.blowdown j ≫ F.levelMap j (le_of_lt hj)) := by
    rw [Category.assoc, S.strictTransformMapOfLE_strictTransformι, ← Category.assoc, F.strictTransformComparison_comp_strictTransformι,
      Category.assoc, F.levelMap_succ_comp_transitionMap j hj hσ]
  have e2 : (S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj)) ≫ S.strictTransformι (F.reindex j)
      = S'.strictTransformι (j + 1) ≫ (S'.blowdown j ≫ F.levelMap j (le_of_lt hj)) := by
    rw [Category.assoc, F.strictTransformComparison_comp_strictTransformι, ← Category.assoc, S'.strictTransformMap_comp_strictTransformι, Category.assoc]
  rw [e1, e2]

@[reassoc]
theorem inr_totalSpaceMap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    (coprod.inr : S'.detachedCoprod j ⟶ S'.totalSpace j) ≫ F.totalSpaceMap j hj =
      F.inactiveTotalMap j hj ≫
        (coprod.inr : S.detachedCoprod (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  simp [ChartFlatBaseChange.totalSpaceMap]

private theorem totalTransition_comp_totalSpaceMap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length)
    (hσ : F.reindex j ≤ F.reindex (j + 1)) :
    S'.totalTransition j ≫ F.totalSpaceMap j (le_of_lt hj) =
      F.totalSpaceMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.totalMapOfLE hσ := by
  apply coprod.hom_ext
  · have e1 : (coprod.inl : S'.strictTransform (j + 1) ⟶ S'.totalSpace (j + 1)) ≫
          (S'.totalTransition j ≫ F.totalSpaceMap j (le_of_lt hj))
        = S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) ≫ coprod.inl := by
      rw [← Category.assoc, S'.inl_totalTransition, Category.assoc, F.inl_totalSpaceMap]
    have e2 : (coprod.inl : S'.strictTransform (j + 1) ⟶ S'.totalSpace (j + 1)) ≫
          (F.totalSpaceMap (j + 1) (Nat.succ_le_of_lt hj) ≫ S.totalMapOfLE hσ)
        = S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) ≫ coprod.inl := by
      rw [← Category.assoc, F.inl_totalSpaceMap, Category.assoc, S.inl_totalMapOfLE,
        ← Category.assoc, F.strictTransformComparison_succ_comp_strictTransformMapOfLE j hj hσ, Category.assoc]
    rw [e1, e2]
  · apply S'.detachedCoprod_hom_ext (j + 1)
    intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | heq
    · have h1 := F.detachedToCoprod_inr_totalSpaceMap (j + 1) (Nat.succ_le_of_lt hj) s hs
      have h4 := F.detachedToCoprod_inr_totalSpaceMap j (le_of_lt hj) s hlt
      have h2 := S.detachedToCoprod_detachedCoprodMapOfLE (F.reindex_lt_reindex hlt (le_of_lt hj)) hσ
      have h3 := S.detachedCoprodMapOfLE_inr_totalMapOfLE hσ
      have h6 := S'.detachedCoprodInl_inr_totalTransition_assoc j (F.totalSpaceMap j (le_of_lt hj))
      rw [reassoc_of% h1, ← h2]
      rw [S'.detachedToCoprod_succ_of_lt s j hlt]
      simp only [Category.assoc]
      rw [h6, h4, h3]
    · subst heq
      have h1 := F.detachedToCoprod_inr_totalSpaceMap (s + 1) (Nat.succ_le_of_lt hj) s hs
      rw [reassoc_of% h1, S.detachedToCoprod_inr_totalMapOfLE hσ (le_refl (F.reindex s))
          (F.reindex_lt_succ s hj), S.strictTransformMapOfLE_self]
      rw [S'.detachedToCoprod_self s]
      simp only [Category.id_comp]
      rw [S'.detachedCoprodInr_inr_totalTransition_assoc s (F.totalSpaceMap s (le_of_lt hj)),
        F.inl_totalSpaceMap, F.detachedSchemeComparison_comp_detachedι_assoc s hj coprod.inl]

private theorem totalCenter_eq_comap (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y'] (i : ℕ) (hi : i < S'.length) :
    S'.totalCenter i = (S.totalCenter (F.reindex i)).comap (F.totalSpaceMap i hi.le) := by
  apply FunctorialResolution.Blowup.idealSheafData_ext_coprod
  · have l1 : (S'.totalCenter i).comap
        (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i) = S'.centerOffDetached i := by
      rw [S'.totalCenter_eq, FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inl,
        Scheme.IdealSheafData.ker_subschemeι]
    have l2 : (S.totalCenter (F.reindex i)).comap
        (coprod.inl : S.strictTransform (F.reindex i) ⟶ S.totalSpace (F.reindex i))
        = S.centerOffDetached (F.reindex i) := by
      rw [S.totalCenter_eq, FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inl,
        Scheme.IdealSheafData.ker_subschemeι]
    rw [l1, ← Scheme.IdealSheafData.comap_comp, F.inl_totalSpaceMap,
      Scheme.IdealSheafData.comap_comp, l2, ← F.centerOffDetached_eq_comap i hi]
  · have r1 : (S'.totalCenter i).comap
        (coprod.inr : S'.detachedCoprod i ⟶ S'.totalSpace i) = ⊤ := by
      rw [S'.totalCenter_eq]
      exact FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inr _
    rw [r1, ← Scheme.IdealSheafData.comap_comp, F.inr_totalSpaceMap,
      Scheme.IdealSheafData.comap_comp, S.totalCenter_eq,
      FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inr]
    simp

private theorem comap_center_eq_top_of_not_mem_range_reindex (F : ChartFlatBaseChange S S') (h : S.TransitionsAreBlowups) (i : ℕ)
    (hi : i < S.length) (hskip : ∀ j, j < S'.length → F.reindex j ≠ i) :
    ((S.inducedBlowups h).center i).comap (pullback.snd F.baseMap ((S.inducedBlowups h).projectionToBase i)) = ⊤ := by
  rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center]
  apply FunctorialResolution.Blowup.comap_eq_top_of_notMem_support
  intro x hx
  rw [S.totalCenter_eq] at hx
  have hmem : (pullback.snd F.baseMap ((S.inducedBlowups h).projectionToBase i)) x ∈
      closure (Set.range
        (⇑((S.centerOffDetached i).subschemeι ≫
          (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)))) := by
    rw [← Scheme.Hom.support_ker]
    exact hx
  have hrange : Set.range
        (⇑((S.centerOffDetached i).subschemeι ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)))
      ⊆ (⇑(coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) ''
        (↑(S.centerOffDetached i).support : Set (S.strictTransform i)) := by
    rintro y ⟨t, rfl⟩
    refine ⟨(S.centerOffDetached i).subschemeι t, ?_, (Scheme.Hom.comp_apply _ _ t).symm⟩
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self t
  have hce : Topology.IsClosedEmbedding
      (⇑(coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) :=
    AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
  have hsupclosed : IsClosed (↑(S.centerOffDetached i).support : Set (S.strictTransform i)) :=
    (S.centerOffDetached i).support.2
  have hclosed : IsClosed ((⇑(coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) ''
      (↑(S.centerOffDetached i).support : Set (S.strictTransform i))) :=
    hce.isClosedMap _ hsupclosed
  obtain ⟨a, ha, hax⟩ := (closure_minimal hrange hclosed) hmem
  have ha2 : (S.strictTransformι i) a ∈ (↑(S.ambientCenter i).support : Set (S.schemeAt i)) :=
    S.support_centerOffDetached_subset_preimage i ha
  set b := (pullback.fst F.baseMap ((S.inducedBlowups h).projectionToBase i)) x with hb
  have hcond := congr_hom_apply (pullback.condition (f := F.baseMap)
    (g := (S.inducedBlowups h).projectionToBase i)) x
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hcond
  have hstr : ((S.inducedBlowups h).projectionToBase i) ((coprod.inl : S.strictTransform i ⟶ S.totalSpace i) a)
      = (S.strictTransformToBase i) a :=
    congr_hom_apply (FunctorialResolution.EmbeddedResolution.inl_inducedBlowups_projectionToBase S h i) a
  have hemb := congr_hom_apply F.isPullback_emb.w b
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hemb
  have hae := congr_hom_apply (S.strictTransformToBase_emb i) a
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hae
  have hcompat : F.ambientMap (S'.emb b) = (S.ambientSeq.projectionToBase i) ((S.strictTransformι i) a) := by
    rw [← hemb, ← hae, ← hstr, hax, ← hcond]
  obtain ⟨z, hz1, hz2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (S'.emb b) ((S.strictTransformι i) a) hcompat
  have hcs := F.comap_center_skipped i hi (fun j hj => hskip j hj)
    (pullback F.ambientMap (S.ambientSeq.projectionToBase i))
    (pullback.snd F.ambientMap (S.ambientSeq.projectionToBase i))
    (pullback.fst F.ambientMap (S.ambientSeq.projectionToBase i))
    ((IsPullback.of_hasPullback F.ambientMap (S.ambientSeq.projectionToBase i)).flip)
  have hz0 : (pullback.snd F.ambientMap (S.ambientSeq.projectionToBase i)) z ∈
      (S.ambientCenter i).support := by
    rw [hz2]; exact ha2
  have hz : z ∈ ((S.ambientCenter i).comap
      (pullback.snd F.ambientMap (S.ambientSeq.projectionToBase i))).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hz0
  rw [hcs] at hz
  simp at hz
  exact hz

private def inducedBlowupsSchemeAtIsoPullback (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    (S'.inducedBlowups h').schemeAt i ≅ pullback F.baseMap ((S.inducedBlowups h).projectionToBase (F.reindex i)) :=
  ((F.isPullback_totalSpaceMap h h' i
    (by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi)).flip).isoPullback

private theorem inducedBlowupsIso_hom_fst (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    (F.inducedBlowupsSchemeAtIsoPullback h h' i hi).hom ≫ pullback.fst F.baseMap ((S.inducedBlowups h).projectionToBase (F.reindex i))
      = (S'.inducedBlowups h').projectionToBase i :=
  IsPullback.isoPullback_hom_fst _

private theorem inducedBlowupsIso_hom_snd (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    (F.inducedBlowupsSchemeAtIsoPullback h h' i hi).hom ≫ pullback.snd F.baseMap ((S.inducedBlowups h).projectionToBase (F.reindex i))
      = F.totalSpaceMap i (by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi) :=
  IsPullback.isoPullback_hom_snd _

theorem isPullbackUpToEmptyCenters_inducedBlowups (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y']
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) :
    IsPullbackUpToEmptyCenters F.baseMap (S'.inducedBlowups h') (S.inducedBlowups h) := by
  refine ⟨F.reindex, fun i hi => F.inducedBlowupsSchemeAtIsoPullback h h' i hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi ⊢
    exact F.reindex_lt i hi
  · intro i j hj hij
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hj
    exact F.reindex_lt_reindex_of_lt hij hj
  · rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length, FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length]
    exact F.reindex_len
  · intro i hi hns
    have hi' : i < S.length := by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi
    have hskip : ∀ j, j < S'.length → F.reindex j ≠ i := by
      intro j hj he
      exact hns ⟨j, by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length], he⟩
    rintro ⟨x, hx⟩
    rw [F.comap_center_eq_top_of_not_mem_range_reindex h i hi' hskip] at hx
    simp at hx
    exact hx
  · intro i hi
    exact F.inducedBlowupsIso_hom_fst h h' i hi
  · intro i hi hr
    have hi' : i < S'.length := by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi
    apply pullback.hom_ext
    · rw [Category.assoc, F.inducedBlowupsIso_hom_fst, Category.assoc,
        SequenceOfBlowups.pullbackTransitionMap_comp_fst, F.inducedBlowupsIso_hom_fst,
        SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]
    · rw [Category.assoc, F.inducedBlowupsIso_hom_snd, Category.assoc,
        SequenceOfBlowups.pullbackTransitionMap_comp_snd, ← Category.assoc, F.inducedBlowupsIso_hom_snd,
        FunctorialResolution.EmbeddedResolution.inducedBlowups_blowupMorphism, FunctorialResolution.EmbeddedResolution.inducedBlowups_transitionMap]
      exact F.totalTransition_comp_totalSpaceMap i hi' hr
  · intro i hi
    have hi' : i < S'.length := by rwa [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length] at hi
    rw [F.inducedBlowupsIso_hom_snd, FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center, FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center]
    exact F.totalCenter_eq_comap i hi'

theorem isPullbackBlowupSequence_inducedBlowupsWithoutIso (F : ChartFlatBaseChange S S')
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced Y']
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) :
    IsPullbackBlowupSequence F.baseMap (S'.inducedBlowupsWithoutIso h') (S.inducedBlowupsWithoutIso h) :=
  (F.isPullbackUpToEmptyCenters_inducedBlowups h h').isPullbackSequenceOfBlowups_withoutIsoBlowups

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
end
