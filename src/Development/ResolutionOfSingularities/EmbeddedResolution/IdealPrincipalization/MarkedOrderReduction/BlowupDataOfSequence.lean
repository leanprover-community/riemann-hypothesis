module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Mathlib.Tactic.Linter.Style

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isPullbackBlowupSequence_congr (F : PrincipalizationAssignment.{u})
    {k₁ k₂ : Type u} [Field k₁] [Field k₂] {B Q : Scheme.{u}}
    (pB : B ⟶ Spec (CommRingCat.of k₁)) (IB : B.IdealSheafData) (mB : ℕ)
    (EB : List B.IdealSheafData) (q : Q ⟶ B)
    (pQ₁ pQ₂ : Q ⟶ Spec (CommRingCat.of k₂)) (IQ₁ IQ₂ : Q.IdealSheafData) (mQ₁ mQ₂ : ℕ)
    (EQ₁ EQ₂ : List Q.IdealSheafData)
    (hp : pQ₁ = pQ₂) (hI : IQ₁ = IQ₂) (hm : mQ₁ = mQ₂) (hE : EQ₁ = EQ₂)
    (h : IsPullbackBlowupSequence q (F (MarkedIdealWithBoundary.mk k₂ Q pQ₁ IQ₁ mQ₁ EQ₁)).toSequenceOfBlowups
        (F (MarkedIdealWithBoundary.mk k₁ B pB IB mB EB)).toSequenceOfBlowups) :
    IsPullbackBlowupSequence q (F (MarkedIdealWithBoundary.mk k₂ Q pQ₂ IQ₂ mQ₂ EQ₂)).toSequenceOfBlowups
      (F (MarkedIdealWithBoundary.mk k₁ B pB IB mB EB)).toSequenceOfBlowups := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact h

theorem BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length = s.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length]
  rfl

theorem BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups {X : Scheme.{u}} (t : SequenceOfBlowups X) (j : ℕ) :
    (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.projectionToBase j = t.projectionToBase j :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase (BlowupSequenceData.ofSequenceOfBlowups t) j).trans (BlowupSequenceData.ofSequenceOfBlowups_projectionToBase t j)

namespace SequenceOfBlowupsPullback

variable {X X' : Scheme.{u}} {φ : X' ⟶ X} {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}

def ofSequenceOfBlowupsMap (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.schemeAt j ⟶ (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt (c.idx j) :=
  eqToHom (rfl : _ = s'.schemeAt j) ≫ c.map j hj ≫ eqToHom (rfl : s.schemeAt _ = _)

theorem index_ofSequenceOfBlowups_length (c : SequenceOfBlowupsPullback φ s' s) :
    c.idx (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length = (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s]
  exact c.idx_length

theorem index_lt_ofSequenceOfBlowups_length (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length →
      c.idx j < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact c.idx_lt j hj

theorem index_lt_index_succ_of_lt_length_ofSequenceOfBlowups (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
  exact c.idx_strictMono j hj

private theorem ofSequenceOfBlowups_map_eq (c : SequenceOfBlowupsPullback φ s' s) (j : ℕ)
    (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    ofSequenceOfBlowupsMap c j hj = c.map j hj := by
  show 𝟙 _ ≫ c.map j hj ≫ 𝟙 _ = c.map j hj
  simp

theorem isPullback_projectionToBase_ofSequenceOfBlowups (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j ≤ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      IsPullback (ofSequenceOfBlowupsMap c j hj) ((BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.projectionToBase j)
        ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.projectionToBase (c.idx j)) φ := by
  intro j hj
  rw [ofSequenceOfBlowups_map_eq,
    BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups,
    BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups]
  exact c.isPullback j hj

private theorem ofSequenceOfBlowups_transitionMap {W : Scheme.{u}} (t : SequenceOfBlowups W)
    {i i' : ℕ} (h : i ≤ i') :
    (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMap h =
      t.transitionMap h := by
  induction i', h using Nat.le_induction with
  | base =>
    rw [SequenceOfBlowups.transitionMap_self_eq_id, SequenceOfBlowups.transitionMap_self_eq_id]
    rfl
  | succ m hm ih =>
    rw [← SequenceOfBlowups.transitionMap_trans _ hm (Nat.le_succ m),
      ← SequenceOfBlowups.blowupMorphism_eq_transitionMap,
      BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
    show t.transitionMapSucc m ≫
      (BlowupSequenceData.ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMap hm = _
    rw [ih, SequenceOfBlowups.blowupMorphism_eq_transitionMap]
    exact SequenceOfBlowups.transitionMap_trans t hm (Nat.le_succ m)

theorem ofSequenceOfBlowups_blowupMorphism_comp_map (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.transitionMapSucc j ≫ ofSequenceOfBlowupsMap c j (le_of_lt hj) =
        ofSequenceOfBlowupsMap c (j + 1) hj ≫
          (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (le_of_lt (index_lt_index_succ_of_lt_length_ofSequenceOfBlowups c j hj)) := by
  intro j hj
  have hlt : j < s'.length := by
    have h := hj
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at h
    exact h
  rw [ofSequenceOfBlowups_map_eq c j (le_of_lt hj), ofSequenceOfBlowups_map_eq c (j + 1) hj,
    ofSequenceOfBlowups_transitionMap, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
  exact c.step j hlt

theorem center_ofSequenceOfBlowups_eq_comap (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ (j : ℕ) (hj : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length),
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.center j =
        ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.center (c.idx j)).comap (ofSequenceOfBlowupsMap c j (le_of_lt hj)) := by
  intro j hj
  rw [ofSequenceOfBlowups_map_eq]
  exact c.center_comap j hj

theorem center_ofSequenceOfBlowups_ne_top (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length →
      (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.center j ≠ ⊤ := by
  intro j hj
  have hj' : j < s'.length := lt_of_lt_of_le hj (le_of_eq (BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s'))
  exact c.center_ne_top j hj'

theorem ofSequenceOfBlowups_ne_of_mem_unmatched_center (c : SequenceOfBlowupsPullback φ s' s) :
    ∀ i : ℕ, i < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length →
      (∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j ≠ i) →
      ∀ z : ↥((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt i),
        z ∈ ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ ((BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.projectionToBase i).base z := by
  intro i hi hmiss z hz x'
  have hi' : i < s.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hi
    exact hi
  have hmiss' : ∀ j : ℕ, j < s'.length → c.idx j ≠ i := by
    intro j hj
    refine hmiss j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have h := c.omitted i hi' hmiss' z hz x'
  rw [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i]
  exact h

def toBlowupDataOfSeq (c : SequenceOfBlowupsPullback φ s' s) :
    SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups where
  idx := c.idx
  map := ofSequenceOfBlowupsMap c
  idx_length := index_ofSequenceOfBlowups_length c
  idx_lt := index_lt_ofSequenceOfBlowups_length c
  idx_strictMono := index_lt_index_succ_of_lt_length_ofSequenceOfBlowups c
  isPullback := isPullback_projectionToBase_ofSequenceOfBlowups c
  step := ofSequenceOfBlowups_blowupMorphism_comp_map c
  center_comap := center_ofSequenceOfBlowups_eq_comap c
  center_ne_top := center_ofSequenceOfBlowups_ne_top c
  omitted := ofSequenceOfBlowups_ne_of_mem_unmatched_center c

def transportedMap
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) : s'.schemeAt j ⟶ s.schemeAt (c.idx j) :=
  eqToHom (rfl : s'.schemeAt j = _) ≫ c.map j hj ≫ eqToHom (rfl : _ = s.schemeAt (c.idx j))

theorem ofSequenceOfBlowups_index_length
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    c.idx s'.length = s.length := by
  have h := c.idx_length
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s] at h
  exact h

theorem ofSequenceOfBlowups_index_lt_length
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ j : ℕ, j < s'.length → c.idx j < s.length := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have h := c.idx_lt j hj'
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at h
  exact h

theorem index_lt_index_succ_of_lt_length
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ j : ℕ, j < s'.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  refine c.idx_strictMono j ?_
  rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
  exact hj

private theorem transportedMap_eq_map
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups)
    (j : ℕ) (hj : j ≤ s'.length) :
    transportedMap c j hj = c.map j hj := by
  show 𝟙 _ ≫ c.map j hj ≫ 𝟙 _ = c.map j hj
  simp

theorem isPullback_transportedMap
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ (j : ℕ) (hj : j ≤ s'.length),
      IsPullback (transportedMap c j hj) (s'.projectionToBase j) (s.projectionToBase (c.idx j)) φ := by
  intro j hj
  rw [transportedMap_eq_map,
    ← BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s' j,
    ← BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s (c.idx j)]
  exact c.isPullback j hj

theorem blowupMorphism_comp_map_of_ofSequenceOfBlowups
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ (j : ℕ) (hj : j < s'.length),
      s'.transitionMapSucc j ≫ transportedMap c j (le_of_lt hj) =
        transportedMap c (j + 1) hj ≫ s.transitionMap (le_of_lt (index_lt_index_succ_of_lt_length c j hj)) := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  have key := c.step j hj'
  rw [ofSequenceOfBlowups_transitionMap,
    BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at key
  rw [transportedMap_eq_map c j (le_of_lt hj), transportedMap_eq_map c (j + 1) hj]
  exact key

theorem center_eq_comap_transportedMap
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ (j : ℕ) (hj : j < s'.length),
      s'.center j = (s.center (c.idx j)).comap (transportedMap c j (le_of_lt hj)) := by
  intro j hj
  rw [transportedMap_eq_map]
  exact c.center_comap j hj

theorem center_ne_top_of_pullback_ofSequenceOfBlowups
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ j : ℕ, j < s'.length → s'.center j ≠ ⊤ := by
  intro j hj
  have hj' : j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  exact c.center_ne_top j hj'

theorem ofSequenceOfBlowups_projectionToBase_ne
    (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    ∀ i : ℕ, i < s.length → (∀ j : ℕ, j < s'.length → c.idx j ≠ i) →
      ∀ z : ↥(s.schemeAt i), z ∈ (s.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ (s.projectionToBase i).base z := by
  intro i hi hmiss z hz x'
  have hi' : i < (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hi
  have hmiss' : ∀ j : ℕ, j < (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j ≠ i := by
    intro j hj
    refine hmiss j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
    exact hj
  have h := c.omitted i hi' hmiss' z hz x'
  rw [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i] at h
  exact h

def ofBlowupDataOfSeq (c : SequenceOfBlowupsPullback φ (BlowupSequenceData.ofSequenceOfBlowups s').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups) :
    SequenceOfBlowupsPullback φ s' s where
  idx := c.idx
  map := transportedMap c
  idx_length := ofSequenceOfBlowups_index_length c
  idx_lt := ofSequenceOfBlowups_index_lt_length c
  idx_strictMono := index_lt_index_succ_of_lt_length c
  isPullback := isPullback_transportedMap c
  step := blowupMorphism_comp_map_of_ofSequenceOfBlowups c
  center_comap := center_eq_comap_transportedMap c
  center_ne_top := center_ne_top_of_pullback_ofSequenceOfBlowups c
  omitted := ofSequenceOfBlowups_projectionToBase_ne c

end SequenceOfBlowupsPullback

end FunctorialResolution.EmbeddedResolution

end
