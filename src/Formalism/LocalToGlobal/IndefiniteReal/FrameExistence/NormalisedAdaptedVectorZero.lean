import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormalFrame0
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def betaYOf (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (j : ℕ) : GL (Fin (D.sp.Y j).rank) (EAf D) :=
  if h : j ≤ D.R.m then
    (show GL (Fin (Yc D j).rank) (EAf D) = GL (Fin (D.sp.Y j).rank) (EAf D) by
      unfold Yc; rw [Nat.min_eq_left h]) ▸ βY j
  else 1

open Classical in

def NormalClauses {T : Type} (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βW : ∀ i : Fin D.R.m, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
    (∀ t : T, NormalFrames (betaYOf βY) e ev z κ s (Pg ∪ Q t ∪ Sd) Pg ∧
      NormalFrame0 (betaYOf βY 0) (Pg ∪ Q t ∪ Sd) Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf βY 0) (βW i) eW ι Pg

def SDFrames (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  (∀ j, j < D.R.m → IsSDFrame (Yc D j) (βY j) (ΛY j) (D.host.g 0 * D.host.g 1)) ∧
    IsSDFrame D.sp.X' βX ΛX 1 ∧ (∀ i, IsSDFrame (Vc D i) (βV i) (ΛV i) 1) ∧
    ∀ i, IsSDFrame (Wc D i) (βW i) (ΛW i) 1

variable (D) in
open Classical in

def FramesExist {T : Type} (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E)) : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧ NormalClauses Pg Sd Q βY βW

def baseHyperbolicVector (i : ℕ) : Fin (D.sp.Y 0).rank → D.host.E :=
  if h : i < D.R.rS then ⇑((D.sp.Y 0).frame.repr (D.sp.hypE ⟨i, h⟩)) else 0

def baseDualHyperbolicVector (i : ℕ) : Fin (D.sp.Y 0).rank → D.host.E :=
  if h : i < D.R.rS then ⇑((D.sp.Y 0).frame.repr (D.sp.hypF ⟨i, h⟩)) else 0

def baseLineVector : Fin (D.sp.Y 0).rank → D.host.E := ⇑((D.sp.Y 0).frame.repr D.sp.zm)

def kap0 (i : ℕ) : D.host.E := if i = D.R.rS then -(D.sp.T : D.host.E) else 1

def patchE (e : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E
  | 0 => baseHyperbolicVector
  | j + 1 => e (j + 1)

def patchEv (ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E
  | 0 => baseDualHyperbolicVector
  | j + 1 => ev (j + 1)

def patchZ (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E
  | 0 => baseLineVector
  | j + 1 => z (j + 1)

def patchK (κ : ℕ → ℕ → D.host.E) (j i : ℕ) : D.host.E := if j = 0 then kap0 (D := D) i else κ j i

def patchS (s : ℕ → D.host.E) (j : ℕ) : D.host.E := if j = 0 then 1 else s j

def IsHyperbolicFrameAt (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (j : ℕ) :
    Prop :=
  (∀ i < (D.R.m - 1 - j) / 2, ∀ l < (D.R.m - 1 - j) / 2,
      (D.sp.Y j).hT (vecY j (e j i)) (vecY j (ev j l)) = (if i = l then 1 else 0) ∧
      (D.sp.Y j).hT (vecY j (e j i)) (vecY j (e j l)) = 0 ∧ (D.sp.Y j).hT (vecY j (ev j i)) (vecY j (ev j l)) = 0) ∧
    ((D.R.m - 1 - j) % 2 = 1 →
      (D.sp.Y j).hT (vecY j (z j)) (vecY j (z j)) = -(D.sp.T : D.host.E) ∧
      ∀ i < (D.R.m - 1 - j) / 2,
        (D.sp.Y j).hT (vecY j (z j)) (vecY j (e j i)) = 0 ∧ (D.sp.Y j).hT (vecY j (z j)) (vecY j (ev j i)) = 0) ∧
    ∀ x : (D.sp.X j).V, ∀ i' < D.R.m - 1 - j,
      (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (adaptedVector e ev z j i')) = 0


open Classical in

def ColsAt (βY : ∀ j : ℕ, GL (Fin (D.sp.Y j).rank) (EAf D)) (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E)
    (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E)
    (Pg : Finset (Pl D.host.E)) (PP : Pl D.host.E) (ei : AE D) (j : ℕ) : Prop :=
  (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i →
      ColAt j (βY j).val ei col fun r =>
        (if PP ∈ Pg then ((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) else 1) *
          (nfScal κ s j i * adaptedVector e ev z j i r)) ∧
    (∀ col : Fin (D.sp.Y j).rank, (col.val < D.R.k ∨ D.R.k + (D.R.m - 1 - j) ≤ col.val) →
      XSpanAt j (βY j).val ei col)


theorem vecY_repr (j : ℕ) (v : (D.sp.Y j).V) : vecY (D := D) j ⇑((D.sp.Y j).frame.repr v) = v := by
  simp [vecY]


theorem m_sub_one_div_two : (D.R.m - 1 - 0) / 2 = D.R.rS := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  show (D.R.m - 1 - 0) / 2 = D.R.m / 2 - 1
  omega

theorem m_sub_one_mod_two : (D.R.m - 1 - 0) % 2 = 1 := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  omega


theorem nfScal_patch_zero (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (i : ℕ) :
    nfScal (patchK κ) (patchS s) 0 i = if i ≤ D.R.rS then 1 else -(D.sp.T : D.host.E) := by
  induction i with
  | zero => simp [nfScal, patchS]
  | succ i ih =>
    show patchK κ 0 i * nfScal (patchK κ) (patchS s) 0 i = _
    rw [ih]
    have hk : patchK κ 0 i = kap0 (D := D) i := if_pos rfl
    rw [hk]
    unfold kap0
    split_ifs <;> first | (exfalso; omega) | simp


theorem normalised_adapted_vector_zero (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (i : ℕ) (hi : i < D.R.m - 1) (r : Fin (D.sp.Y 0).rank) :
    nfScal (patchK κ) (patchS s) 0 i * adaptedVector (patchE e) (patchEv ev) (patchZ z) 0 i r = frame0 i r := by
  have hd : (D.R.m - 1 - 0) / 2 = D.R.rS := m_sub_one_div_two
  have hm : (D.R.m - 1 - 0) % 2 = 1 := m_sub_one_mod_two
  rw [nfScal_patch_zero]
  unfold adaptedVector frame0
  rcases lt_trichotomy i D.R.rS with h | h | h
  · rw [if_pos (by omega : i ≤ D.R.rS), if_pos (by omega : i < (D.R.m - 1 - 0) / 2), dif_pos h]
    simp [patchE, baseHyperbolicVector, h]
  · rw [if_pos (by omega : i ≤ D.R.rS), if_neg (by omega : ¬ i < (D.R.m - 1 - 0) / 2),
      if_pos (⟨hm, by omega⟩ : (D.R.m - 1 - 0) % 2 = 1 ∧ i = (D.R.m - 1 - 0) / 2),
      dif_neg (by omega : ¬ i < D.R.rS), if_pos h]
    simp [patchZ, baseLineVector]
  · have hk : D.R.m - 1 - 0 - 1 - i = 2 * D.R.rS - i := by omega
    have h4 : 2 * D.R.rS - i < D.R.rS := by omega
    rw [if_neg (by omega : ¬ i ≤ D.R.rS), if_neg (by omega : ¬ i < (D.R.m - 1 - 0) / 2),
      if_neg (by rintro ⟨-, hc⟩; omega), dif_neg (by omega : ¬ i < D.R.rS), if_neg (by omega : ¬ i = D.R.rS),
      dif_pos h4, hk]
    simp [patchEv, baseDualHyperbolicVector, h4]


open Classical in

theorem colsAt_zero (βY : ∀ j : ℕ, GL (Fin (D.sp.Y j).rank) (EAf D)) (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E)
    (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (S Pg : Finset (Pl D.host.E))
    (h0 : NormalFrame0 (βY 0) S Pg) :
    ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      ColsAt βY (patchE e) (patchEv ev) (patchZ z) (patchK κ) (patchS s) Pg PP ei 0 := by
  have hN : D.R.N 0 = D.R.k := by simp [Formalism.BasicNotions.Ranks.N]
  intro PP hPP ei hei
  obtain ⟨h1, h2⟩ := h0 PP hPP ei hei
  unfold ColsAt
  refine ⟨?_, ?_⟩
  · intro i hi col hcol
    simp only [normalised_adapted_vector_zero e ev z κ s i (by omega)]
    exact h1 i (by omega) col (by rw [hN]; exact hcol)
  · intro col hcol
    rcases hcol with hc | hc
    · exact h2 col (by rw [hN]; exact hc)
    · exfalso
      have hr := D.sp.Y_rank 0 (Nat.zero_le _)
      have hlt := col.isLt
      simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r] at hr
      omega


variable (D) in

def AdaptedVectorsExist : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E),
    ∀ j, 1 ≤ j → j < D.R.m → IsHyperbolicFrameAt e ev z j

open Classical in

def LatFramesExist {T : Type} (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E))
    (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧
    (∀ t : T, (∀ PP ∈ Pg ∪ Q t ∪ Sd, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → ∀ j, 1 ≤ j → j < D.R.m →
        ColsAt (betaYOf βY) e ev z κ s Pg PP ei j) ∧
      NormalFrame0 (betaYOf βY 0) (Pg ∪ Q t ∪ Sd) Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf βY 0) (βW i) eW ι Pg





end Formalism.IndefR.Seed.Frm

end
