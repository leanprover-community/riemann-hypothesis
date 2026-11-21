import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLoc
import Formalism.SharpRestriction.GrowthBounds.DefsInst
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.FrobeniusOrbits

def consts1 : Consts := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩


section InstSec

variable (D : D7) (L : SizeData₂ D)

def bsOf (h t : HH D) : HH D :=
  Quotient.out (QuotientAddGroup.mk t : HH D ⧸ AddSubgroup.zmultiples h)

theorem bsOf_step (h t : HH D) : bsOf D h (t + h) = bsOf D h t := by
  have hq : (QuotientAddGroup.mk (t + h) : HH D ⧸ AddSubgroup.zmultiples h) = QuotientAddGroup.mk t := by
    rw [QuotientAddGroup.eq]
    have e : -(t + h) + t = -h := by abel
    rw [e]
    exact neg_mem (AddSubgroup.mem_zmultiples h)
  unfold bsOf
  rw [hq]

theorem bsOf_orb (h t : HH D) : ∃ i : ℕ, bsOf D h t + i • h = t := by
  have hq : (QuotientAddGroup.mk (bsOf D h t) : HH D ⧸ AddSubgroup.zmultiples h) = QuotientAddGroup.mk t :=
    Quotient.out_eq _
  rw [QuotientAddGroup.eq] at hq
  rw [← mem_multiples_iff_mem_zmultiples] at hq
  obtain ⟨i, hi⟩ := hq
  refine ⟨i, ?_⟩
  simp only at hi
  rw [hi]
  abel

open Classical in

def offOf (_j : ℕ) (z : Bool × HH D) : ℝ :=
  if IsTopPl D z then L.sc.b' / L.sc.x else if IsThickPl D z then L.sc.b else L.sc.w'' D.R.n

def instOf : Inst D L where
  bs := bsOf D
  bs_orb := bsOf_orb D
  bs_step := bsOf_step D
  off := offOf D L
  off_top := fun j z hz => by
    have := L.etaSz_pos
    unfold offOf
    rw [if_pos hz]
    exact ⟨le_rfl, by linarith⟩
  off_thin := fun j z hz => by
    have := L.etaSz_pos
    unfold offOf
    rw [if_neg hz.1, if_neg hz.2]
    exact ⟨le_rfl, by linarith⟩
  off_thick := fun j z hz => by
    have := L.etaSz_pos
    have hnt : ¬ IsTopPl D z := fun ht => by
      have h1 := ht.1
      have h2 := hz.1
      rw [h1] at h2
      exact Bool.false_ne_true h2
    unfold offOf
    rw [if_neg hnt, if_pos hz]
    exact ⟨le_rfl, by linarith⟩
  kapI := fun _ _ _ _ _ => 1
  ep := fun _ => 0



end InstSec

def GatHasPlaces (D : D7) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), 0 < (D.gat u w hg).P.nV

theorem gatHasPlaces_of_ties {D : D7} (hT : GatTies D) : GatHasPlaces D := by
  intro u w hg
  obtain ⟨v, _⟩ := (hT.gat_pos u w hg).symm (D.eTau.symm 1)
  exact lt_of_le_of_lt (Nat.zero_le _) v.isLt

def latOf (D : D7) (h : GatHasPlaces D) : LatInst D where
  vOf := fun u w hg _ => ⟨0, h u w hg⟩
  Fl := fun u w hg => fillsOf (D.gat u w hg) (fun _ => ∅) D.R.t D.R.m
  Lv := fun _ _ _ => levelsOf _
  Ch := fun _ _ _ => chainOf _
  Vram := fun _ _ _ => ⊤



def twLocOf {D : D7} (Y : LatInst D) : Formalism.MainNotions.WeilJacquetShalikaLaw.TwLoc D Y where
  LC := fun _ u w hg => ⟨Y.Lv u w hg, Y.Ch u w hg⟩
  LC_muAt := fun _ _ _ => rfl




end Formalism.MainNotions.G.Inhab

end
