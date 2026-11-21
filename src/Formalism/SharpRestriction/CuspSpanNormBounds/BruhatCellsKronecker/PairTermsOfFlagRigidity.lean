import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusProjectedBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HS

variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]



end HS

section Sizes

variable (D : D7) (large₂ : SizeData₂ D)













end Sizes

section B

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {C' Cl Cg cb Cu cT CT C0 : ℝ}

theorem q_split (hH : FrobeniusProjectedBounds.Hyp D large₂ C' Cl Cg cb Cu cT CT C0) (h1 : FrobeniusProjectedBounds.adm1 D large₂ C' Cl Cg cb Cu cT CT C0)
    (ha : FrobeniusProjectedBounds.Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0) (u : D.what₂.Word) :
    Kmat D.s u u - FrobeniusProjectedBounds.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u) =
      KOf D.s u u (famNG D.s) + KOf D.s u u (famG D.s) := by
  classical
  obtain ⟨hE, _⟩ := h1 hH u u
  obtain ⟨c1, c2, c3, _, c5, _, _, _⟩ := ha hH u
  have hs : Summable (fun t => D.s.aTerm u u t) := hE.summable
  set a : D.s.Term u u → (D.s.Cu u →L[ℂ] D.s.Cu u) := fun t => D.s.aTerm u u t with ha'
  have i1 : ({t | D.s.inS t} : Set (D.s.Term u u)).indicator a = ({t | D.s.isId t} : Set (D.s.Term u u)).indicator a := by
    funext t
    by_cases hi : D.s.isId t
    · simp [Set.indicator, hi, c2 t hi]
    · by_cases hS : D.s.inS t
      · have hr : ¬ D.s.relevant t := fun hr => hi (c3 t hS hr)
        simp [Set.indicator, hi, hS, ha', c5 t hr]
      · simp [Set.indicator, hi, hS]
  have s1 : HasSum (({t | D.s.isId t} : Set (D.s.Term u u)).indicator a) (ContinuousLinearMap.id ℂ (D.s.Cu u)) := by
    rw [← i1]
    exact (hasSum_subtype_iff_indicator (s := {t | D.s.inS t})).1 c1
  have sS : ∀ S : Set (D.s.Term u u), HasSum (S.indicator a) (KOf D.s u u S) := fun S =>
    (hasSum_subtype_iff_indicator (s := S)).1 (hs.subtype S).hasSum
  have s2 := sS {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}
  have s3 := sS (famNG D.s)
  have s4 := sS (famG D.s)
  have e : (fun t => ({t | D.s.isId t} : Set (D.s.Term u u)).indicator a t +
      ({t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} : Set (D.s.Term u u)).indicator a t +
      (famNG D.s : Set (D.s.Term u u)).indicator a t + (famG D.s : Set (D.s.Term u u)).indicator a t) = a := by
    funext t
    by_cases hi : D.s.isId t
    · simp [Set.indicator, famNG, famG, hi]
    · by_cases hG : D.s.Gterm t = 0
      · simp [Set.indicator, famNG, famG, hi, hG]
      · by_cases hg : D.s.generic t
        · simp [Set.indicator, famNG, famG, hi, hG, hg]
        · simp [Set.indicator, famNG, famG, hi, hG, hg]
  have tot := ((s1.add s2).add s3).add s4
  rw [e] at tot
  have := hE.unique tot
  rw [this]
  unfold FrobeniusProjectedBounds.Kpp
  abel




end B

section Fam

variable {eps : ℝ} (Fm : FamP eps)


end Fam

section FlagsGen

open Formalism.MainNotions.S.Lat Module

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}





def InSF {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  (∀ a : Fin r, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) ∧ F'.fl.z - F.fl.z ∈ Xsp F








def Shape {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (c : Fin r → E) (ζ : E) : Prop :=
  (∀ a, c a ≠ 0) ∧ (∀ a : Fin r, F'.fl.e a - c a • F.fl.e a ∈ Xflag F a.val) ∧ F'.fl.z - ζ • F.fl.z ∈ Xsp F



end FlagsGen

section A

open Formalism.MainNotions.S.Lat Module

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {C' Cl Cg cb Cu cT CT C0 : ℝ}







def FlagRigid (D : D7) (X : TermTie D) : Prop :=
  ∀ (u : D.what₂.Word) (t : D.s.Term u u), FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t) → D.s.relevant t → D.s.isId t

def RelScal (D : D7) (X : TermTie D) : Prop :=
  ∀ (u : D.what₂.Word) (t : D.s.Term u u) (c : Fin D.R.rS → D.host.E) (ζ : D.host.E),
    Shape (X.fl t) (X.fl' t) c ζ → D.s.relevant t → ∀ a, c a = ζ

def ZetaOne (D : D7) (X : TermTie D) : Prop :=
  ∀ (u : D.what₂.Word) (t : D.s.Term u u) (c : Fin D.R.rS → D.host.E) (ζ : D.host.E),
    Shape (X.fl t) (X.fl' t) c ζ → ζ = 1

def UnipExt (D : D7) (X : TermTie D) : Prop :=
  ∀ (u : D.what₂.Word) (t : D.s.Term u u), InSF (X.fl t) (X.fl' t) → D.s.isId t



end A

end Formalism.MainNotions.BridgeLemma

end
