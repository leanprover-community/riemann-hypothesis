import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.Lemmas

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV NumberField

variable {D : D7} {L : SizeData₂ D}

theorem ptB_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ptB D u := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ptB
  exact Finset.prod_nonneg fun τ _ => mul_nonneg (by positivity) (sq_nonneg _)


def PtBSize (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop := ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ptB D u ≤ Real.exp (SZbP D L C u)


def SZKer (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u i (h : (D.fm u).KRat i), i + 1 ≤ D.R.m → Formalism.MainNotions.placeRankTwoOne.kLe D u i h (kernelPlaceMeanBound D L C u (i + 1))

def APlusShape (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ ρ,
    (∀ i i', i ≤ i' → i' < (D.R.sigW j).1 → aPlus D j ρ i' ≤ aPlus D j ρ i) ∧
    ∀ i, D.R.k - 1 ≤ i → i < (D.R.sigW j).1 → aPlus D j ρ i ≤ L.etaSz


theorem ETDef_of {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : ∀ u (i : Fin 2), D.host.g i ≠ (D.mem u).A.T) : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ETDef D u L := by
  intro u w hw
  have hw' : D.what₂.places.resChar w = (D.mem u).A.T := hw
  have hs : D.host.cls (D.what₂.places.resChar w) = PrimeClass.splitK := by
    rw [hw']; exact P.level_split _ (D.T_level u)
  obtain ⟨hg, ht, _⟩ := L.not_inert w (by rw [hs]; exact fun h => by cases h) (by rw [hs]; exact fun h => by cases h)
  refine ⟨ht, fun j hj => ⟨hg j, ?_, ?_⟩⟩
  · rw [hF j hj w]
    unfold Fval FvalP
    have h1 : D.what₂.places.resChar w ∉ L.gTypes := by
      rw [hw']
      simp only [SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hTg u 0 h.symm, fun h => hTg u 1 h.symm⟩
    have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by rw [hs]; exact fun h => by cases h
    have h3 : ¬ ((Formalism.MainNotions.G.IsResidueClassZero D (D.what₂.places.resChar w) ∨ Formalism.MainNotions.G.IsSg D (D.what₂.places.resChar w)) ∧
        (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := by
      rintro ⟨h | h, _⟩
      · exact absurd (hs.symm.trans h) (fun h => by cases h)
      · exact absurd (hs.symm.trans h) (fun h => by cases h)
    rw [if_neg h1, if_neg h2, if_neg h3]
  · rw [hE u j hj w]
    unfold Eval
    simp only [hw', if_true]

end Formalism.MainNotions.J

end
