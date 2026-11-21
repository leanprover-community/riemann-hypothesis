import Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticeOfRankSlopeLength
import Formalism.LocalToGlobal.GlobalTheory.GL6.SecondBranchInclLengthOfLengths

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Classical

def ConcreteFormsLevelZero (D : D7) (u : D.what₂.Word) : Prop := FormsTwistCompatibilityFamily D u ∧ product_first_zeroth_parts.admS D u

def FreeTT (D : D7) (u : D.what₂.Word) : Prop := ConcreteFormsLevelZero D u → Nonempty (product_first_zeroth_parts.FreeT D u)

def SlopeLineT (D : D7) (u : D.what₂.Word) : Prop := product_first_zeroth_parts.HidaSetting D u → ConcreteFormsLevelZero D u → product_first_zeroth_parts.SlopeLine D u

def SecondBranchIntegralityUnderForms (D : D7) (u : D.what₂.Word) : Prop :=
  product_first_zeroth_parts.HidaSetting D u → ConcreteFormsLevelZero D u → Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength D u

theorem freeT_of_model {D : D7} {u : D.what₂.Word} (M : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.FreeRankModel (D.mem u).A) :
    Nonempty (product_first_zeroth_parts.FreeT D u) := by
  letI := M.grp
  letI := M.finX
  letI := M.act
  let ph : (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) →* ((D.mem u).A.vT → M.H) :=
    { toFun := fun g v => M.e v (g v)
      map_one' := by
        funext v
        exact (M.e v).map_one
      map_mul' := by
        intro g h
        funext v
        exact (M.e v).map_mul (g v) (h v) }
  letI : MulAction (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) M.X := MulAction.compHom M.X ph
  have hsingle : ∀ v (a : ((D.mem u).A.Fv v)ˣ), ph (Pi.mulSingle v a) = (Pi.mulSingle v (M.e v a) : (D.mem u).A.vT → M.H) := by
    intro v a
    funext w
    by_cases hw : w = v
    · subst hw
      show M.e w ((Pi.mulSingle w a : (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ)) w) = (Pi.mulSingle w (M.e w a) : (D.mem u).A.vT → M.H) w
      simp only [Pi.mulSingle_eq_same]
    · show M.e w ((Pi.mulSingle v a : (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ)) w) = (Pi.mulSingle v (M.e v a) : (D.mem u).A.vT → M.H) w
      first
      | simp [Pi.mulSingle_eq_of_ne hw]
      | (simp only [Pi.mulSingle_eq_of_ne hw]; exact (M.e w).map_one)
  refine ⟨{ X := M.X, Θ := M.E, free := ?_, equiv := ?_ }⟩
  · intro g x hx
    have h1 : ph g = 1 := M.free (ph g) x hx
    funext v
    have h2 : M.e v (g v) = 1 := congrFun h1 v
    first
    | exact (M.e v).map_eq_one_iff.mp h2
    | exact (MulEquiv.map_eq_one_iff (M.e v)).mp h2
  · intro v a φ h x
    rw [M.intertw v a φ h x]
    show M.E φ ((Pi.mulSingle v (M.e v a) : (D.mem u).A.vT → M.H) • x) = M.E φ (ph (Pi.mulSingle v a) • x)
    rw [hsingle]




variable {eps : ℝ}

theorem slope_free_branch_family (Fm : FamP eps) (tT : FamU Fm ConcreteFormsLevelZero) (hWT : ∀ (D : D7) (u : D.what₂.Word), FreeTT D u)
    (hμT : ∀ (D : D7) (u : D.what₂.Word), SlopeLineT D u) (hBT : ∀ (D : D7) (u : D.what₂.Word), SecondBranchIntegralityUnderForms D u) :
    FamU Fm (fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) ∧ FamU Fm product_first_zeroth_parts.SlopeLine ∧ FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength := by
  unfold FamU at tT ⊢
  obtain ⟨x0, hx⟩ := tT
  exact ⟨⟨x0, fun x h0 h1 i u hS => hWT _ u (hx x h0 h1 i u hS)⟩,
    ⟨x0, fun x h0 h1 i u hS => hμT _ u hS (hx x h0 h1 i u hS)⟩,
    ⟨x0, fun x h0 h1 i u hS => hBT _ u hS (hx x h0 h1 i u hS)⟩⟩



end Formalism.MainNotions.RT

end
