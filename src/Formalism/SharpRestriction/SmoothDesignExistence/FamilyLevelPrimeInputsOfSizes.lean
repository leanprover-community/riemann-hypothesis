import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLl
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold
import Formalism.SharpRestriction.SmoothDesignExistence.LatticeIndexTer
import Formalism.SharpRestriction.SmoothDesignExistence.WithSmOfWithCh
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLw

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions Formalism.BasicNotions.DV

section Family

variable {eps : ℝ} (Fm : FamP eps)

structure BrT : Prop where

  t5Tw : DIV.Ev Fm fun x hx i => J.LevelPrimeColumnOtherTuples (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

  tg : DIV.Ev Fm fun x _ i => WeightDegreeSizes.LevelPrimeNotTypePrime (Fm.D x i)

variable {Fm}


theorem servedModel_of_params {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (X : G.Inst D L) (K : G.Consts)
    (h3 : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) : WeightDegreeSizes.ServedHasModel X K := by
  intro u w hw hVV
  have hc : G.Cand D L K (D.what₂.places.resChar w) := by
    by_contra hn
    apply hVV
    unfold G.VV
    rw [if_neg (fun h => hn h.1)]
  exact gIdx_of_cand P K h3 u _ hc hw






theorem vanishing_above_threshold : DIV.Ev Fm fun x _ i => LocalQuadraticParts.ZeroGainAbove (Fm.L x i) := by
  unfold DIV.Ev
  refine ⟨0, fun x _ hx i => J.gains_losses_eq_defined (Fm.Gx x i) Fm.GK _ _ (Fm.fills x hx i) (Fm.ex x hx i).err.edef⟩


end Family

end Formalism.MainNotions.Pk

end
