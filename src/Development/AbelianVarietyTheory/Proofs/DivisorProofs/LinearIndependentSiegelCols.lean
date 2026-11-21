import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnisoClauseOfFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FirstTermIsoCst

def siegelCols (D : D7) (n : ℕ) : Matrix (Fin (n + n)) (Fin n) D.host.E :=
  Matrix.of fun i j => if i = finSumFinEquiv (Sum.inl j) then 1 else 0

variable (D : D7) {n : ℕ}






end GlobalTheory.FirstTermIsoCst

end
