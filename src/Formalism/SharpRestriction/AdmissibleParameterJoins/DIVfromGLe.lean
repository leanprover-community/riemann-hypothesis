import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV

def RankHyp (D : D7) : Prop :=
  StandardLattice.GBig D ∧ (∀ i, StandardLattice.SplitsF D (D.host.g i)) ∧
    ∀ u : D.what₂.Word, StandardLattice.SplitsF D (D.mem u).A.T ∧ StandardLattice.Mu0Tie D u

def CountTie (D : D7) : Prop :=
  (∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u) ∧ D.what₂.Dstar = StandardLattice.DstarD D




end Formalism.MainNotions.J
