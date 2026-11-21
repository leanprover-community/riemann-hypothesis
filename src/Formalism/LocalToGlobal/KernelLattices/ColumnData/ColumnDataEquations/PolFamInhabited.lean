import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuFinal

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_top (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hSp : Sq.SqSplit B) : B.EqP χ :=
  Sq.eqP_of_split B hcc hδ hδ0 hS χ hχ hSp (Mu.left_move_triangles_hold hcc hδ hδ0 B hS) (Mu.right_move_triangles_hold hcc hδ hδ0 B hS)


end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
