module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)



def reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) : Transport (reX Z X) u F' where
  wt := T.wt
  wt_isom := T.wt_isom
  wt_e := T.wt_e
  wt_f := T.wt_f
  weight_z := T.weight_z
  ιA := T.ιA
  ιA_rat := T.ιA_rat
  ιA_int := T.ιA_int
  h0 := T.h0
  hc := T.hc
  hc_rep := fun c => by rw [hy]; exact T.hc_rep c
  J := T.J
  J_eqv := T.J_eqv
  J_val := T.J_val
  J_isom := fun c ξ η => by rw [he]; exact T.J_isom c ξ η



theorem colDictL_reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (hK : X.LevelSubgroupCharacter) (x : Cu X u hK) :
    colDictL (reX Z X) (reTr Z T hy he) hK x = colDictL X T hK x := by
  funext c z
  show T.J (shP X u x.1 (T.hc c)) (F'.val0.eY z) = T.J (shP X u x.1 (T.hc c)) (F.val0.eY z)
  rw [he]
  rfl

end GlobalTheory.Mem.SRe

end
