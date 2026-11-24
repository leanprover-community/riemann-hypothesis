module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PWOfInW
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HSumRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InWLeft
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

theorem h_e_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (X.eX c) (nL X X0 xs M w) = 0 := by
  rw [nL_w X X0 xs M hw, map_add (f := _), h_sum_right]
  simp [(hw c).1, X.ee]

theorem h_f_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (X.fY c) (nL X X0 xs M w) = (VS D).hT (xs c) w := by
  rw [nL_w X X0 xs M hw, map_add (f := _), h_sum_right]
  simp [(hw c).2, h_fe, Finset.sum_ite_eq]

theorem h_xs_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (xs c) (nL X X0 xs M w) = (VS D).hT (xs c) w := by
  rw [nL_w X X0 xs M hw, map_add (f := _), h_sum_right]
  simp [(inW_left X (hxs c) _).1]

theorem g_ew (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT (nE X X0 a) (nL X X0 xs M w) = (VS D).hT (X.eX a) w := by
  rw [h_nE_left, (hw a).1]
  simp [h_e_nLw X X0 xs M hxs hw]

theorem g_fw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT (nF X X0 xs M a) (nL X X0 xs M w) = (VS D).hT (X.fY a) w := by
  rw [h_nF_left, (hw a).2]
  simp [h_e_nLw X X0 xs M hxs hw, h_f_nLw X X0 xs M hxs hw, h_xs_nLw X X0 xs M hxs hw]

theorem g_ww (hxs : ∀ b, InW X (xs b)) {w w' : (VS D).V} (hw : InW X w) (hw' : InW X w') :
    (VS D).hT (nL X X0 xs M w) (nL X X0 xs M w') = (VS D).hT w w' := by
  rw [nL_w X X0 xs M hw, nL_w X X0 xs M hw', LinearMap.map_add₂, map_add (f := _), map_add (f := _), h_sum_left, h_sum_left,
    h_sum_right]
  simp [(hw' _).1, (inW_left X hw _).1, X.ee]

theorem iso_gen_left (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs)
    (g : (VS D).V) (hg : ∀ c, (VS D).hT (nL X X0 xs M g) (nL X X0 xs M (X.eX c)) = (VS D).hT g (X.eX c) ∧
      (VS D).hT (nL X X0 xs M g) (nL X X0 xs M (X.fY c)) = (VS D).hT g (X.fY c))
    (hgw : ∀ w, InW X w → (VS D).hT (nL X X0 xs M g) (nL X X0 xs M w) = (VS D).hT g w) (y : (VS D).V) :
    (VS D).hT (nL X X0 xs M g) (nL X X0 xs M y) = (VS D).hT g y := by
  conv_lhs => rw [decomp X y]
  conv_rhs => rw [decomp X y]

  simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul]
  rw [hgw _ (inW_pW X y)]
  simp only [(hg _).1, (hg _).2]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
