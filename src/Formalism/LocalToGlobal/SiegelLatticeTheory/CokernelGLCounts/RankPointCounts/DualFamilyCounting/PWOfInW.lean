module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InWLeft
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
import Mathlib.Tactic.NormNum.Prime
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

def Ym : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := (X0⁻¹)ᴴ

def om (a : Fin D.R.rS) : (VS D).V := -∑ b, Ym X0 b a • xs b

def nE (a : Fin D.R.rS) : (VS D).V := ∑ b, X0 b a • X.eX b

def nF (a : Fin D.R.rS) : (VS D).V := ∑ c, Ym X0 c a • X.fY c + om X0 xs a + ∑ b, (X0 * M) b a • X.eX b

def nWL : (VS D).V →ₗ[D.host.E] (VS D).V := LinearMap.id + ∑ b, ((VS D).hT (xs b)).smulRight (X.eX b)

def pWL : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ c, ((VS D).hT (X.fY c)).smulRight (X.eX c) - ∑ c, ((VS D).hT (X.eX c)).smulRight (X.fY c)

theorem pWL_apply (y : (VS D).V) : pWL X y = pW X y := by
  simp [pWL, pW, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

def nL : (VS D).V →ₗ[D.host.E] (VS D).V :=
  ∑ c, ((VS D).hT (X.fY c)).smulRight (nE X X0 c) + ∑ c, ((VS D).hT (X.eX c)).smulRight (nF X X0 xs M c) +
    (nWL X xs).comp (pWL X)

theorem nL_apply (y : (VS D).V) : nL X X0 xs M y =
    ∑ c, (VS D).hT (X.fY c) y • nE X X0 c + ∑ c, (VS D).hT (X.eX c) y • nF X X0 xs M c +
      (pW X y + ∑ b, (VS D).hT (xs b) (pW X y) • X.eX b) := by
  simp [nL, nWL, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply, pWL_apply]

theorem pW_of_inW {w : (VS D).V} (hw : InW X w) : pW X w = w := by
  unfold pW
  simp [(hw _).1, (hw _).2]

theorem pW_e (a : Fin D.R.rS) : pW X (X.eX a) = 0 := by
  unfold pW
  simp [h_fe, X.ee, Finset.sum_ite_eq']

theorem pW_f (a : Fin D.R.rS) : pW X (X.fY a) = 0 := by
  unfold pW
  simp [X.ef, X.ff, Finset.sum_ite_eq']

theorem nL_e (a : Fin D.R.rS) : nL X X0 xs M (X.eX a) = nE X X0 a := by
  rw [nL_apply, pW_e]
  simp [h_fe, X.ee, Finset.sum_ite_eq']

theorem nL_f (a : Fin D.R.rS) : nL X X0 xs M (X.fY a) = nF X X0 xs M a := by
  rw [nL_apply, pW_f]
  simp [X.ef, X.ff, Finset.sum_ite_eq']

theorem nL_w {w : (VS D).V} (hw : InW X w) : nL X X0 xs M w = w + ∑ b, (VS D).hT (xs b) w • X.eX b := by
  rw [nL_apply, pW_of_inW X hw]
  simp [(hw _).1, (hw _).2]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
