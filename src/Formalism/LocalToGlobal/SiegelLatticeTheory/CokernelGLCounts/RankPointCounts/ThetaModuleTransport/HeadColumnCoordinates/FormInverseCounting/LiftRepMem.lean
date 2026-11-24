module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SumMapCompSub
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem supp_inl (Y : Ix r → O) (h : ∀ a : Fin r, Y (Sum.inl a.castSucc) = 0) :
    (fun j => Y (Sum.inl j)) = Y (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast a => simp [h a]

theorem supp_inr (Y : Ix r → O) (h : ∀ a : Fin r, Y (Sum.inr a.castSucc) = 0) :
    (fun j => Y (Sum.inr j)) = Y (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast a => simp [h a]

theorem elim_eta (Y : Ix r → O) : Y = Sum.elim (fun j => Y (Sum.inl j)) (fun j => Y (Sum.inr j)) := by
  funext i
  cases i <;> rfl

theorem lift_e_mem {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z →ₗ[O] MbMod Z')
    (he : f (eCl Z) = eCl Z') (s : O) :
    liftOf O f (s • Pi.single (Fin.last r) 1) - s • Pi.single (Fin.last r) 1 ∈ headCols Z' := by
  rw [← Submodule.Quotient.eq, liftOf_spec, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul]
  exact congrArg (s • ·) he

theorem lift_rep_mem {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z ≃ₗ[O] MbMod Z')
    (y : Fin (r + 1) → O) (y₂ : Fin (r + 1) → O)
    (hy : (Submodule.Quotient.mk y : MbMod Z) = f.symm (Submodule.Quotient.mk y₂)) :
    liftOf O f.toLinearMap y - y₂ ∈ headCols Z' := by
  rw [← Submodule.Quotient.eq, liftOf_spec, hy, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
