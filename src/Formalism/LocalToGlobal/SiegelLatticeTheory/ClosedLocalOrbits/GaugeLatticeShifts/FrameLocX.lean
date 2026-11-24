module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameWZeroExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
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
import Mathlib.Tactic.Basify

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem frameLoc_X (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    FrameLoc (X.B.I.ε v) D.R.k (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
      (Tw u) (Tw u') := by
  refine
    { dim := (Formalism.L2.SG.Pf.card_frame X).symm
      k_pos := by have := D.R.m_add_three_le_k; omega
      sig := Formalism.L2.SG.PoincareInHH.Cut.card_eps_false X v
      e_li := ?_
      ee := fun a b => (hJ_X X v _ _).trans (by rw [X.ee]; simp)
      ez := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
      ez' := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u' a).1]; simp)
      zz := (hJ_X X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
      zz' := (hJ_X X v _ _).trans (by rw [X.zu_norm u']; simp [Tw])
      T_pos := Tw_pos u
      T'_pos := Tw_pos u' }
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
  rw [hJ_fsum_r] at h
  have hfe : ∀ i, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR i)) = if i = j then 1 else 0 :=
    fun i => (hJ_X X v _ _).trans (by rw [Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X]; split_ifs <;> simp)
  simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [h]
  unfold hJ
  simp

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
