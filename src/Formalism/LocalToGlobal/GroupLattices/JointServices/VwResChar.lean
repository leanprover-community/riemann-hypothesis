module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.MirabolicMackeyTheory.StatementT
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.NumbersP
public import Formalism.LocalToGlobal.GroupLattices.JointServices.VAddEqVw
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataAmbForm

@[expose] public section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV

noncomputable section

namespace Formalism.L2.G.ServJoint

theorem vw_resChar (D : D7) (w : D.what₂.places.Pl) :
    Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
  have hp0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D.what₂.places.resChar_prime w).ne_zero
  have h1 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hp0, vAdd_eq_vw _ _ hp0] at h1
  exact_mod_cast h1

theorem plc_plEq (D : D7) (w : D.what₂.places.Pl) : Formalism.EigenvalueLevelCeiling.plc (D.plEq w) = D.what₂.places.resChar w := by
  by_contra hne
  have h0 := Formalism.L2.DIV.vw_prime_eq_zero (D.plEq w) (D.what₂.places.resChar_prime w) (fun h => hne h.symm)
  rw [vw_resChar] at h0
  have := D.what₂.places.ramIdx_pos w
  omega

end Formalism.L2.G.ServJoint

end
