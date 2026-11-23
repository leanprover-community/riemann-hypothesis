module

public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.HermitianForms.BothSym
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormsTiedSym.to0 {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : FormsTiedSym D u Ch chOf) : Forms0 D u where
  atT := T.atT
  cls0 := T.cls 0 (Nat.zero_le _) (Or.inl rfl)
  val0 := T.val 0 (Nat.zero_le _) (Or.inl rfl)
  gl := T.gl
  gl_K := T.gl_K
  glev0 := T.glev0
  lv0 := T.lv 0 (Nat.zero_le _)
  fMe0 := T.fMe 0 (Nat.zero_le _) (Or.inl rfl)
  fv0 := T.fv 0 (Nat.zero_le _) (Or.inl rfl)
  up_natural_level_zero := T.upN 0 (Nat.zero_le _) (Or.inl rfl)
  down_natural_level_zero := T.dnN 0 (Nat.zero_le _) (Or.inl rfl)
  norm0 := T.norm 0 (Nat.zero_le _) (Or.inl rfl)
  bw0 := T.bw 0 (Nat.zero_le _) (Or.inl rfl)

theorem ColsTiedSym.joint0 {D : D7} (C : ColsTiedSym D) (u : D.what₂.Word) :
    Joint0 C.herm.base.lev0 u (C.forms u).to0 := C.car0 u

end Formalism.L2.Forms
