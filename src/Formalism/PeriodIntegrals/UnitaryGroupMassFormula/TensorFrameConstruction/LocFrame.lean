module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorFrameConstruction.LocalFramePreservesOrthogonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Lemma
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

open Matrix NumberField

namespace PI.ScPiBuildW.Rv

open PI.ScPiExists

lemma phi_star (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (a : I.E) :
    I.φ v (star a) = star (I.φ v a) := by
  exact I.cm.cmUnram.2.1 (I.φ v) a

lemma hJ_rv (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  apply PI.ScPiFrameW.hJ_rv <;> assumption

lemma phi_ite (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {r : ℕ} (a b : Fin r) :
    I.φ v (if a = b then (1 : I.E) else 0) = if a = b then 1 else 0 := by
  split_ifs <;> simp

def locFrame (I : Formalism.MainNotions.S.AutInst) {r k : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (hn : I.n = 2 * r + k + 1) (hF : IsFrame I e f z)
    (hz : Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0) (v : InfinitePlace I.F) (w : Fin k → Fin I.n → ℂ)
    (hw : (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0) :
    Loc.LocFrame I.n r k (I.ε v) where
  e := fun a => rv I v (e a)
  f := fun a => rv I v (f a)
  z := rv I v z
  w := w
  hn := hn
  ee := fun a b => by rw [hJ_rv, hF.1 a b, map_zero]
  ef := fun a b => by rw [hJ_rv, hF.2.2.1 a b, phi_ite]
  ez := fun a => by rw [hJ_rv, (hF.2.2.2 a).1, map_zero]
  fz := fun a => by rw [hJ_rv, (hF.2.2.2 a).2, map_zero]
  zz := by rw [hJ_rv]; exact (map_ne_zero (I.φ v)).2 hz
  ww := hw.1
  ew := fun c a => ((hw.2 a).1 c).1
  fw := fun c a => ((hw.2 a).1 c).2
  zw := fun a => (hw.2 a).2

section Simp

variable (I : Formalism.MainNotions.S.AutInst) {r k : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
  (hn : I.n = 2 * r + k + 1) (hF : IsFrame I e f z)
  (hz : Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0) (v : InfinitePlace I.F) (w : Fin k → Fin I.n → ℂ)
  (hw : (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0)

end Simp

end PI.ScPiBuildW.Rv
