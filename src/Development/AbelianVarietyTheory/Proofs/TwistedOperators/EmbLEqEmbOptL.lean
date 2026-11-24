module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.PackLoc

def embOpt {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (h : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => h i j
    | none, none => 1
    | _, _ => 0

def embOptL {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (X : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => X i j
    | _, _ => 0

theorem embH_eq_embOpt {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (h : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embH e h = embOpt e h := rfl

theorem embL_eq_embOptL {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (X : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embL e X = embOptL e X := rfl

theorem embOpt_one {m N : ℕ} (e : Option (Fin m) ≃ Fin N) : embOpt e 1 = 1 := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Matrix.one_apply]

end GlobalTheory.PackLoc

end
