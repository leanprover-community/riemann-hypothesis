module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.ResidueEisenstein.ModConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def skewA (σ : E →ₐ[F] E) (j : ℕ) : AddSubgroup (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) where
  carrier := {c | c + cT (sigR (AF F) σ) c = 0}
  add_mem' := fun {a b} ha hb => by
    have e : cT (sigR (AF F) σ) (a + b) = cT (sigR (AF F) σ) a + cT (sigR (AF F) σ) b :=
      Matrix.ext fun i k => by simp [cT]
    change a + b + cT _ (a + b) = 0
    change a + cT _ a = 0 at ha
    change b + cT _ b = 0 at hb
    rw [e, add_add_add_comm, ha, hb, add_zero]
  zero_mem' := by
    change (0 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + cT _ 0 = 0
    ext i k; simp [cT]
  neg_mem' := fun {a} ha => by
    have e : cT (sigR (AF F) σ) (-a) = -cT (sigR (AF F) σ) a := Matrix.ext fun i k => by simp [cT]
    change -a + cT _ (-a) = 0
    change a + cT _ a = 0 at ha
    rw [e, ← neg_add, ha, neg_zero]

theorem mem_skewA {σ : E →ₐ[F] E} {j : ℕ} {c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)} :
    c ∈ skewA σ j ↔ c + cT (sigR (AF F) σ) c = 0 := Iff.rfl

end GlobalTheory.ResidueEisenstein.ModConj

end
