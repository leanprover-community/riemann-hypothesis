module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

def FlagConcl (v : Valuation C NNReal) (p : ℕ) (M : Submodule R (N → C)) {n : ℕ}
    (b : Module.Basis (Fin n) F N) (σ : MulChar F R) : Prop :=
  ∃ c δ : Fin n → ℕ → R,
    (∀ i s, c i s ≠ 0 ∧
      idealX M (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} ∧
      xIdeal (stepOrderRes M (flagSub b i) (b i)) (σ ^ p ^ s) = Ideal.span {c i s} ∧
      idealD p M (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} ∧
      c i s ^ p = δ i s * c i (s + 1) ∧
      HasLen v R (OmType (stepOrder M (flagSub b i) (b i)) (σ ^ p ^ (s + 1)))
        (v (algebraMap R C (δ i s)))) ∧
    (∀ s, HasLen v R (OmType M (σ ^ p ^ (s + 1))) (∏ i, v (algebraMap R C (δ i s)))) ∧
    ∀ (j s : ℕ), HasLen v R
      (OmType (M.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) (σ ^ p ^ (s + 1)))
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), v (algebraMap R C (δ i s)))

def FlagStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → IsTight v p AA.carrier →
  ∀ (n : ℕ) (b : Module.Basis (Fin n) F N),
    (∀ i : Fin n, GenAF p AA.carrier (flagSub b i).toAddSubgroup) →
  ∀ σ : MulChar F R, IsFund p σ → FlagConcl v p AA.carrier b σ

end GlobalTheory.CompanionTheory.Ar.GR
