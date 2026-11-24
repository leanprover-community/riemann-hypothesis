module

public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HermitianLattices.StatementLat
public import Mathlib.RingTheory.FractionalIdeal.Norm
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

open Module NumberField

noncomputable section

namespace Formalism.LFunctionChainParameters.LLcv

open Formalism.HN

section Defs

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

def lcvInf (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) {j : ℕ} (e : Fin j → V) : ℝ :=
  (1 / (nPl K : ℝ)) * ∑ v, Real.log (gramPl b X v e).det.re

def lcvFin {j : ℕ} (e : Fin j → V) (M : Submodule (𝓞 K) V) : ℝ :=
  2 * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
    (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
      (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ))

def lcv (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) {j : ℕ} (e : Fin j → V)
    (M : Submodule (𝓞 K) V) : ℝ :=
  lcvInf b X e + lcvFin e M

end Defs

def LcvMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V) (M : Submodule (𝓞 K) V), LinearIndependent K e → M.FG → M ≠ ⊥ →
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e) →
      rkK M = j ∧ 0 < j ∧
      (∀ v, 0 < (gramPl b X v e).det.re ∧ (gramPl b X v e).det.im = 0) ∧
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M)).Finite ∧
      muDef b X M = -lcv b X e M / (rkK M : ℝ)

def LcvExists : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V),
    ∃ (j : ℕ) (e : Fin j → V), LinearIndependent K e ∧ (∀ a, e a ∈ M) ∧
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e)

def LcvFree : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V), LinearIndependent K e → 0 < j →
      lcvFin e (Submodule.span (𝓞 K) (Set.range e)) = 0 ∧
      muDef b X (Submodule.span (𝓞 K) (Set.range e)) = -lcvInf b X e / (j : ℝ)

def LcvIdeal : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (_b : Basis ι K V) (j : ℕ) (e : Fin j → V)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), LinearIndependent K e → 0 < j → I ≠ 0 →
      lcvFin e (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K)
        (Submodule.span (𝓞 K) (Set.range e))) =
        2 * (j : ℝ) * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)

def IndexLocLen : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V), B ≤ A → B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 →
      (∀ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI := p.2.isPrime;
        Module.length (𝓞 K) ((Formalism.HermitianLatticesTheory.localization₂ p.1 A) ⧸
          (Formalism.HermitianLatticesTheory.localization₂ p.1 B).comap (Formalism.HermitianLatticesTheory.localization₂ p.1 A).subtype)) ≠ ⊤) ∧
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.locLen p.1 A B)).Finite ∧
      Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
        ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, Real.log (Ideal.absNorm p.1 : ℝ) *
          (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.locLen p.1 A B : ℝ))

end Formalism.LFunctionChainParameters.LLcv
