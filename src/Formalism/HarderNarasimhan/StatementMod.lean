module

public import Formalism.HarderNarasimhan.StatementPl
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField

noncomputable section

namespace Formalism.HN

def IdealScale : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), I ≠ 0 →
    ∀ M : Submodule (𝓞 K) V, M.FG → M ≠ ⊥ →
      (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M).FG ∧
      muDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muMaxDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muMaxDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muMinDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muMinDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)

def IndexMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ M N : Submodule (𝓞 K) V, M.FG → N ≤ M → N ≠ ⊥ → rkK N = rkK M →
      muDef b X N = muDef b X M -
        2 * Real.log (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) /
          ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) ∧
      muMaxDef b X N ≤ muMaxDef b X M

end Formalism.HN
