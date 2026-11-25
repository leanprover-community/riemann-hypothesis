module

public import Formalism.CyclotomicNorms.StatementT
public import Mathlib.LinearAlgebra.Eigenspace.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL

section OnePrime

variable {g : ℕ} [Fact g.Prime]

def rootC (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

def labelChar (ω : Fbar g →*₀ ℂ) (d : ℕ) (x y : Fbar g) : ℂ :=
  ω x ^ sInf {a : ℕ | ω y = rootC (g ^ d - 1) ^ a}


open Classical in
def cuspVal (ω : Fbar g →*₀ ℂ) (x : Fbar g) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod g)) : ℂ :=
  if ∃ (p : (ZMod g)[X]) (k : ℕ), Irreducible p ∧ M.charpoly = p ^ k then
    (-1) ^ (Fintype.card ι - 1) *
      ∑ y ∈ (rootsBar M.charpoly).toFinset, labelChar ω (Fintype.card ι) x y *
        ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar g)
            (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) y)),
          (1 - (g : ℂ) ^ ((rootsBar M.charpoly).toFinset.card * i))
  else 0

end OnePrime

section BothPrimes

variable {E : Type} [Field E] [NumberField E] [StarRing E] {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E}

variable [∀ i, Fact (gp i).Prime] {K : Type} [Field K]

end BothPrimes

end GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison
