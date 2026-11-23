module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemCone
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.RgBcC.RealD (inCone)

theorem GlobalTheory.T.highest_weight_mem_cone :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (K : Fin n → Fin n → Module.End ℂ V),
      Formalism.REAL.GlRel K → ∀ lev : Fin n → ℕ, Monotone lev →
      ∀ (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ) (x : V),
        Formalism.REAL.KHighest (fun _ => true) K ν x →
        (∀ a b v, lev a = lev b → a ≠ b → ev (K a b v) = 0) →
        (∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) →
        (∃ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ev (T x) ≠ 0) →
        inCone lev (ν - μ) :=
  GlobalTheory.CompanionTheory.HighestCone.inCone_of_highest
