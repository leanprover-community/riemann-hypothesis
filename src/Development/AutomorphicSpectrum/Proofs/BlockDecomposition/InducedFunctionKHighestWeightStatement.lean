module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeight
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.RgBcC.RealD (IsLev)
open GlobalTheory.CompanionTheory.ModelS (SmF fRaw Kf muZ)

theorem GlobalTheory.T.inducedFunction_k_highest_weight :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam →
      ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : SmF n, F.1 = fRaw lam lev →
        (∀ a b : Fin n, a < b → Kf a b F = 0) ∧
          ∀ a : Fin n, Kf a a F = (muZ lam lev a : ℂ) • F :=
  GlobalTheory.CompanionTheory.ModelS.f_highest
