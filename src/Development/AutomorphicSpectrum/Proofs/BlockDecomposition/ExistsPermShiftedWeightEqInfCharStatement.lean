module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermShiftedWeightEqInfChar
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

open PositivityTheory.RgBcC (infOf)
open PositivityTheory.RgBcC.RealD (IsLev)

theorem _root_.GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
      ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n,
        (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 -
          ((a : ℕ) : ℂ) = infOf lam false (σ a) :=
  GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ
