module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.HeckeLevelFrameExistence.powEig :
    UpperTheory.HeckeLevelFrameExistence.PowEig := by
  intro E _ _ _ n w σ K' hlev g hg y hy m
  have key : ∀ k : ℕ, IsHecke K' (U.lpow K' g k) ∧ locOp σ K' (U.lpow K' g k) y = y := by
    intro k
    induction k with
    | zero =>
      obtain ⟨-, -, -, -, -, -, h1, h2⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g g hg hg
      refine ⟨h1, ?_⟩
      show locOp σ K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) y = y
      rw [h2]
      rfl
    | succ k ih =>
      obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g _ hg ih.1
      refine ⟨h3, ?_⟩
      show locOp σ K' (lconv g (U.lpow K' g k)) y = y
      rw [h5, Module.End.mul_apply, ih.2, hy]
  exact (key m).2
