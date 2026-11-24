module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityReductionDiagonalProd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.multiplicity_reduction_diagonal_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod | exact GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod <;> assumption)
