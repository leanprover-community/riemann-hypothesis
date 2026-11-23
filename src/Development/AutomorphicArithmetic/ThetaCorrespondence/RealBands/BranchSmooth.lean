module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryStabiliserEmbeddingNormLawsStatement
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

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal UpperTheory.Lit.Branch
open scoped InnerProductSpace

open GlobalTheory.SepReal.ProjSm in
theorem UpperTheory.Lit.Branch.mapSmooth :
    MapSmooth := by
  intro n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ T hT v hv
  obtain ⟨-, -, -, -, -, -, hlie, hexp, -⟩ := GlobalTheory.T.unitary_stabiliser_embedding_norm_laws n e ε ε' hpar.signs
  intro k Xs hXs
  have key : (fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (T v)) =
      fun t => T (π ((List.ofFn fun i => NormedSpace.exp (t i • embL e (Xs i))).prod) v) := by
    funext t
    rw [← hT _ (list_mem _ (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact exp_mem (hXs i) (t i))), embH_list, List.map_ofFn]
    simp only [Function.comp_def, hexp]
  rw [key]
  exact (T.restrictScalars ℝ).contDiff.comp (hv k (fun i => embL e (Xs i)) fun i => hlie _ (hXs i))
