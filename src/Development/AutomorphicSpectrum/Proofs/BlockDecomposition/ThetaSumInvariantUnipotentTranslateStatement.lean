module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantUnipotentTranslate
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_sum_invariant_unipotent_translate : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
  PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
  ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g b hg Φ
  obtain ⟨-, -, hψ, -, -, -, -, hW⟩ := hS
  refine tsum_congr fun ξ => ?_
  have hmul : (b.map (incA D) * inner V (ξ.map (incA D)) (ξ.map (incA D)) : Mx D n n) =
      (b * (ξᴴ * (V.gram * ξ))).map (incA D) := by
    change rat b * (adj (rat ξ) * (gA V * rat ξ)) = rat (b * (ξᴴ * (V.gram * ξ)))
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose, gA]
  have htrace (M : Matrix (Fin n) (Fin n) D.host.E) :
      Matrix.trace (M.map (incA D)) = incA D (Matrix.trace M) := by

    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [hW.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), hmul, htrace,
    GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA, hψ.2.2.1, one_mul]
