module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfolding
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.eisenstein_coefficient_block_unfolding : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (μr : Measure (Mx D V.rank r)) (𝓕r : Set (Mx D V.rank r)) (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)),
    IsCovolOne (ratMx D V.rank r) μr 𝓕r → IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ Φ : Mx D V.rank (r + s) → ℂ, Continuous Φ →
    ∀ B : ℝ≥0, (∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) →
      ∫ z in 𝓕r ×ˢ 𝓕s, ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
          cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂(μr.prod μs) =
        ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq | exact GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.integral_cells_eq <;> assumption)
