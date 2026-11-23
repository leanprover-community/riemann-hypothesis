module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary

@[expose] public section

open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)


theorem _root_.GlobalTheory.T.siegel_eisenstein_convergent : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  first | exact @GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | exact GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | (intros; apply GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law <;> assumption)
