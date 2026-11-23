module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
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

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel

theorem bigCell_of_poisson_siegel :
    (∀ (D : Formalism.BasicNotions.D7) (r : ℕ), ∃ (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)) (𝓖 : Set (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)), PositivityTheory.GramSchwartzFunctions.BC.IsCovolOneH lam 𝓖) → PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm → (∀ (D : Formalism.BasicNotions.D7) (r : ℕ) (V : Formalism.BasicNotions.TH.HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → HasSum (fun β : PositivityTheory.GramSchwartzFunctions.HermE D r => PositivityTheory.GramSchwartzFunctions.BC.IfrB V ν φ β) (PositivityTheory.GramSchwartzFunctions.Ifr V ν φ)) → PositivityTheory.GramSchwartzFunctions.BC.SiegelND → PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg → PositivityTheory.GramSchwartzFunctions.BigCell := by
  intro hlam hP hG hND hDeg D r V h2r ψ hψ θ hθ μ 𝓕 h𝓕 ν hν φ hφ habs hsum
  obtain ⟨lam, 𝓖, hlg⟩ := hlam D r
  have hyp : Hyp D r V ψ θ μ lam ν φ :=
    ⟨h2r, hψ, hθ, ⟨𝓕, h𝓕⟩, ⟨𝓖, hlg⟩, hν, hφ, habs⟩
  have h1 := hP D r V ψ θ μ lam ν φ hyp hsum
  have h2 := hG D r V θ hθ ν hν φ hφ habs
  have h3 : (fun β : HermE D r => IfrB V ν φ β) = fun β : HermE D r => W ψ V μ lam φ β := by
    funext β
    by_cases hβ : β.1.det = 0
    · exact hDeg D r V ψ θ μ lam ν φ hyp β hβ
    · exact hND D r V ψ θ μ lam ν φ hyp β hβ
  rw [h3] at h2
  have h4 := h1.unique h2
  have h5 := hsum.hasSum
  rwa [h4] at h5

end GlobalTheory.CompanionTheory.WeilSiegel
