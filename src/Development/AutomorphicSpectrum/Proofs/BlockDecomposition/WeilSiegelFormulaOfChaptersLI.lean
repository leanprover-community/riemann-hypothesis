module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.PullSchLI
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsThetaIntLtTopOfEqZero
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelAssemblyLI

open GlobalTheory.CompanionTheory.SiegelAssembly

theorem weilSiegelFormula_of_chapters_LI : GlobalTheory.Published.WeilThetaConvergence → GlobalTheory.Published.WeilEisensteinSiegelConvergence →
    PullSchLI → EisCells → ThetaOrbits → BigCell → GlobalTheory.Published.WeilSiegelFormula := by
  intro hTh hES hP hE hT hB D n V hn h2n ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω ν hν Φ
  haveI := hν
  have hw : 2 * Formalism.MainNotions.SchurIrreducible.wittIdx V ≤ V.rank := two_mul_wittIdx_le_rank V
  have hSet : HidaSetting D n V ψ χ θ μ ω := ⟨hn, h2n, hψ, hχ, hη, hθ, ⟨𝓕, hμ⟩, hω⟩
  have hconv := hES D n V hn h2n ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω Φ
  choose μr 𝓕r hμr using fun r => GlobalTheory.MixModel.exists_isCovolOne D V.rank r
  choose c hc using fun U : Submodule D.host.E (Fin n → D.host.E) => exists_isRowBasis U
  have hEis := hE D n V ψ χ θ μ ω hSet Φ hconv μr (fun r => ⟨𝓕r r, hμr r⟩) c hc
  have hfib : ∀ U : Submodule D.host.E (Fin n → D.host.E),
      HasSum (fun b : HermE D (Module.finrank D.host.E U) => J ψ V (μr _) (pull (c U) Φ.1) b)
        (Ifr V ν (pull (c U) Φ.1)) := by
    intro U
    have hr : Module.finrank D.host.E U ≤ n := by
      have := Submodule.finrank_le U
      simpa using this
    have hpull := hP D θ hθ V.rank _ n (c U) (hc U).1 Φ.1 Φ.2
    have habs : GlobalTheory.SiegelFormula.absThetaInt V ν (pull (c U) Φ.1) < ⊤ := by
      rcases Nat.eq_zero_or_pos (Module.finrank D.host.E U) with h0 | hpos
      · exact absThetaInt_lt_top_of_eq_zero V ν h0 _
      · exact hTh D _ V hpos (Or.inr (by omega)) θ hθ ν hν ⟨_, hpull⟩
    exact hB D _ V (by omega) ψ hψ θ hθ (μr _) (𝓕r _) (hμr _) ν hν _ hpull habs
      (hEis.summable.sigma_factor U)
  exact (hEis.sigma hfib).unique
    (hT D n V θ hθ ν hν Φ (hTh D n V hn (Or.inr (by omega)) θ hθ ν hν Φ) c hc)

end GlobalTheory.CompanionTheory.SiegelAssemblyLI
