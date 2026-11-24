module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LiftTypeDn

theorem hasTypeAt_of_approx {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (ψ : GA D V → ℂ)
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ χ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S χ ∧ ∀ x ∈ C, ‖ψ x - χ x‖ < δ) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S ψ := by
  intro C hC δ hδ
  obtain ⟨χ, hχ, h1⟩ := h C hC (δ / 2) (by linarith)
  obtain ⟨ψ', hψ', h2⟩ := hχ C hC (δ / 2) (by linarith)
  refine ⟨ψ', hψ', fun x hx => ?_⟩
  have e : ψ x - ψ' x = (ψ x - χ x) + (χ x - ψ' x) := by ring
  rw [e]
  have := norm_add_le (ψ x - χ x) (χ x - ψ' x)
  linarith [h1 x hx, h2 x hx]

end GlobalTheory.LiftTypeDn
