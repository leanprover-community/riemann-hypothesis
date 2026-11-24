module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticeClassesFibreSummand
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

@[expose] public section

open NumberField
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_equiv_latticeClasses_fibre_summand : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)) ≃
      {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0},
      ∀ (k : ℕ), Even k → ∀ (σ : ℂ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (e x).1 = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z ((x.2 : F), GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  first | exact @GlobalTheory.LatFibre.exists_equiv | exact GlobalTheory.LatFibre.exists_equiv | (intros; apply GlobalTheory.LatFibre.exists_equiv <;> assumption)
