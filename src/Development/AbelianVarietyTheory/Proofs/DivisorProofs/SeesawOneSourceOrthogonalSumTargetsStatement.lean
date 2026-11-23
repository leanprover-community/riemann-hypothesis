module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExternalProductOnHermitianSumSmulLeft
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.seesaw_oneSource_orthogonalSumTargets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B : HSp D) (χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle)
    (ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)) (ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)),
    IsWeilDatumO ψ S A χ₁ χ₁' ω₁ → IsWeilDatumO ψ S B χ₂ χ₂' ω₂ →
    ∃ (ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ))
      (χ χ' : (AE D)ˣ →* Circle) (c : GA D S → GA D A → GA D B → ℂ),
      IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ χ' ω ∧ (∀ u g g₁, ‖c u g g₁‖ = 1) ∧
      ∀ φ φ', IsThetaFunO ψ S A φ → IsThetaFunO ψ S B φ' → IsThetaFunO ψ S (GlobalTheory.Doubling.hsum A B) (box2 φ φ') ∧
        ∀ u g g₁, thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') =
          c u g g₁ * (thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ') := by
  first | exact @GlobalTheory.SeesawSumTarget.seesaw_sum | exact GlobalTheory.SeesawSumTarget.seesaw_sum | (intros; apply GlobalTheory.SeesawSumTarget.seesaw_sum <;> assumption)
