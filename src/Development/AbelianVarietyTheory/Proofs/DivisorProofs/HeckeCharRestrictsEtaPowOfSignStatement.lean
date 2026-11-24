module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharRestrictsEtaPowOfSign
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heckeChar_restricts_eta_pow_of_sign : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (N : ℕ), IsHeckeChar D χ →
    (∀ x y : (AE D)ˣ, (y : AE D) = x * cA D x → χ y = 1) →
    ∀ θ : InfFam D, IsInfFam θ →
    (∀ (τ : D.what₂.Tau) (x : (AE D)ˣ), finPart D (x : AE D) = 1 → θ τ (infPart D (x : AE D)) = -1 →
      (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) → ((χ x : Circle) : ℂ) = (-1) ^ N) →
    ResEta D χ N := by
  first | exact @GlobalTheory.HeckeSignEta.resEta_of_sign | exact GlobalTheory.HeckeSignEta.resEta_of_sign | (intros; apply GlobalTheory.HeckeSignEta.resEta_of_sign <;> assumption)
