module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatement
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical


theorem _root_.GlobalTheory.T.aux_statement_22 : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* ((GLw a w.1 × GLw b w.1) × (GLw a w.1 × GLw b w.1)), (∀ y, (e y).1 = evw w y) ∧
    (∀ y, e (thv a b v y) = swTw (sgP a b w.1) (e y)) ∧ (∀ y, y ∈ Kv a b v ↔ e y ∈ (K2 a b w.1).prod (K2 a b w.1)) ∧
    ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), e (pv a b v (ratF E a δ₁, ratF E b δ₂)) =
      ((ratW a w.1 δ₁, ratW b w.1 δ₂),
        (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
         ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂))) := by
  first | exact @GlobalTheory.CompanionTheory.SplitIso.split_iso | exact GlobalTheory.CompanionTheory.SplitIso.split_iso | (intros; apply GlobalTheory.CompanionTheory.SplitIso.split_iso <;> assumption)
