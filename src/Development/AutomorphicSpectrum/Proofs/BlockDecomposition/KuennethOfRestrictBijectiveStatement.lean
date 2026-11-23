module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijective
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_of_restrict_bijective : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃), (∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n)) → (∀ a n, Function.Bijective ((resU (E.F₂ a) k₂).pull n)) → (∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n)) → (E.Kun U₁ U₂ U₃ h₁ h₂ ↔ E.Kun U₁' U₂' U₃' h₁' h₂') := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_res | exact GlobalTheory.CompanionTheory.KunGlue.kun_res | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_res <;> assumption)
