module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureSmooth
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem _root_.GlobalTheory.T.localization_closure_smooth : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (R : Subring Ω) (v : ι → K), AlgebraicIndependent Ω v → ∀ ℓ : K, ℓ ∈ Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) → ℓ ≠ 0 → ∀ h : (∀ a ∈ R, algebraMap Ω K a ∈ locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ), (((algebraMap Ω K).comp R.subtype).codRestrict (locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ) (fun a => h a a.2)).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure <;> assumption)
