module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisConjHeckeCharacterFinitePartEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.norm_galois_conj_heckeCharacter_finitePart_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E) (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ), ‖σ (finPart χ y : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.CMVal.norm_conj_finPart | exact GlobalTheory.CMVal.norm_conj_finPart | (intros; apply GlobalTheory.CMVal.norm_conj_finPart <;> assumption)
