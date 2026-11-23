module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateCmValueCharacterPermutedWeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.exists_conjugate_cmValueCharacter_permuted_weight : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φK : K →+* ℂ) (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (χ : HChar E) (σ : ℂ ≃+* ℂ), IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = φK) → (starRingEnd ℂ).comp φK ≠ φK → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → IsValChar φ s κ 𝔣 ∅ χ → ∃ (π : Equiv.Perm I) (χ' : HChar E), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsConjWt φ σ κ (κ ∘ π) ∧ GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsConjChar φ s (κ ∘ π) σ χ χ' ∧ IsValChar φ s (κ ∘ π) 𝔣 ∅ χ' := by
  first | exact @GlobalTheory.ConjValChar.exists_conj_valChar | exact GlobalTheory.ConjValChar.exists_conj_valChar | (intros; apply GlobalTheory.ConjValChar.exists_conj_valChar <;> assumption)
