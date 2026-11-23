module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterResidueFieldsEqProdGenericShift
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.character_residueFields_eq_prod_genericShift : ∀ (E : Type) [Field E] [NumberField E] (S : Type) [CommRing S] (Pg : Finset (Pl E)) (p p' : ∀ PP : Pl E, S →+* kP PP) (χ : S → ℂ) (ψ0 : ∀ PP : Pl E, AddChar (kP PP) ℂ), IsGenericPsi Pg ψ0 → (∀ s t, χ (s + t) = χ s * χ t) → (∀ s, (∀ PP ∈ Pg, p PP s = 0 ∧ p' PP s = 0) → χ s = 1) → (∀ u u' : ∀ PP : Pl E, kP PP, ∃ s, ∀ PP ∈ Pg, p PP s = u PP ∧ p' PP s = u' PP) → (∀ PP ∈ Pg, (∃ s, (∀ PP' ∈ Pg, (PP' ≠ PP → p PP' s = 0) ∧ p' PP' s = 0) ∧ χ s ≠ 1) ∧ ∃ s, (∀ PP' ∈ Pg, p PP' s = 0 ∧ (PP' ≠ PP → p' PP' s = 0)) ∧ χ s ≠ 1) → ∃ a₁ a₂ : ∀ PP : Pl E, kP PP, (∀ PP ∈ Pg, a₁ PP ≠ 0 ∧ a₂ PP ≠ 0) ∧ ∀ s, χ s = ∏ PP ∈ Pg, ψ0 PP (a₁ PP * p PP s + a₂ PP * p' PP s) := by
  first | exact @GlobalTheory.LeviBlockCharacter.char_eq_prod_shift | exact GlobalTheory.LeviBlockCharacter.char_eq_prod_shift | (intros; apply GlobalTheory.LeviBlockCharacter.char_eq_prod_shift <;> assumption)
