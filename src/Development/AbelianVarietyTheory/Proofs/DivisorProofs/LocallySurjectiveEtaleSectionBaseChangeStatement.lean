module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isLocallySurjective_etale_baseChange : (∀ (Y X : Scheme.{0}) (f : Y ⟶ X), Etale f → Surjective f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f)) ∧ (∀ (P Q : PSh) (f : P ⟶ Q) (s : Q ⟶ P), s ≫ f = 𝟙 Q → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) ∧ ∀ (P Q P' Q' : PSh) (a : P' ⟶ P) (f' : P' ⟶ Q') (f : P ⟶ Q) (b : Q' ⟶ Q), IsPullback a f' f b → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' := by
  first | (exact @GlobalTheory.EtC.locallySurjective_etale_section_baseChange) | (exact GlobalTheory.EtC.locallySurjective_etale_section_baseChange) | (intros; apply GlobalTheory.EtC.locallySurjective_etale_section_baseChange  <;> assumption)
