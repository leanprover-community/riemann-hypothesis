module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictNormalCrossingsDescentEtaleCompletion
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

@[expose] public section

open AlgebraicGeometry IsLocalRing ReciprocityTheory.AnForm.R GlobalTheory.Toroidal

theorem _root_.GlobalTheory.T.strictNormalCrossings_descent_etale_completion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type) [Field k] (m e : ℕ) (φ : A →+* ChartRing k m e) (D : Ideal A), IsEtaleCompletion φ → D.map φ = Ideal.span {∏ i : Fin m, bdParam k m e i} → (∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap φ = (Ideal.span {bdParam k m e i'}).comap φ → i = i') → ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  first | exact @GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion | exact GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion | (intros; apply GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion <;> assumption)
