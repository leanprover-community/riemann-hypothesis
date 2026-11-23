module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteEtaleFunctionFieldIntegralClosureDifferent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.finiteEtale_functionField_integralClosure_differentials : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → IsFinite c → Etale c → ∀ (d : ℕ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] [i1 : Algebra ℂ Z.functionField] [i2 : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], i1 = ffAlg s → i2 = ffAlg s' → (∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (f : Γ(Z, U)), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom ((c.app U).hom f) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ U (genericPoint Z) hU).hom f)) → FiniteDimensional Z.functionField Y.functionField ∧ ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (B : Subalgebra ℂ Z.functionField) (B' : Subalgebra ℂ Y.functionField), IsAffineOpen U → (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y) → (∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y) → (∀ y ∈ B', IsIntegral B (y : Y.functionField)) ∧ (∀ x : Z.functionField, IsIntegral B x → x ∈ B) ∧ (∀ y : Y.functionField, IsIntegral B y → y ∈ B') ∧ (∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → Y.functionField) (w : Fin m → Z.functionField), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D ℂ Y.functionField v) = ∑ j, b j • mapDR ℂ Z.functionField Y.functionField (ι1 (D ℂ Z.functionField (w j)))) := by
  first | (exact @GlobalTheory.W1.SchFF.finiteEtale_functionField) | (exact GlobalTheory.W1.SchFF.finiteEtale_functionField) | (intros; apply GlobalTheory.W1.SchFF.finiteEtale_functionField  <;> assumption)
