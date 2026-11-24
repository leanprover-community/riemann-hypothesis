module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyDescendsToNumberField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.cmFamily_descends_to_numberField : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (ω : k) (C : Ell H k ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp k)) (L : Submodule (𝓞 E) D.La) (ω' : ℂ) (C' : Ell H ℂ ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap (algebraMap k ℂ))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap k ℂ) φ → IsFam C' T' h L ψ' →
  ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ (ω₂ : k₂) (C₂ : Ell H k₂ ω₂) (φ₂ : C₂.P.A.left ⟶ C.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left) (T₂ : PAT H (Sp k₂)) (m₂ : SABMap T₂.t T.t (spMap (IntermediateField.inclusion h₂).toRingHom)) (m₃ : SABMap T'.t T₂.t (spMap (algebraMap k₂ ℂ))),
    EllMap C₂ C (IntermediateField.inclusion h₂).toRingHom φ₂ → EllMap C' C₂ (algebraMap k₂ ℂ) φ₃ → φ₃ ≫ φ₂ = φ → m₃.φ ≫ m₂.φ = m.φ → ∃ ψ : L → (C₂.P.A ⟶ T₂.t.G), IsFam C₂ T₂ h L ψ ∧ ∀ a, (ψ' a).left ≫ m₃.φ = φ₃ ≫ (ψ a).left := by
  first | exact @GlobalTheory.CM.isFam_descends_to_numberField | exact GlobalTheory.CM.isFam_descends_to_numberField | (intros; apply GlobalTheory.CM.isFam_descends_to_numberField <;> assumption)
