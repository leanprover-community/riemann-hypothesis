module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_hom_birational_models_ampleFrames : GlobalTheory.LN.HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (Z₁ Z₂ W : Scheme.{0}) (s₁ : Z₁ ⟶ Sp R) (s₂ : Z₂ ⟶ Sp R) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (tW : SAB H W) (j : W ⟶ Z₁) (j' : W ⟶ Z₂) (_ : SABMap tW t₁ j) (_ : SABMap tW t₂ j') (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsDedekindDomain R → CharZero R → Algebra.FiniteType ℤ R → IsNormalScheme Z₁ → IsProjOver s₁ → IsProjOver s₂ → Flat s₁ → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsProper tW.G.hom → j ≫ s₁ = j' ≫ s₂ → A₁.r = A₂.r → A₁.s = A₂.s → ∃ ρ : Z₁ ⟶ Z₂, j ≫ ρ = j' := by
  first | exact @GlobalTheory.AmpUniq.exists_hom_of_ampFrames | exact GlobalTheory.AmpUniq.exists_hom_of_ampFrames | (intros; apply GlobalTheory.AmpUniq.exists_hom_of_ampFrames <;> assumption)
