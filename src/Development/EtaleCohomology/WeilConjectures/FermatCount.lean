module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace IsProjOver)

namespace LateralTheory.EWeil

attribute [local instance] MvPolynomial.gradedAlgebra

def Base : Prop :=
  (A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ DivisorNaturality ∧ DivisorRingCompatibility ∧ DivisorSupportCondition ∧ DivisorAdditivity ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11) ∧
  (B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ DivisorPicardCompatibility ∧ B6h1 ∧ B7) ∧ (C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5) ∧ D1 ∧ (E1 ∧ E2 ∧ E3 ∧ E4 ∧ E6 ∧ E8)

section Defs
variable (l : ℕ) [Fact l.Prime] {k : Type} [Field k]

def IsFrob {Ω : Type} [Field Ω] [Algebra k Ω] (σ : Ω ≃ₐ[k] Ω) : Prop := ∀ x, σ x = x ^ Nat.card k

abbrev HX (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) : Type 1 :=
  HQ l (sch.obj (geom Ω p)) n 0

def geoF {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) (σ : Ω ≃ₐ[k] Ω) :
    HX l Ω p n →ₗ[ℚ_[l]] HX l Ω p n := galHQ l Ω p n 0 σ⁻¹

def IsEig {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) (σ : Ω ≃ₐ[k] Ω)
    (α : AlgebraicClosure ℚ_[l]) : Prop :=
  Module.End.HasEigenvalue ((geoF l p n σ).baseChange (AlgebraicClosure ℚ_[l])) α

def WtIn {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) (S : Set ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ α, IsEig l p n σ α →
    ∀ ι : AlgebraicClosure ℚ_[l] →+* ℂ, Real.logb (Nat.card k) (‖ι α‖ ^ 2) ∈ S

def SmProj (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k) : Prop := SmoothOfRelativeDimension d p ∧ IsProjOver p

def IsCI (d r : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k) : Prop := SmoothOfRelativeDimension d p ∧
  ∃ (f : Fin r → MvPolynomial (Fin (d + r)) k)
    (e : X ≅ Sp (MvPolynomial (Fin (d + r)) k ⧸ Ideal.span (Set.range f))),
    e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k _)) = p

inductive Peel : ℕ → ∀ {Y : Scheme.{0}} (_ : Y ⟶ Sp k) {X : Scheme.{0}} (_ : X ⟶ Sp k), Prop
  | base {d : ℕ} {Y : Scheme.{0}} (pY : Y ⟶ Sp k) : SmProj d pY → Peel d pY pY
  | step {e : ℕ} {Y X Y' Z : Scheme.{0}} (pY : Y ⟶ Sp k) (pX : X ⟶ Sp k) (pY' : Y' ⟶ Sp k) (ι : Z ⟶ X) (U : X.Opens) :
      Peel (e + 1) pY pX → Peel e pY' (ι ≫ pX) → IsClosedImmersion ι → (U : Set X) = (Set.range ι)ᶜ →
      Peel (e + 1) pY (U.ι ≫ pX)

end Defs

def Model : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj d p →
  ∃ (k' : Type) (_ : Field k') (_ : Finite k') (_ : Algebra k k') (Y U : Scheme.{0}) (pY : Y ⟶ Sp k') (pU : U ⟶ Sp k') (r : ℕ),
    Peel d pY pU ∧ IsCI d r pU ∧ ∀ S, WtIn l pY d S → WtIn l p d S

end LateralTheory.EWeil

end
