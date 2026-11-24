module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullEndo
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibre, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibreStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibre =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibre", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange\nimport Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullEndo\nimport Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.EndoHom

theorem isMonHom_of_prod_pow {S : Scheme.{0}} {A C : Over S} [GrpObj A] [GrpObj C] [IsCommMonObj C]
    (pr : Fin 8 → (A ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over S) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ A, ∀ a, x ≫ pr a = y a)
    (f : A ⟶ A) (e : Fin 8 → Fin 8 → ℤ)
    (hf : ∀ a, f ≫ pr a = ((List.finRange 8).map fun b => pr b ^ e a b).prod) : IsMonHom f := by
  refine isMonHom_of_mul f fun T x y => ?_
  obtain ⟨z, -, hu⟩ := huniq T (fun a => ((x * y) ≫ f) ≫ pr a)
  refine (hu ((x * y) ≫ f) fun a => rfl).trans (hu ((x ≫ f) * (y ≫ f)) fun a => ?_).symm
  have hpre : ∀ {T : Over S} (w : T ⟶ A) (a : Fin 8),
      w ≫ f ≫ pr a = ((List.finRange 8).map fun b => (w ≫ pr b) ^ e a b).prod := fun {T} w a => by
    let φ : (A ⟶ C) →* (T ⟶ C) := MonoidHom.mk' (w ≫ ·) fun g₁ g₂ => MonObj.comp_mul w g₁ g₂
    have h := map_list_prod φ ((List.finRange 8).map fun b => pr b ^ e a b)
    rw [List.map_map] at h
    rw [hf a]
    refine h.trans (congrArg List.prod (List.map_congr_left fun b _ => ?_))
    exact map_zpow φ (pr b) (e a b)
  have := hpr
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hpre, hpre, hpre]
  simp only [MonObj.mul_comp, mul_zpow]
  exact (List.prod_map_mul).symm

theorem isMonHom_of_isGrpPullback_endo {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (hg : IsGrpPullback G' G b φ) (f : G ⟶ G) (hf : IsMonHom f)
    (f₀ : G' ⟶ G') (h : f₀.left ≫ φ = φ ≫ f.left) : IsMonHom f₀ := by
  obtain ⟨f', hf', he⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hg f hf
  have : f' = f₀ := Over.OverMorphism.ext (hg.1.hom_ext (he.trans h.symm) ((Over.w f').trans (Over.w f₀).symm))
  exact this ▸ hf'

end GlobalTheory.Poinc.EndoHom


open GlobalTheory.Poinc.EndoHom in
theorem GlobalTheory.Poinc.isMonHom_of_same_rechart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → ∀ E, IsMonHom (ε' E) := by
  intro g n F W Z i X ε hD c₀ hc R' fg frac hth hev ρ' ε' hS E
  obtain ⟨c, -, pr, hpr, huniq, -, hε⟩ := hD
  have hE : IsMonHom (ε E) := isMonHom_of_prod_pow pr hpr huniq (ε E) E (hε E)
  obtain ⟨P₀, a, a', ε₀, h₁, h₂, -, -, hε₀, -⟩ := hS
  have h₀ : IsMonHom (ε₀ E) := isMonHom_of_isGrpPullback_endo h₁ (ε E) hE (ε₀ E) (hε₀ E).1
  have : IsSchemeTheoreticallyDominant (spMap (X.S.rechart c₀ hc R' fg frac hth hev).R.val.toRingHom) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ Subtype.val_injective
  have := ρ'.P.isAb.smooth
  have := ρ'.P.isAb.proper
  exact GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback h₂ h₂ (ε₀ E) (ε' E) (hε₀ E).2
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibre =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibreStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibreStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibre\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isMonHom_rescaled_realisation_same_genericFibre : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → ∀ E, IsMonHom (ε' E) := by
  first | exact @GlobalTheory.Poinc.isMonHom_of_same_rechart
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibreStatement =====
