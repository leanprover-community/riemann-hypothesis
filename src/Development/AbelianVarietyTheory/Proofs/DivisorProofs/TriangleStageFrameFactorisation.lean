module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTwoTriplesAgreeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Helpers

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StageGeo

private theorem one_factor {T K : Type} [Group K] {t u : T} (ν : T → K →* Circle) (lam : T → ℂ) (h0 : ∀ s, lam s ≠ 0)
    (good : T → ℂ → Prop)
    (H : ∀ s₁ s₂ c₁ c₂, (s₁ = t ∨ s₁ = u) → (s₂ = t ∨ s₂ = u) → good s₁ c₁ → good s₂ c₂ →
      ∃ k, (ν s₂ k : ℂ) * c₁ * lam s₂ = (ν s₁ k : ℂ) * c₂ * lam s₁) :
    ∃ (κ : ℂ) (k : K), ∀ s c, (s = t ∨ s = u) → good s c → c = κ * ((ν s k : ℂ) * lam s) := by
  have same : ∀ s c₁ c₂, (s = t ∨ s = u) → good s c₁ → good s c₂ → c₁ = c₂ := fun s c₁ c₂ hs g₁ g₂ => by
    obtain ⟨k, hk⟩ := H s s c₁ c₂ hs hs g₁ g₂
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (mul_right_cancel₀ (h0 s) hk)
  have nz : ∀ s k, (ν s k : ℂ) * lam s ≠ 0 := fun s k => mul_ne_zero (Circle.coe_ne_zero _) (h0 s)
  by_cases ht : ∃ c, good t c
  · obtain ⟨c₁, g₁⟩ := ht
    by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      obtain ⟨k, hk⟩ := H t u c₁ c₂ (.inl rfl) (.inr rfl) g₁ g₂
      refine ⟨c₁ / ((ν t k : ℂ) * lam t), k, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · rw [same _ _ _ (.inr rfl) g g₂, div_mul_eq_mul_div, eq_div_iff (nz _ _)]
        linear_combination -hk
    · refine ⟨c₁ / ((ν t 1 : ℂ) * lam t), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · exact absurd ⟨c, g⟩ hu
  · by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      refine ⟨c₂ / ((ν u 1 : ℂ) * lam u), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inr rfl) g g₂
    · refine ⟨0, 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · exact absurd ⟨c, g⟩ hu

private theorem exists_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} {a a' : ℕ}
    {Γ : Geo σ a a'} {Xa Xb : Chars F E} {oa oa' ob ob'} (ha : IsTriple B Γ Xa oa oa') (hb : IsTriple B Γ Xb ob ob') :
    ∃ R Ra Rb ca cb, IsMatched B Γ Xa oa oa' R Ra ∧ IsMatched B Γ Xb ob ob' R Rb ∧ IsConst B Γ Xa oa oa' R Ra ca ∧
      IsConst B Γ Xb ob ob' R Rb cb ∧ cb ≠ 0 := by
  obtain ⟨R, Ra, h1⟩ := hM F E σ B a a' Γ Xa oa oa' ha
  obtain ⟨R', Rb, h2⟩ := hM F E σ B a a' Γ Xb ob ob' hb
  have h3 : IsMatched B Γ Xb ob ob' R Rb := ⟨hb, GlobalTheory.T.real_maps_two_triples_agree hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩
  obtain ⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩ := (hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1
  obtain ⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩ := (hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3
  exact ⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

end Helpers
