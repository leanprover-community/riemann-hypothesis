module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperIdentificationChainAgreesGenerically
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.deeper_identification_chain_agrees_generically : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) → ∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left := by
  first | exact @GlobalTheory.UPoinc.tied_chain_generic | exact GlobalTheory.UPoinc.tied_chain_generic | (intros; apply GlobalTheory.UPoinc.tied_chain_generic <;> assumption)
