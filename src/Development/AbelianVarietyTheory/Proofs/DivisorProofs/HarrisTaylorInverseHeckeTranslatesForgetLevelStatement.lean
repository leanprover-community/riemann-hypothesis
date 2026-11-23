module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.harrisTaylor_inverse_heckeTranslates_forget_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (o₁ : Obj b (N * k) s) (o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o₁.A ⟶ o₂.A), IsHecke g' c' k (N * k) o o₁ ψ₁ → IsHecke g c k N o₁ o₂ ψ₂ → Nonempty (ObjMap (o.forget N ⟨k * k, by ring⟩ hc) o₂ (𝟙 S)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget) | (exact GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget) | (intros; apply GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget <;> assumption)
