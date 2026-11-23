module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLattices
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_form_extend_to_all_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (mu : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ ga ∈ Δ, IsUn X ga) → (∀ ga ∈ Δ, ∀ L' ∈ 𝓛, mapL ga L' ∈ 𝓛 ∧ ‖mu ga L'‖ = 1) → (∀ ga ∈ Δ, ∀ ga' ∈ Δ, ∀ L' ∈ 𝓛, mu (ga * ga') L' = mu ga (mapL ga' L') * mu ga' L') → (∀ k, L k ∈ 𝓛) → (∀ k k', ∀ ga ∈ Δ, mapL ga (L k) = L k' → k = k') → (∀ k, ∀ ga ∈ Δ, mapL ga (L k) = L k → mu ga (L k) = 1) → (∀ k, IsStabForm X Δ (L k) la (Q k)) → ∃ F : Lt E r → Frame X.Ψ r → ℂ, IsForm X Δ 𝓛 mu la F ∧ ∀ k, ∀ x ∈ X.dom, F (L k) x = Q k x := by
  first | exact @GlobalTheory.Dict.exists_form_extend | exact GlobalTheory.Dict.exists_form_extend | (intros; apply GlobalTheory.Dict.exists_form_extend <;> assumption)
