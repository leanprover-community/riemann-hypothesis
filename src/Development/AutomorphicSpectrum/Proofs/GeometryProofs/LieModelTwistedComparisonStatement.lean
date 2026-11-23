module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelTwistedComparison
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

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_twisted_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (Ω : Type) [Field Ω]
    (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (tΩ : SAB H (Sp Ω))
    (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ') (V V' : Type) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V')
    (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (φ : V ≃ₗ[Ω] V'),
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M.pt v).left ∧ w.left ≫ m'.φ = (M'.pt (φ v)).left) →
    ∀ a v, φ (ρ (g.s a) v) = ρ' a (φ v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine | exact GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine | (intros; apply GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine <;> assumption)
