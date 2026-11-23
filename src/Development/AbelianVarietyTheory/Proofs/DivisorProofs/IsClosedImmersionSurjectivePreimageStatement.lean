module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSurjectivePreimage
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.isClosedImmersion_surjective_to_colimit : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0}) [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected] (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G), (∀ x : X, ∃ U ∈ 𝒰, x ∈ G U) → ∀ (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U), (∀ U, IsClosedImmersion (e U)) → (∀ U, Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → ∀ j : X ⟶ colimit F, (∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U) → IsClosedImmersion j ∧ Surjective j ∧ ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
  first | exact @GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage | exact GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage | (intros; apply GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage <;> assumption)
