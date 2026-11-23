module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

theorem _root_.GlobalTheory.T.twisted_frame_invariant_under_descentDatum : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∀ (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) →
    ∀ (V' : Y.Opens), V' ≤ V → ∀ u : Γ(X, f ⁻¹ᵁ V')ˣ, (∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u) →
    ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V' ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V' → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V' → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j) := by
  first | exact @GlobalTheory.LBDescent.twist_frame_descent | exact GlobalTheory.LBDescent.twist_frame_descent | (intros; apply GlobalTheory.LBDescent.twist_frame_descent <;> assumption)
