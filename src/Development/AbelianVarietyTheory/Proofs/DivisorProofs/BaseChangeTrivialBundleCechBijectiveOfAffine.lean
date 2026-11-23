module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_bijective {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (V : X'.Opens) : Function.Bijective (trivCoord φ s' V) :=
  (GlobalTheory.AbLaw.SecOn.chart (LB.isLB_pull (LB.isLB_triv X) φ) (i0 φ)
    (by rw [triv_pull_U]; exact le_top)).bijective

theorem Φ_bijective_of_affine : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := by
  intro R R' _ _ _ X X' s s' φ h κ _ _ D hD' hD p
  have hB := GlobalTheory.AbLaw.secTermBaseChange_bijective (M := LB.triv X) (D := D) (LB.isLB_triv X) h (p + 1)
    fun t ht => hD t (Finset.card_pos.1 (by omega))
  exact (Function.Bijective.piMap fun t => trivCoord_bijective φ s' _).comp hB

end GlobalTheory.CechPoset
