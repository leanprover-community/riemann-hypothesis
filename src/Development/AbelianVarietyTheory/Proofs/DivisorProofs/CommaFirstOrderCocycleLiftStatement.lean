module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaFirstOrderCocycleLift
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.comma_first_order_cocycle_lift : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict F G).pull2 → Function.Surjective (CoefMap.restrict F G).pull1 → (∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T)) → Function.Surjective (pullGlob1 (CoefMap.restrict F G)) → (∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) → Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.CechDR.pullHyp2_restrict_injective | exact GlobalTheory.CechDR.pullHyp2_restrict_injective | (intros; apply GlobalTheory.CechDR.pullHyp2_restrict_injective <;> assumption)
