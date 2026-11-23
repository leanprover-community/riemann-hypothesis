module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOfBasisFunctor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → (F).obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp (F) u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (F).obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp (F) u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt <;> assumption)
