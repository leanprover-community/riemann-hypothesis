module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc.Basis

theorem oneCocycle_invertibleLocus_isCoboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e y hy
  obtain ⟨L, l, hl, -, -, huniv⟩ := H T e
  have hunit : ∀ t (w : L ⟶ G.obj t), IsUnit (mp F (l ≫ w) e) := by
    intro t w
    rw [mp_comp]
    exact hl.map _
  obtain ⟨gL, hgL⟩ := oneCocycle_coboundary_comma_localBasis F G H hcov hdir L (fun t t' w a ↦ y t t' (l ≫ w) a)
    (fun t t' t'' w a b ↦ by
      have h := hy t t' t'' (l ≫ w) a b (hunit t w)
      rw [Category.assoc] at h
      exact h)
  classical
  refine ⟨fun t u ↦ if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0, ?_⟩
  have hg : ∀ t (u : T ⟶ G.obj t) (w : L ⟶ G.obj t), l ≫ w = u →
      (if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0) = gL t w := by
    intro t u w hw
    have h : ∃ w : L ⟶ G.obj t, l ≫ w = u := ⟨w, hw⟩
    rw [dite_eq_left h]
    exact congrArg (gL t) (Subsingleton.elim _ _)
  intro t t' u a hu
  obtain ⟨w, hw, -⟩ := huniv (G.obj t) u hu
  have hw' : l ≫ (w ≫ G.map a) = u ≫ G.map a := by rw [← Category.assoc, hw]
  simp only []
  rw [hg t u w hw, hg t' (u ≫ G.map a) (w ≫ G.map a) hw', hgL t t' w a, hw]

end GlobalTheory.CatCoh.Desc.Basis
