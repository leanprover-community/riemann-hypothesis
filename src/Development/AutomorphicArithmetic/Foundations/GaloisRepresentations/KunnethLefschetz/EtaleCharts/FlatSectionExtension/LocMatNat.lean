module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem appLE_top_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  change _ = f.app ⊤
  rw [Scheme.Hom.app_eq_appLE]
  rfl

private theorem appLE_comp_appTop' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Opens)
    (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ N) (h' : (⊤ : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ N) :
    (f ≫ g).appLE N ⊤ h' = g.appLE N ⊤ h ≫ f.appTop := by
  have e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun _ _ => trivial
  rw [← appLE_top_eq f e]
  exact (Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ h e).symm

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V' V : Scheme.{0}} (s : V' ⟶ V) (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B α β (s ≫ p) (M.map s.appTop.hom) := by
  intro K _ W Z Y q i π D d B α β V' V s p M h x'
  obtain ⟨U, N, hx, hN, h₁, h₂, hU, G, hG, hM⟩ := h (s x')
  have e : (s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i = (s ∣_ U) ≫ U.ι ≫ p ≫ i := by
    rw [← Category.assoc (s ∣_ U), morphismRestrict_ι]
    simp only [Category.assoc]
  have hU' : ⊤ ≤ ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i) ⁻¹ᵁ N := by
    rw [e]
    intro y _
    exact hU (Set.mem_univ ((s ∣_ U) y))
  refine ⟨s ⁻¹ᵁ U, N, hx, hN, h₁, h₂, hU', G, hG, ?_⟩
  have gen : ∀ (f g : ((s ⁻¹ᵁ U : V'.Opens) : Scheme.{0}) ⟶ Z) (_ : f = g) (hf : ⊤ ≤ f ⁻¹ᵁ N) (hg : ⊤ ≤ g ⁻¹ᵁ N),
      f.appLE N ⊤ hf = g.appLE N ⊤ hg := by
    rintro f g rfl _ _
    rfl
  have h3 : ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i).appLE N ⊤ hU' = (U.ι ≫ p ≫ i).appLE N ⊤ hU ≫ (s ∣_ U).appTop :=
    (gen _ _ e hU' (e ▸ hU')).trans (appLE_comp_appTop' _ _ N hU _)
  have h4 : ∀ a : Γ(V, ⊤), (s ∣_ U).appTop.hom (U.ι.appTop.hom a) = (s ⁻¹ᵁ U).ι.appTop.hom (s.appTop.hom a) := by
    intro a
    have e2 : ((s ∣_ U) ≫ U.ι).appTop = ((s ⁻¹ᵁ U).ι ≫ s).appTop := by rw [morphismRestrict_ι]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e2
    exact congrArg (fun φ => φ.hom a) e2
  ext m l
  have h1 := congrFun (congrFun hM m) l
  simp only [Matrix.map_apply] at h1 ⊢
  rw [h3, ← h4, h1]
  rfl
