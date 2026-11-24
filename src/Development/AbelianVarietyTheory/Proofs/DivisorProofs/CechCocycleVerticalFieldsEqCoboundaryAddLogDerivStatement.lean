module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleVerticalFieldsEqCoboundaryAddLogDeriv
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cechCocycle_verticalFields_eq_coboundary_add_logDerivatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ (e : J → J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i i', IsField (W i ⊓ W i') (e i i')) → (∀ i i' (h : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), e i i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') h).hom r) = 0) → (∀ i i' i'' (O : t.G.left.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → ∀ f : Γ(t.G.left, O), e i i' O f + e i' i'' O f = e i i'' O f) → ∃ (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (h : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsField (W i) (h i)) ∧ (∀ i (hW : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), h i (W i) ((t.G.hom.appLE U.1 (W i) hW).hom r) = 0) ∧ ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (e i i' O f) = valR g₀ O (h i O f - h i' O f) + ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := by
  first | exact @GlobalTheory.KSCocycle.exists_coboundary_add_dlog | exact GlobalTheory.KSCocycle.exists_coboundary_add_dlog | (intros; apply GlobalTheory.KSCocycle.exists_coboundary_add_dlog <;> assumption)
