module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalVectorFieldUniqueCombinationBasis
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

theorem _root_.GlobalTheory.T.verticalVectorField_unique_combination_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (W : t.G.left.Opens) (hW : W ≤ t.G.hom ⁻¹ᵁ U.1) (e : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), IsField W e → (∀ r : Γ(X, U.1), e W ((t.G.hom.appLE U.1 W hW).hom r) = 0) → ∃! c : Fin n → Γ(t.G.left, W), ∀ (O : t.G.left.Opens) (hO : O ≤ W) (f : Γ(t.G.left, O)), e O f = ∑ a, resG t.G.left hO (c a) * δ a O f := by
  first | exact @GlobalTheory.VertSpan.vert_span | exact GlobalTheory.VertSpan.vert_span | (intros; apply GlobalTheory.VertSpan.vert_span <;> assumption)
