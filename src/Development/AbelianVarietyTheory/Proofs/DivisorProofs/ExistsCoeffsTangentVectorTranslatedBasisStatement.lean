module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffsTangentVectorTranslatedBasis
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

theorem _root_.GlobalTheory.T.exists_coeffs_tangentVector_translatedBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ → w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom → ∃ c : Fin n → S, ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = ∑ a, ρ (c a) * (valR (wt a) O f).snd := by
  first | exact @GlobalTheory.VertSpan.exists_coeffs_translate | exact GlobalTheory.VertSpan.exists_coeffs_translate | (intros; apply GlobalTheory.VertSpan.exists_coeffs_translate <;> assumption)
