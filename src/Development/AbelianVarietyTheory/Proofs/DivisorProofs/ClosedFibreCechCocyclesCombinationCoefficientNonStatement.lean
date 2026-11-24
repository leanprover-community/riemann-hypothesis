module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocyclesCombinationCoefficientNon
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

theorem _root_.GlobalTheory.T.closed_fibre_cechCocycles_combination_coefficient_nonunit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (e : Fin (n + 1) → ∀ i i' : J, Γ(A.left, ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')), (∀ b, (∀ i i' i'', resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (e b i i''))) → ∃ r : Fin (n + 1) → Γ(X, U.1), (∃ b, r b ∉ m) ∧ ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * e b i i' = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  first | exact @GlobalTheory.FibreH1.fibre_dim | exact GlobalTheory.FibreH1.fibre_dim | (intros; apply GlobalTheory.FibreH1.fibre_dim <;> assumption)
