module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComparisonStructureH1Affine
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cech_comparison_structure_h1_affine : ∀ (X T : Scheme.{0}) (p : T ⟶ X), IsSeparated p → ∀ (U : X.affineOpens) (J : Type) (W : J → T.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = p ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), ∃ Φ : (∀ i i' : J, Γ(T, W i ⊓ W i')) → GlobalTheory.CechDR.HO1 ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)), (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∀ (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ k, (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ((e k) i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ((e k) i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') ((e k) i i''))) → Φ (fun i i' => c i i' - ∑ k, (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i') = Φ c - ∑ k, r k • Φ (e k)) ∧ (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → Φ c = 0 → ∃ h : ∀ i : J, Γ(T, W i), ∀ i i', c i i' = resG T inf_le_left (h i) - resG T inf_le_right (h i')) ∧ (∀ x, ∃ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) ∧ Φ c = x) ∧ ∀ (R' : Type) [CommRing R'] (σ : Γ(X, U.1) →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ T) (ι' : Y ⟶ (p ⁻¹ᵁ U.1).toScheme), ι' ≫ (p ⁻¹ᵁ U.1).ι = ι → ∀ (w : ι' ≫ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (Φ c) = 0 := by
  first | exact @GlobalTheory.CechCmp.exists_cech_ho1_cmp | exact GlobalTheory.CechCmp.exists_cech_ho1_cmp | (intros; apply GlobalTheory.CechCmp.exists_cech_ho1_cmp <;> assumption)
