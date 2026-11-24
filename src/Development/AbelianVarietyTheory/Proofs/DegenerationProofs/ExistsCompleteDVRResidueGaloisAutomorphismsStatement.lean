module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRResidueGaloisAutomorphisms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_completeDVR_residue_galois_automorphisms : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V → CDvr V' → (∀ n : ℕ, n ≠ 0 → IsUnit (n : V)) → ∀ g : V →+* V', Function.Injective g → g.Finite → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (j : V' →+* W), CDvr W ∧ Function.Injective j ∧ (IsLocalRing.maximalIdeal V').map j ≤ IsLocalRing.maximalIdeal W ∧ (IsLocalRing.maximalIdeal V).map (j.comp g) ≤ IsLocalRing.maximalIdeal W ∧ ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : V →+* k) (q : W →+* K), Function.Surjective p → Function.Surjective q → (∀ x, algebraMap k K (p x) = q (j (g x))) → FiniteDimensional k K ∧ IsGalois k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : W ≃+* W, (∀ x, σ (j (g x)) = j (g x)) ∧ ∀ x, q (σ x) = τ (q x) := by
  first | exact @GlobalTheory.exists_cDvr_residue_galois | exact GlobalTheory.exists_cDvr_residue_galois | (intros; apply GlobalTheory.exists_cDvr_residue_galois <;> assumption)
