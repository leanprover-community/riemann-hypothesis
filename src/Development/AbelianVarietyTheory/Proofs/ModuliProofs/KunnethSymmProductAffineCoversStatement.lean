module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KunnethSymmProductAffineCovers
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.kunneth_symm_product_affine_covers : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (u : ∀ i i' j, Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)) (u' : ∀ i j j', Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))), (∀ i i' j j', ∑ a, (pbT p₁ (θ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (φ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - pbT p₁ (φ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (θ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) = (rsT (u i i' j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u i i' j) (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) + (rsT (u' i' j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u' i j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')))) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by
  first | exact @GlobalTheory.KS.Kunneth.kunneth_symm | exact GlobalTheory.KS.Kunneth.kunneth_symm | (intros; apply GlobalTheory.KS.Kunneth.kunneth_symm <;> assumption)
