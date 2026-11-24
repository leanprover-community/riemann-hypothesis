module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsAlongGroupHom
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
theorem _root_.GlobalTheory.T.invariantVectorFields_along_groupHom : ∀ (K : Type) [Field K] (A₁ A₀ : Over (Sp K)) [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (w : epsR K ⟶ A₁) (dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)) (c : Fin g → K), IsMonHom f → (∀ a, IsTangent (v a)) → IsTangent w → (∀ a, IsInvDer (v a) (dd a)) → IsInvDer w dw → IsLieComb c v (w ≫ f) → ∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)), dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = ∑ a, constFn A₁.hom _ (c a) * (f.left.app W).hom (dd a W h) := by
  first | exact @GlobalTheory.KS.InvHom.invDer_along_hom | exact GlobalTheory.KS.InvHom.invDer_along_hom | (intros; apply GlobalTheory.KS.InvHom.invDer_along_hom <;> assumption)
