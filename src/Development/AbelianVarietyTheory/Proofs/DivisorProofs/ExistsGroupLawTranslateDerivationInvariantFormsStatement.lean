module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLawTranslateDerivationInvariantForms
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_groupLawTranslate_derivation_invariantForms : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left) (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1), (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1), (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧ ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  first | exact @GlobalTheory.InvForm.exists_transl_val | exact GlobalTheory.InvForm.exists_transl_val | (intros; apply GlobalTheory.InvForm.exists_transl_val <;> assumption)
