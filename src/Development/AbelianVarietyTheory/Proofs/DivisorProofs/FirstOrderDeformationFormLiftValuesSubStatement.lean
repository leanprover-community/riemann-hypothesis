module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationFormLiftValuesSub
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.firstOrderDeformation_form_lift_values_sub : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (U : A'.left.Opens), IsAffineOpen U → ∀ (P : GPt A), P.In (i ⁻¹ᵁ U) → ∀ (y₁ y₂ : Sp (DualNumber P.B) ⟶ A'.left) (h₁ : IsLift i P y₁) (h₂ : IsLift i P y₂) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (c : Fin n → P.B), (∀ a, IsTangent (u a)) → (∀ f : Γ(A'.left, U), valR y₁ U f - valR y₂ U f = (TrivSqZeroExt.inr (∑ a, c a * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B)) → (liftVal h ω.1 h₁ - liftVal h ω.1 h₂).snd = -∑ a, c a * algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
  first | exact @GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd | exact GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd | (intros; apply GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd <;> assumption)
