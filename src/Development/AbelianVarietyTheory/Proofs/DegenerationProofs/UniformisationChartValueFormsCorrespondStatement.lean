module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespond
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
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.uniformisation_chart_value_forms_correspond : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U₀ : UnifPre I D A G, ∃ U : PreU I D.toPre A G, Under U U₀) ∧ (∀ U : PreU I D.toPre A G, ∃ U₀ : UnifPre I D A G, Under U U₀) ∧ ∀ (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G), Under U U₀ → ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D.toPre (𝟙_ _) k α) (σ₀ : H0 U₀.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α), (∀ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ → ∀ z J, Good U.P.L.L z J → sval σ (𝟙 _) z J = sval σ₁ (snd (𝟙_ _) G).left z J) → (∀ α z J, Good D.toPre.P.L z J → sval (f α) (𝟙 _) z J = sval (f₀ α) (snd (𝟙_ _) D.toPre.P.A).left z J) → (U.ExpT (𝟙_ _) k σ f ↔ ∀ e, U₀.ExpandsAt e k σ₀ f₀) := by
  first | exact @GlobalTheory.LN.PreForm.under_exists_and_expands | exact GlobalTheory.LN.PreForm.under_exists_and_expands | (intros; apply GlobalTheory.LN.PreForm.under_exists_and_expands <;> assumption)
