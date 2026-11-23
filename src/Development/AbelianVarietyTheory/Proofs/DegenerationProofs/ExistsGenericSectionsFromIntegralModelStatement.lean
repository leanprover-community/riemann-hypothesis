module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSectionsFromIntegralModel
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

theorem _root_.GlobalTheory.T.exists_generic_sections_from_integral_model : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (J : Type) (σ : J → (u.H k).Sec) (f : J → ∀ α, u.D.toPre.SecB k α), (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) → (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) → ∀ w₀ : W0 u.U.toUnifPre, w₀.IsGen → ∃ (t : J → SecA u.A (PadicAlgCl p) k) (s : J → Fam u.D.toPre (PadicAlgCl p) k), (∀ i, u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ (t i) (s i)) ∧ (∀ i α, (∀ j, (f i α).f j = 0) → ∀ j, ((s i).s α).f j = 0) ∧ ∀ (a : u.PtC) (v : J → PadicAlgCl p), Crd (u.H k) σ (u.toG a) v → Crd (LPow u.A.A u.A.L (k : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v := by
  first | exact @GlobalTheory.ZH.IntegralCarry.exists_carry | exact GlobalTheory.ZH.IntegralCarry.exists_carry | (intros; apply GlobalTheory.ZH.IntegralCarry.exists_carry <;> assumption)
