module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGe
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_integralExpansions_of_valuation_ge : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (q : ℕ), 1 ≤ q → ∀ (s : Fam D.toPre F q) (r : ℚ), (∀ χ, VGe D F v q χ (s.s χ) r) → ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α), (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i)) ∧ (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ ∀ α : D.toPre.X, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε q) (s.s α) (D.toPre.famφB α) (DegPre.famε q) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) := by
  first | exact @GlobalTheory.exists_integral_expansions_of_vge | exact GlobalTheory.exists_integral_expansions_of_vge | (intros; apply GlobalTheory.exists_integral_expansions_of_vge <;> assumption)
