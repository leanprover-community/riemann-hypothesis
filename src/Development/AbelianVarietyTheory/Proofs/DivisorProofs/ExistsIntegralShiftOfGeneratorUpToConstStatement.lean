module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralShiftOfGeneratorUpToConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_integralShift_of_generator_up_to_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) (N : ℕ) (c : R) (uR : LB.Gen (LB.LinComb Q.P.L (Sum.elim (Q.famφB (0 + N • y)) (fun i => (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left ≫ Q.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen → (∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) N y 0) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * (val uR (DegPre.prB Q (FractionRing R)).left z J).val) → ∃ (w : ∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), (Q.P.A.left.presheaf.stalk z)ˣ) (Sh : Q.SecB N 0 → Q.SecB N (0 + N • y)), ∀ x : Q.SecB N 0, (∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval (Sh x) (𝟙 _) z J = sval x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left z J * (w z J).val) ∧ ∃ x₁ : Q.SecB N (0 + N • y), ShiftEq Q N y 0 x x₁ 0 x₁ ∧ ∀ (Z : Scheme.{0}) (X : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval x₁ X z J = gs (X ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval (Sh x) X z J := by
  first | exact @GlobalTheory.IntegralShift.exists_shift_of_gen | exact GlobalTheory.IntegralShift.exists_shift_of_gen | (intros; apply GlobalTheory.IntegralShift.exists_shift_of_gen <;> assumption)
