module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudShiftUnitIdentityFractionField
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer

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
open ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.raynaudShift_unitIdentity_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  first | exact @GlobalTheory.ShiftUnit.shift_unit_identity | exact GlobalTheory.ShiftUnit.shift_unit_identity | (intros; apply GlobalTheory.ShiftUnit.shift_unit_identity <;> assumption)
