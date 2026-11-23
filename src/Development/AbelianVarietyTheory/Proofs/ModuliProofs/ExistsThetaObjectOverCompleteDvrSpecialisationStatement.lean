module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectOverCompleteDvrSpecialisation
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_thetaObject_over_complete_dvr_specialisation : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [CharZero R] [Algebra.FiniteType ℤ R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)) (𝔪 : Ideal R), 𝔪.IsMaximal → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V)) (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V) (tF : TObj g (N' ^ 2) J b (spMap (algebraMap V F) ≫ spMap (y.comp β))), (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ tF.Shape Mat κ ∧ tF.Prim w w' ∧ tF.HasTh (𝟙 _) (fun a => algebraMap V F (y (v a))) := by
  first | exact @GlobalTheory.ZM.exists_obj_over_complete_dvr | exact GlobalTheory.ZM.exists_obj_over_complete_dvr | (intros; apply GlobalTheory.ZM.exists_obj_over_complete_dvr <;> assumption)
