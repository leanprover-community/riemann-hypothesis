module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_thetaPoint_shape_primitivity_near_generic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (s : Sp R ⟶ Sp o) (s' : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s) (t : TObj g (N' ^ 2) J b s') (v : Ix g (N' ^ 2) → R), TMap t t' (spMap (algebraMap R K)) → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (s'' : Sp R' ⟶ Sp o) (t'' : TObj g (N' ^ 2) J b s''), IsUnit (φ f) → TMap t'' t' (spMap φ) → t''.HasTh (𝟙 _) (fun a => φ (v a)) ∧ t''.Shape Mat κ ∧ t''.Prim w w' := by
  first | exact @GlobalTheory.GenericSpread.exists_ne_zero_hasTh_shape_prim | exact GlobalTheory.GenericSpread.exists_ne_zero_hasTh_shape_prim | (intros; apply GlobalTheory.GenericSpread.exists_ne_zero_hasTh_shape_prim <;> assumption)
