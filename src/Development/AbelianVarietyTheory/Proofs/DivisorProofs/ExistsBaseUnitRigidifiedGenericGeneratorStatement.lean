module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseUnitRigidifiedGenericGenerator
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

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_baseUnit_rigidifiedGenericGenerator : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → ∀ (eA : Sp K ⟶ pullback X.hom (spMap (algebraMap R K))), eA ≫ pullback.fst X.hom (spMap (algebraMap R K)) = spMap (algebraMap R K) ≫ e → ∀ (M : LB X.left) (rig : LB.Gen (M.pull e)) (c : LB.Gen (M.pull (pullback.fst X.hom (spMap (algebraMap R K))))), M.IsLB → rig.IsGen → LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ c eA) (LB.pullGen M _ _ rig (spMap (algebraMap R K))) → ∀ (a : Kˣ) (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ pullback X.hom (spMap (algebraMap R K))) (z : Z), pullback.fst X.hom (spMap (algebraMap R K)) (r z) ∈ M.U i → (gm (r ≫ pullback.fst X.hom (spMap (algebraMap R K))) z (M.U i) (u.s i)).val = gs (r ≫ pullback.snd X.hom (spMap (algebraMap R K))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull (pullback.fst X.hom (spMap (algebraMap R K)))).U fun _ => i) (c.s fun _ => i)).val) → ∃ b : Rˣ, algebraMap R K (b : R) = (a : K) := by
  first | exact @GlobalTheory.rigUnit_exists | exact GlobalTheory.rigUnit_exists | (intros; apply GlobalTheory.rigUnit_exists <;> assumption)
