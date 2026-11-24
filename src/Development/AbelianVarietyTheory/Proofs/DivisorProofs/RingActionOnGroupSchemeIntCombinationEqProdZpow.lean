module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActSum

theorem act_sum_zsmul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k := by
  intro S A _ _ O _ act h r e c
  let f : Multiplicative O →* (A ⟶ A) := MonoidHom.mk' (fun a => act (Multiplicative.toAdd a)) (fun a b => h.2.2.2 _ _)
  have key : ∀ x : O, act x = f (Multiplicative.ofAdd x) := fun x => rfl
  rw [key, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  rfl

end GlobalTheory.ActSum
