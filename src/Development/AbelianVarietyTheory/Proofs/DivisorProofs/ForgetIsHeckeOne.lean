module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromPStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LKGeo.ForgetHecke

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem lattice_dvd (n : ℕ) (hn : 0 < n) (hp : n.Coprime p) (z : D.La)
    (h : ∃ w ∈ LaHat D, inAf D z = n • w) : ∃ u : D.La, z = n • u :=
  GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul p D n hn hp (GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP p n hn hp) z h

def inAfHom (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D where
  toFun := inAf D
  map_zero' := by simp [inAf]
  map_add' x y := by simp [inAf, TensorProduct.tmul_add]

theorem acts_one_iff {G : HTGroup p} (L : GlobalTheory.LKGeo.Link D G) (n : ℕ) (hn : 0 < n) (hp : n.Coprime p) (x y : D.La) :
    (∃ w ∈ LaHat D, ((1 : ℕ) : ℤ) • L.actG 1 (inAf D x) = inAf D y + n • w) ↔ ∃ u : D.La, x - y = n • u := by
  simp only [map_one, Nat.cast_one, one_smul, one_apply_eq_self]
  constructor
  · rintro ⟨w, hw, e⟩
    refine lattice_dvd n hn hp _ ⟨w, hw, ?_⟩
    change inAfHom D (x - y) = _
    rw [map_sub]
    change inAf D x - inAf D y = _
    rw [e]; abel
  · rintro ⟨u, hu⟩
    refine ⟨inAf D u, AddSubgroup.subset_closure ⟨1, u, fun v => ?_, ?_⟩, ?_⟩
    · rw [map_one]; exact (v.1.adicCompletionIntegers ℚ).one_mem
    · rfl
    · have h1 : x = y + n • u := by rw [← hu]; abel
      rw [h1]
      change inAfHom D (y + n • u) = inAfHom D y + n • inAfHom D u
      rw [map_add (f := _), map_nsmul]

end GlobalTheory.LKGeo.ForgetHecke

namespace GlobalTheory.LKGeo.ForgetHecke

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

end GlobalTheory.LKGeo.ForgetHecke
