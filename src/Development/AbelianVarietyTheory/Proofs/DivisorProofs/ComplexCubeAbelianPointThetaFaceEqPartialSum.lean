module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def pt3 (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) : Sp ℂ ⟶ (G3 D.P.A).left :=
  (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left

def wI (x y z : Fin g → ℂ) (I : thK) : Fin g → ℂ := ∑ a ∈ I.down, ![x, y, z] a

abbrev cubW (D : DegPre R) (j : thK → D.P.L.ι) : (G3 D.P.A).left.Opens :=
  LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j

theorem psum_eA (ν : NumOf D ℂ N) (d : AB N.toNumB g) {n : ℕ} (w : Fin n → Fin g → ℂ) (I : Finset (Fin n)) :
    psum D.P.A (fun k => ν.eA (d.ex (w k))) I = ν.eA (d.ex (∑ i ∈ I, w i)) := by
  have e0 : ν.eA (d.ex 0) = 1 := by
    have h := d.ex_add 0 0
    rw [add_zero] at h
    have h1 : d.ex 0 = 1 := left_eq_mul.mp h
    rw [h1, map_one]
  have hl : ∀ l : List (Fin n),
      l.foldr (fun k acc => padd D.P.A (ν.eA (d.ex (w k))) acc) (pzero D.P.A _) = ν.eA (d.ex (l.map w).sum) := by
    intro l
    induction l with
    | nil =>
      rw [List.foldr_nil, List.map_nil, List.sum_nil, e0, CategoryTheory.Hom.one_def]
      rfl
    | cons k l ih =>
      rw [List.foldr_cons, ih, List.map_cons, List.sum_cons, d.ex_add, map_mul, padd, CategoryTheory.Hom.mul_def]
  have hI : ((List.finRange n).filter (· ∈ I)).toFinset = I := by
    ext i
    simp
  unfold psum
  rw [hl, ← List.sum_toFinset w ((List.nodup_finRange n).filter _), hI]

theorem complexCubeAbelianPoint_thetaFace_eq_partialSum (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK) :
    pt3 ν d x y z ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (wI x y z I))).left := by
  have e := psum_hom (preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))))) (x3 D.P.A) I.down
  have e' : psum D.P.A (fun i => preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))) (x3 D.P.A i))
      I.down = psum D.P.A (fun k => ν.eA (d.ex (![x, y, z] k))) I.down :=
    congrArg (fun q => psum D.P.A q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])
  rw [e', psum_eA] at e
  rw [pt3, thφ, ← Over.comp_left]
  exact congrArg (fun q => q.left) e

end GlobalTheory.MBLow.Cl.CubHol

end
