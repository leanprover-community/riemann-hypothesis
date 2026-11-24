module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem pmaps_self_of_tautological {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    PMaps w φ φ ε t t (𝟙 Y) := by
  subst hF
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id, gen_trans ht r z (j := p) (j' := q) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq), trF]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hw Z (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)]

end GlobalTheory.TorsionFormCompare
