module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.UU
namespace SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}

@[ext] theorem ext {s t : SecMod p N} (h : ∀ j, s.sec.f j = t.sec.f j) : s = t :=
  DVR.SecOps.sec_ext (s := s.sec) (t := t.sec) h

theorem eq_zero_iff (s : SecMod p N) : s = 0 ↔ ∀ j, s.sec.f j = 0 :=
  ⟨fun h _ => h ▸ rfl, fun h => ext h⟩

section Val
variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ

theorem sval_add (s t : SecMod p (LB.LinComb L φ ε)) :
    sval (s + t).sec r z J = sval s.sec r z J + sval t.sec r z J :=
  gs_add r z _ (hJ.mem φ r) _ _

theorem sval_smul (c : F) (s : SecMod p (LB.LinComb L φ ε)) :
    sval (c • s).sec r z J = gs r z ⊤ (scal p c) * sval s.sec r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans
    (congrArg (· * sval s.sec r z J) (gs_res r z le_top (hJ.mem φ r) _))

end Val


end SecMod
end GlobalTheory.UU
end
