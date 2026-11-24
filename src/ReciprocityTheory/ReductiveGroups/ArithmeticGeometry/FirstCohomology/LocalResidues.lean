module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.H1.LocalResidues

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {k : Type} [Field k] {X W Z : Scheme.{0}}

theorem sval_rel {L : LB X} {K : Type} [Fintype K] {φ : K → (W ⟶ X)} {ε : K → ℤ}
    (s s₀ : LB.Sec (LB.LinComb L φ ε)) (D : W.Opens) (rr : Γ(W, D))
    (hrel : ∀ j, (W.presheaf.map (homOfLE (inf_le_right : D ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U j)).op).hom
        (s.f j) =
      (W.presheaf.map (homOfLE (inf_le_left : D ⊓ (LB.LinComb L φ ε).U j ≤ D)).op).hom rr *
      (W.presheaf.map (homOfLE (inf_le_right : D ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U j)).op).hom
        (s₀.f j))
    (r : Z ⟶ W) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (hz : r z ∈ D) :
    sval s r z J = gs r z D rr * sval s₀ r z J := by
  have hm : r z ∈ D ⊓ (LB.LinComb L φ ε).U (fun k => J (r ≫ φ k)) := ⟨hz, hJ.mem φ r⟩
  have e := congrArg (gs r z _) (hrel (fun k => J (r ≫ φ k)))
  rw [gs_res r z _ hm, gs_mul r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  exact e

end ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
