module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section PSHelp

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}}

theorem ps_gm_linCombIso {L M : LB X} (w : LB.Iso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : (LB.LinComb M φ ε).ι × (LB.LinComb L φ ε).ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ (LB.div (LB.LinComb M φ ε) (LB.LinComb L φ ε)).U p) :
    gm r z _ ((LB.linCombIso w φ ε).s p) = ∏ a, gm (r ≫ φ a) z ((LB.div M L).U (p.1 a, p.2 a)) (w.s (p.1 a, p.2 a)) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ M.U (p.1 a) ⊓ L.U (p.2 a) :=
    ⟨LB.wchart_le M φ p.1 a hz.1, LB.wchart_le L φ p.2 a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z ((LB.div M L).U (p.1 a, p.2 a)) hm _)

theorem ps_gs_secOfIso {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB)
    (a : A.ι) (b : B.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ A.U a ⊓ B.U b) :
    gs r z (A.U a) ((secOfIso t hu hA hB).f a) =
      ((gm r z ((LB.div B A).U (b, a)) (u.s (b, a)))⁻¹).val * gs r z (B.U b) (t.f b) := by
  refine (gs_res r z inf_le_left hz _).symm.trans ?_
  refine (congrArg (gs r z (A.U a ⊓ B.U b)) (secOfIso_spec t hu hA hB a b)).trans ?_
  unfold isoCand
  refine (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ?_ (gs_res r z inf_le_right hz _))
  rw [gs_unit r z _ hz, map_inv, gm_res r z (divLe a b) hz]

end PSHelp

section ScalB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

end ScalB

end ReciprocityTheory.ChartRestriction.G.DVR
