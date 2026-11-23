module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.OLinPf

open ReciprocityTheory.ChartRestriction.G.Out Semi

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

namespace ILin

section Base

variable {I : Ideal R} {I' : Ideal R'} (φ : R →+* R')
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  (bc : G' ≅ (Over.pullback (specOf φ)).obj G)

end Base

end ILin

section ILin

variable {I : Ideal R} {I' : Ideal R'} (φ : R →+* R') {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : Unif I D A G}
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  {bc : G' ≅ (Over.pullback (specOf φ)).obj G}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))} {D' : DegData R' I'}
  {hD : IsPullDeg φ D.toPre D'.toPre} {U' : Unif I' D' A' G'}
  {O : Type} [CommRing O] [StarRing O]

namespace ILin

section Val

open Geo.Tor

theorem val_maps {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} (F : X' ⟶ X)
    (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (h : Y' ⟶ Y) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L' ψ ε))
    (hm : LB.Gen.Maps (LB.linCombIso w ψ ε) t' (GeneratorPullback.pullAlong L F h φ ε ψ hψ t))
    (r : Z ⟶ Y') (z : Z) (J' : (Z ⟶ X') → L'.ι) (J : (Z ⟶ X) → L.ι)
    (hJ' : Good L' z J') (hJ : Good L z J) :
    val t (r ≫ h) z J =
      (∏ k, gm (r ≫ ψ k) z _ (w.s (fun _ => J ((r ≫ ψ k) ≫ F), J' (r ≫ ψ k))) ^ ε k) *
        val t' r z J' := by
  let p1 : (LB.LinComb (L.pull F) ψ ε).ι := fun k _ => J ((r ≫ ψ k) ≫ F)
  let p2 : (LB.LinComb L' ψ ε).ι := fun k => J' (r ≫ ψ k)
  have m1 : r z ∈ (LB.LinComb (L.pull F) ψ ε).U p1 :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ ψ k) ≫ F)
  have m2 : r z ∈ (LB.LinComb L' ψ ε).U p2 := Set.mem_iInter.2 fun k => hJ' (r ≫ ψ k)
  have m12 : r z ∈ (LB.LinComb (L.pull F) ψ ε).U p1 ⊓ (LB.LinComb L' ψ ε).U p2 := ⟨m1, m2⟩
  have mt : h.base (r.base z) ∈ LB.wchart L φ (fun k => J ((r ≫ ψ k) ≫ F)) :=
    Set.mem_iInter.2 fun k => by
      have hx := hJ ((r ≫ ψ k) ≫ F)
      have hp : ((r ≫ ψ k) ≫ F).base z = (φ k).base (h.base (r.base z)) := by
        rw [Category.assoc, hψ k]; rfl
      rw [hp] at hx
      exact hx
  have L1 : gm r z ((LB.LinComb (L.pull F) ψ ε).U p1) ((GeneratorPullback.pullAlong L F h φ ε ψ hψ t).s p1) =
      val t (r ≫ h) z J :=
    (gm_res r z _ m1 _).trans ((gm_pull r h z _ mt _).trans
      (val_of t (r ≫ h) z J (fun k => J ((r ≫ ψ k) ≫ F))
        (fun k => congrArg J (by rw [Category.assoc, Category.assoc, hψ k]))).symm)
  have H := congrArg (gm r z ((LB.LinComb (L.pull F) ψ ε).U p1 ⊓ (LB.LinComb L' ψ ε).U p2))
    (hm (p1, p2))
  have W1 : gm r z ((LB.LinComb (L.pull F) ψ ε).U p1 ⊓ (LB.LinComb L' ψ ε).U p2)
      ((LB.linCombIso w ψ ε).s (p1, p2)) =
      ∏ k, gm (r ≫ ψ k) z _ (w.s (fun _ => J ((r ≫ ψ k) ≫ F), J' (r ≫ ψ k))) ^ ε k :=
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans
      (congrArg (· ^ ε k) ((gm_res r z _ m12 _).trans
        (gm_pull r (ψ k) z ((L.pull F).U (p1 k) ⊓ L'.U (p2 k))
          ⟨Set.mem_iInter.1 m1 k, Set.mem_iInter.1 m2 k⟩ _))))
  exact L1.symm.trans ((gm_res r z _ m12 _).symm.trans (H.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) W1 (gm_res r z _ m12 _)))))

end Val

end ILin

end ILin

end ReciprocityTheory.ChartRestriction.G.Out.OLinPf
