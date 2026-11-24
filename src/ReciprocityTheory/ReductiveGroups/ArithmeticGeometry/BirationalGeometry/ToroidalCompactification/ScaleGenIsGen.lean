module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

section Transport

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

def scaleGen {M : LB X} (t : LB.Gen M) (c : Γ(X, ⊤)ˣ) : LB.Gen M := ⟨fun i => res le_top c * t.s i⟩

theorem gm_scaleGen {M : LB X} (t : LB.Gen M) (c : Γ(X, ⊤)ˣ) (r : Z ⟶ X) (z : Z) (i : M.ι) (h : r z ∈ M.U i) :
    gm r z (M.U i) ((scaleGen t c).s i) = gm r z ⊤ c * gm r z (M.U i) (t.s i) := by
  have hT : r z ∈ (⊤ : X.Opens) := trivial
  have e : X.presheaf.map (homOfLE (le_top : M.U i ≤ ⊤)).op ≫ r.app (M.U i) ≫
      Z.presheaf.germ (r ⁻¹ᵁ M.U i) z h = r.app ⊤ ≫ Z.presheaf.germ (r ⁻¹ᵁ ⊤) z hT := by
    first
      | (rw [Scheme.Hom.naturality_assoc]; congr 1; exact TopCat.Presheaf.germ_res _ _ _ _)
  have key : gm r z (M.U i) (res le_top c) = gm r z ⊤ c := by
    unfold gm
    rw [dite_eq_left h, dite_eq_left hT]
    ext
    exact congrArg (fun f => f.hom (c : Γ(X, ⊤))) e
  show gm r z (M.U i) (res le_top c * t.s i) = _
  rw [map_mul, key]

theorem scaleGen_isGen {M : LB X} (hM : M.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
    (ht : t.IsGen) (c : Γ(Y, ⊤)ˣ) : (scaleGen t c).IsGen := by
  have rr : ∀ {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)ˣ),
      res h2 (res h1 x) = res (h2.trans h1) x := by
    intro U V W h1 h2 x
    ext
    show (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom (x : Γ(Y, U))) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom (x : Γ(Y, U))
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
    rfl
  unfold LB.Gen.IsGen
  intro i j
  show res _ (res le_top c * t.s i) = _ * res _ (res le_top c * t.s j)
  rw [map_mul, map_mul, rr, rr, ht i j]
  exact mul_left_comm _ _ _

end Transport

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}

end Pull

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
