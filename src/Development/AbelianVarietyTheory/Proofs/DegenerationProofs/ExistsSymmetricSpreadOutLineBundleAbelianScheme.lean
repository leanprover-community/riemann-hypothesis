module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem pull_inv_cls_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) :
    CechPic.pull (GrpObj.inv : G' ⟶ G').left (CechPic.cls L' hL') = CechPic.cls L' hL' ↔
      LBIso ((L.pull (GrpObj.inv : G ⟶ G).left).pull φ) (L.pull φ) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _),
    (CechPic.cls_eq_iff hL' (pull_isLB hL _)).2 e, CechPic.cls_pull hL, CechPic.cls_pull (pull_isLB hL _),
    CechPic.cls_pull hL, ← CechPic.pull_comp, ← CechPic.pull_comp, OddDescent.inv_left_comp h]

theorem exists_sym : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Out.Sym A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Out.Sym G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ e hs
  have := hG.proper
  obtain ⟨a, ha, H⟩ := exists_lbIso G.hom h.1 (pull_isLB hL _) hL
    ((pull_inv_cls_iff h hL hL₀ e).1 (OddDescent.pull_inv_cls_of_sym A hL₀ hs))
  exact ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' e' => OddDescent.sym_of_pull_inv_cls G' hL'
    ((pull_inv_cls_iff h' hL hL' e').2 (H R' g hg _ π G'.hom h'.1.w))⟩

end GlobalTheory.GenSpread
