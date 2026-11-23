module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeomPointThrough
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullLiftOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullUnitEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentableOver
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

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem same_id_map {S : Scheme.{0}} {A T U : Over S} [GrpObj A] {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : Fam A N) (hM : Fam A M) (u : T ⟶ U) :
    Same A N M (𝟙 T) u ↔ (addF A).map u.op (famCls hM) = famCls hN := by
  rw [same_iff_map hN hM, op_id, CategoryTheory.Functor.map_id]
  exact eq_comm

theorem glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (U : Ix → Over S) (M : ∀ i, LB (A ⊗ U i).left), (∀ i, IsChart A (M i)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∃ (i : Ix) (u : Over.mk s ⟶ U i), Same A N (M i) (𝟙 _) u) → ∃ (B : Over S) (P : LB (A ⊗ B).left) (j : ∀ i, U i ⟶ B), Rep A (toUnit B) P ∧ (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, Same A (M i) P (𝟙 _) (j i) := by
  intro S A _ hA Ix U M hM hcov
  obtain ⟨B, x, hu, j, ho, hc, hj⟩ := GlobalTheory.RepOver.representable_over S (addF A) (GlobalTheory.PicGlue.addF_separated S A hA) (GlobalTheory.PicGlue.addF_glue S A hA) Ix U
    (fun i ↦ famCls (hM i).fam)
    (fun i Y u u' h ↦ (hM i).inj Y u u' ((same_iff_map (hM i).fam (hM i).fam u u').2 h))
    (fun i T y ↦ by
      obtain ⟨N, hN, rfl⟩ := famCls_surj y
      obtain ⟨W, hW⟩ := (hM i).chart T N hN
      exact ⟨W, fun Y a ↦ (exists_congr fun u ↦ (same_iff_map hN (hM i).fam a u).symm).trans (hW Y a)⟩)
    (fun T y p ↦ by
      obtain ⟨K, _, _, s, hs⟩ := GlobalTheory.exists_geomPoint_through T.left p
      let a : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s rfl
      obtain ⟨N, hN, e⟩ := famCls_surj ((addF A).map a.op y)
      obtain ⟨i, u, h⟩ := hcov K (s ≫ T.hom) N hN
      exact ⟨i, _, a, u, hs, e.symm.trans ((same_id_map hN (hM i).fam u).1 h).symm⟩)
  obtain ⟨P, hP, rfl⟩ := famCls_surj x
  refine ⟨B, P, j, ⟨hP, fun T t N hN ↦ ?_⟩, ho, hc, fun i ↦ (same_id_map (hM i).fam hP _).2 (hj i)⟩
  obtain ⟨g, hg, hg'⟩ := hu T (famCls hN)
  have k : ∀ g : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ g)) ↔ (addF A).map g.op (famCls hP) = famCls hN :=
    fun g ↦ (same_id_iff hN.isLB hP.isLB g).symm.trans (same_id_map hN hP g)
  exact ⟨g, ⟨toUnit_unique _ _, (k g).2 hg⟩, fun g' h ↦ hg' g' ((k g').1 h.2)⟩

end GlobalTheory.PicGlue
