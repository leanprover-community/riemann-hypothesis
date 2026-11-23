module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem etale_of_killed_tangent_trivial : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Flat H.hom → (∀ c ∈ w0 ^ r, i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1) → Etale H.hom := by
  intro p _ D R _ b N w0 r S _ s o H i hfin hflat hkill hrep htan
  haveI := hfin
  haveI := hflat
  haveI : LocallyOfFinitePresentation H.hom := inferInstance
  have hinv : ∀ {T : Over S} (a : T ⟶ o.A) (f : o.A ⟶ o.A) [IsMonHom f], a⁻¹ ≫ f = (a ≫ f)⁻¹ := by
    intro T a f _
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← mul_comp, inv_mul_cancel, one_comp]
  haveI : FormallyUnramified H.hom := by
    refine TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw => ?_
    let x : Sp k ⟶ S := TangentCrit.dualPt k ≫ w ≫ H.hom
    let W : epsPtR x ⟶ H := Over.homMk w hw
    let U : epsPtR x ⟶ H := Over.homMk (TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w)
      (by simp only [Category.assoc]; rfl)
    let e : Over.mk x ⟶ epsPtR x := Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
      (TangentCrit.dualPt_dualBase_assoc k _)
    have heU : e ≫ W = e ≫ U := by
      ext1
      exact (TangentCrit.dualPt_dualBase_assoc k (TangentCrit.dualPt k ≫ w)).symm
    have hv : (W ≫ i) * (U ≫ i)⁻¹ = 1 := by
      refine htan k x _ ?_ ?_
      · have h1 : e ≫ ((W ≫ i) * (U ≫ i)⁻¹) = 1 := by
          rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, heU, mul_inv_cancel]
        exact congrArg (fun q => q.left) h1
      · intro c hc
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        rw [mul_comp, hinv, Category.assoc, Category.assoc, hkill c hc, comp_one, comp_one, inv_one, _root_.mul_one]
    have hWU : W ≫ i = U ≫ i := mul_inv_eq_one.1 hv
    have hk : ∀ c ∈ w0 ^ r, (W ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, hkill c hc, comp_one]
    obtain ⟨y, -, hy⟩ := hrep _ (W ≫ i) hk
    have hW := hy W rfl
    have hU := hy U hWU.symm
    exact congrArg (fun q => q.left) (hW.trans hU.symm)
  exact Etale.of_formallyUnramified_of_flat H.hom

end GlobalTheory.UPel.HT.EtLev
