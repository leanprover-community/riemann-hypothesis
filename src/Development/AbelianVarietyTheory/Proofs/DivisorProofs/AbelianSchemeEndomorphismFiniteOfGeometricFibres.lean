module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbEnd

theorem isFinite_of_isFinite_geomFibres :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  intro S A _ hA φ hgeo
  haveI : IsProper A.hom := hA.proper
  haveI : IsProper (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  haveI : IsProper φ.left := IsProper.of_comp φ.left A.hom
  haveI : LocallyQuasiFinite φ.left := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton φ.left fun y => ?_
    let K := AlgebraicClosure (A.left.residueField y)
    let u : Spec (CommRingCat.of K) ⟶ A.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (A.left.residueField y) K)) ≫
        A.left.fromSpecResidueField y
    let t := u ≫ A.hom
    haveI := hgeo K t
    let φ' := ((Over.pullback t).map φ).left
    let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
    have hup : u p = y := Scheme.fromSpecResidueField_apply y _
    let v : Spec (CommRingCat.of K) ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
    refine ((φ'.finite_preimage_singleton (v p)).image (pullback.fst A.hom t)).subset fun x hx => ?_
    have hx' : φ.left x = u p := by rw [hup]; exact hx
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := u) x p hx'
    let m : pullback φ.left u ⟶ pullback A.hom t :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
        rw [← Over.w φ, ← Category.assoc, pullback.condition, Category.assoc])
    have hm1 : m ≫ pullback.fst A.hom t = pullback.fst _ _ := pullback.lift_fst _ _ _
    have hφ1 : φ' ≫ pullback.fst A.hom t = pullback.fst A.hom t ≫ φ.left :=
      (GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ).w.symm
    have hφ2 : φ' ≫ pullback.snd A.hom t = pullback.snd A.hom t := pullback.lift_snd _ _ _
    have hmv : m ≫ φ' = pullback.snd φ.left u ≫ v := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφ1, ← Category.assoc, hm1, Category.assoc, pullback.lift_fst, pullback.condition]
      · rw [Category.assoc, hφ2, pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    refine ⟨m w, ?_, ?_⟩
    · change φ' (m w) = v p
      rw [← Scheme.Hom.comp_apply, hmv, Scheme.Hom.comp_apply, hw2]
    · rw [← Scheme.Hom.comp_apply, hm1, hw1]
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ.left

end GlobalTheory.AbEnd
