module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusA
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBu
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LeOfPowLePolyMulPow

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace CompanionTheory.PfDual


open GlobalTheory.TrivSubscheme in
theorem exists_closed_locTriv_noeth : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → IsLocallyNoetherian Y.left → ∀ F : LB (A ⊗ Y).left, F.IsLB → ∃ (H : Over S) (j : H ⟶ Y), IsClosedImmersion j.left ∧ ∀ (T' : Over S) (x : T' ⟶ Y), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (A ◁ x).left).pull ((snd A T').left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  intro S A Y _ hB hY F hF
  have h₀ : IsPullback (pullback.fst A.hom Y.hom) (snd A Y).left A.hom Y.hom :=
    IsPullback.of_hasPullback A.hom Y.hom
  obtain ⟨I, hI⟩ := GlobalTheory.TrivSubscheme.exists_idealSheaf
    (GlobalTheory.TrivSubscheme.LocTrivOver (snd A Y).left F)
    GlobalTheory.TrivSubscheme.LocTrivOver.comp GlobalTheory.TrivSubscheme.locTrivOver_of_affine
    (fun U => by
      haveI : IsNoetherianRing Γ(Y.left, U) := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(Y.left, U)) ⟶ S := U.2.fromSpec ≫ Y.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ Y.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A Y).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth Γ(Y.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hB t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun S g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI S g.hom _ _ _ h₃,
        GlobalTheory.TrivSubscheme.locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _).trans
        (GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ Y.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun T' x => ?_⟩
  have h₄ : IsPullback (A ◁ x).left (snd A T').left (snd A Y).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerLeft_left_snd x) h₀
    rw [Over.whiskerLeft_left_fst, Over.w x]
    exact IsPullback.of_hasPullback A.hom T'.hom
  simp only [GlobalTheory.TrivSubscheme.triv_pull_iff]
  rw [← GlobalTheory.TrivSubscheme.locTrivOver_iff h₄, hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ x.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι x.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w x)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨y, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp y.left I.subschemeι)

end CompanionTheory.PfDual
