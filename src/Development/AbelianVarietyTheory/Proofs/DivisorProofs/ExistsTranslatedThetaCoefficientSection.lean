module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistedSectionThetaTranslateCoef
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN GlobalTheory.PsiRing GlobalTheory.PsiCoef

namespace GlobalTheory.PsiCoefMk

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_twist (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (hu : u.IsGen)
    (th : SecBT D (𝟙_ _) 1 0) :
    ∃ g : SecBT D (𝟙_ _) 1 χ, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval g (lift (toUnit T) y).left z J =
        sval th (lift (toUnit T) (y * cT D T χ)).left z J * (val u (toUnit T).left z J * rigV D z J).val := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * cT D Y χ)
  have hF : FormEq
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) 0 k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1)))
      (famφT D (𝟙_ _) χ) (DegPre.famε 1) := by
    intro U _ h
    have e₁ : τ.left ≫ famφT D (𝟙_ _) 0 1 = famφT D (𝟙_ _) χ 1 := by
      change (τ ≫ (snd _ _ * cT D Y 0)).left = (snd _ _ * cT D Y χ).left
      rw [cT_zero, _root_.mul_one, lift_snd]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [comp_cT, cT_zero]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) 0 3 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) χ 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨g, hg⟩ := exists_sec D.P.isLB hF (pullMulSec th τ.left
    (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ u D.rig) (toUnit Y).left)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hu D.rig_gen) _))
  refine ⟨g, fun T y z J hJ => ?_⟩
  have e₂ : (lift (toUnit T) y).left ≫ τ.left = (lift (toUnit T) (y * cT D T χ)).left := by
    rw [← Over.comp_left]
    congr 1
    refine (comp_lift _ _ _).trans (congrArg₂ lift (toUnit_unique _ _) ?_)
    rw [MonObj.comp_mul, comp_cT, lift_snd]
  have e₃ : (lift (toUnit T) y).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hg _ _ z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, e₂, val_pull hJ, e₃, val_mul hJ]
  congr 4

theorem exists_sec_coef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ b : R, ∃ g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ, GlobalTheory.PsiRing.Coef D χ u th g b := by
  intro R _ _ _ D th χ u hu b
  obtain ⟨g, hg⟩ := exists_twist D χ u hu th
  refine ⟨GlobalTheory.IndivisibleSection.smulSec (scal (𝟙_ _ ⊗ D.P.A).hom b) g, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) y).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom := Over.w _
  have h := GlobalTheory.IndivisibleSection.sval_of_secIsMul (p := (𝟙_ _ ⊗ D.P.A).hom) (a := b)
    (s := GlobalTheory.IndivisibleSection.smulSec (scal (𝟙_ _ ⊗ D.P.A).hom b) g) (t := g) (fun _ => rfl)
    (lift (toUnit T) y).left z hJ
  rw [e₁, hg T y z J hJ] at h
  exact h.trans (by ring)

end GlobalTheory.PsiCoefMk
