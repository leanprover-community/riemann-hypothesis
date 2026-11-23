module

import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullGenBoxGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxSymLoc

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res)
open ReciprocityTheory.ChartRestriction.G.Out.LBxP

variable {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]

lemma gU_pull_box_g (F : J → (X' ⟶ X)) (a : Y ⟶ X') (i j : J → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.LinComb L F (fun _ => 1)).U i ⊓ (LB.LinComb L F (fun _ => 1)).U j))
    (hy' : ∀ m, y ∈ (a ≫ F m) ⁻¹ᵁ (L.U (i m) ⊓ L.U (j m))) :
    gU y hy (pullU a _ ((LB.LinComb L F (fun _ => 1)).g i j)) =
      ∏ m, gU y (hy' m) (pullU (a ≫ F m) _ (L.g (i m) (j m))) := by
  refine (gU_pullU a _ y hy _).trans ?_
  have e := gU_lcg L F (fun _ => 1) i j (a.base y) hy
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom)) e).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun m _ => ?_)
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom)) (zpow_one _)).trans ?_
  refine (gU_pullU a _ y _ _).symm.trans ?_
  exact gU_pullU_comp a (F m) _ _ y _ _

lemma isGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  apply GlobalTheory.BoxCubical.isGen_boxGen <;> assumption

lemma exists_restrict {S : Scheme.{0}} {A B : Over S} (f : A ⟶ B) (U : S.Opens) :
    ∃ ρ : (A.hom ⁻¹ᵁ U).toScheme ⟶ (B.hom ⁻¹ᵁ U).toScheme,
      ρ ≫ (B.hom ⁻¹ᵁ U).ι = (A.hom ⁻¹ᵁ U).ι ≫ f.left := by
  refine ⟨f.left.resLE _ _ ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  rw [← Scheme.Hom.comp_preimage, Over.w]

end GlobalTheory.BoxSymLoc

namespace GlobalTheory

open BoxSymLoc ReciprocityTheory.ChartRestriction.G.Out.LBxP

theorem rigidified_sym_boxLB (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (_hL : L.IsLB) :
    (Rigidified G L → Rigidified G' (boxLB L p.pr)) ∧
      (Out.Sym G L → Out.Sym G' (boxLB L p.pr)) := by
  constructor
  · rintro ⟨t, ht⟩
    have he : ∀ i : Fin j, ∀ _k : PUnit, eSec G' ≫ (p.pr i).left = 𝟙 _ ≫ eSec G := by
      intro i _
      have := p.hom i
      rw [Category.id_comp, eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
    exact ⟨GeneratorPullback.boxGen L (fun i => (p.pr i).left) (fun _ => eSec G') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (p.pr i).left (𝟙 _) (fun _ => eSec G) _ _ (he i) t),
      isGen_boxGen L _ _ _ _ fun i => isGen_pullAlong L _ _ _ _ _ (he i) t ht⟩
  · intro h s
    obtain ⟨U, hs, t, ht⟩ := h s
    refine ⟨U, hs, ?_⟩
    choose ρ hρ using fun i => exists_restrict (p.pr i) U
    have he : ∀ i : Fin j, ∀ k : Fin 2,
        (![(G'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G' ⟶ G').left, (G'.hom ⁻¹ᵁ U).ι] :
          Fin 2 → ((G'.hom ⁻¹ᵁ U).toScheme ⟶ G'.left)) k ≫ (p.pr i).left =
        ρ i ≫ (![(G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ U).ι] :
          Fin 2 → ((G.hom ⁻¹ᵁ U).toScheme ⟶ G.left)) k := by
      intro i k
      have := p.hom i
      fin_cases k
      · have h0 : (GrpObj.inv : G' ⟶ G').left ≫ (p.pr i).left =
            (p.pr i).left ≫ (GrpObj.inv : G ⟶ G).left := inv_pr p i 0
        show ((G'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G' ⟶ G').left) ≫ (p.pr i).left =
          ρ i ≫ (G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left
        rw [Category.assoc, h0, ← Category.assoc, ← hρ i, Category.assoc]
      · exact (hρ i).symm
    exact ⟨GeneratorPullback.boxGen L (fun i => (p.pr i).left) _ _
      (fun i => GeneratorPullback.pullAlong L (p.pr i).left (ρ i) _ _ _ (he i) t),
      isGen_boxGen L _ _ _ _ fun i => isGen_pullAlong L _ _ _ _ _ (he i) t ht⟩

end GlobalTheory
