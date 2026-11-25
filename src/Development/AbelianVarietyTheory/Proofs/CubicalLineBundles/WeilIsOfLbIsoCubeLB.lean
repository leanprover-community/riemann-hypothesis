module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PairingOfLam

open ReciprocityTheory.ChartRestriction.G.Out DescentPairing AdjointOfPairing

theorem val_ratio {X X' Y Y₀ B : Scheme.{0}} {L : LB X} {N : LB X'} (hL : L.IsLB) (hN : N.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y₀ ⟶ X')} {ε' : K' → ℤ}
    (H : LBIso (LB.LinComb N φ' ε') (LB.LinComb L φ ε)) (h : Y ⟶ Y₀)
    (t : LB.Gen (LB.LinComb L (fun k => h ≫ φ k) ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb N (fun k => h ≫ φ' k) ε')) (ht' : t'.IsGen) (p : Y ⟶ B)
    (hp : Function.Surjective p.appTop.hom) {Z : Scheme.{0}} (r r' : Z ⟶ Y) (e₁ : r ≫ h = r' ≫ h)
    (e₂ : r ≫ p = r' ≫ p) (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good N z J') :
    val t r z J * (val t' r z J')⁻¹ = val t r' z J * (val t' r' z J')⁻¹ := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ (i : K → L.ι) (i' : K' → N.ι),
      LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart N (fun k => h ≫ φ' k) i' ≤
        h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart N φ' i') := fun i i' y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i i',
      r z ∈ LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart N (fun k => h ≫ φ' k) i' →
      gm r z _ (res inf_le_left (t.s i) * (res (le i i') (pullU h _ (w.s (i, i'))) * res inf_le_right (t'.s i'))⁻¹) =
        gm r z (LB.wchart L (fun k => h ≫ φ k) i) (t.s i) *
          (gm (r ≫ h) z (LB.wchart L φ i ⊓ LB.wchart N φ' i') (w.s (i, i')) *
            gm r z (LB.wchart N (fun k => h ≫ φ' k) i') (t'.s i'))⁻¹ :=
    fun Z r z i i' hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z _ hz _).trans (gm_pull r h z _ (le i i' hz) _)) (gm_res r z _ hz _))))))
  obtain ⟨c, hc⟩ := glue_unit (⊤ : Y.Opens)
    (fun i : (K → L.ι) × (K' → N.ι) =>
      LB.wchart L (fun k => h ≫ φ k) i.1 ⊓ LB.wchart N (fun k => h ≫ φ' k) i.2) (fun _ => le_top)
    (fun y _ => by
      choose i hi using fun k => exists_chart hL (φ k (h y))
      choose i' hi' using fun k => exists_chart hN (φ' k (h y))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), Set.mem_iInter.2 hi, Set.mem_iInter.2 hi'⟩)
    (fun i => res inf_le_left (t.s i.1) *
      (res (le i.1 i.2) (pullU h _ (w.s (i.1, i.2))) * res inf_le_right (t'.s i.2))⁻¹)
    (fun i j y hy => by
      have hm : (𝟙 Y ≫ h) y ∈ LB.wchart L φ i.1 ⊓ LB.wchart N φ' i.2 ⊓ (LB.wchart L φ j.1 ⊓ LB.wchart N φ' j.2) :=
        ⟨le _ _ hy.1, le _ _ hy.2⟩
      have e : gm (𝟙 Y ≫ h) y (LB.wchart L φ i.1 ⊓ LB.wchart N φ' i.2) (w.s (i.1, i.2)) =
          trF φ ε (𝟙 Y ≫ h) y i.1 j.1 * (trF φ' ε' (𝟙 Y ≫ h) y i.2 j.2)⁻¹ *
            gm (𝟙 Y ≫ h) y (LB.wchart L φ j.1 ⊓ LB.wchart N φ' j.2) (w.s (j.1, j.2)) :=
        (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y ≫ h) y _) (hw (i.1, i.2) (j.1, j.2))).trans
          ((map_mul _ _ _).trans (congrArg₂ (· * ·)
            ((gm_div (LB.LinComb N φ' ε') (LB.LinComb L φ ε) _ y (i.1, i.2) (j.1, j.2) hm).trans
              (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ ε _ y _ _ hm.1.1 hm.2.1)
                (gm_linComb N φ' ε' _ y _ _ hm.1.2 hm.2.2))) (gm_res _ y _ hm _))))
      have f₁ : trF φ ε (𝟙 Y ≫ h) y i.1 j.1 = trF (fun k => h ≫ φ k) ε (𝟙 Y) y i.1 j.1 := by
        simp only [trF, Category.assoc]
      have f₂ : trF φ' ε' (𝟙 Y ≫ h) y i.2 j.2 = trF (fun k => h ≫ φ' k) ε' (𝟙 Y) y i.2 j.2 := by
        simp only [trF, Category.assoc]
      refine (hv _ _ y _ _ hy.1).trans (Eq.trans ?_ (hv _ _ y _ _ hy.2).symm)
      rw [e, f₁, f₂,
        gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, gen_trans ht' (𝟙 Y) y hy.1.2 hy.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  obtain ⟨a, ha⟩ := hp c.val
  have hcv : ∀ r : Z ⟶ Y, (gm r z ⊤ c).val = gs (r ≫ p) z ⊤ a := fun r =>
    (gs_unit r z ⊤ trivial _).symm.trans ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a))
  have key : ∀ r : Z ⟶ Y, gm r z ⊤ c = val t r z J *
      (gm (r ≫ h) z (LB.wchart L φ (fun k => J ((r ≫ h) ≫ φ k)) ⊓ LB.wchart N φ' (fun k => J' ((r ≫ h) ≫ φ' k)))
        (w.s (fun k => J ((r ≫ h) ≫ φ k), fun k => J' ((r ≫ h) ≫ φ' k))) * val t' r z J')⁻¹ := fun r => by
    have hz : r z ∈ LB.wchart L (fun k => h ≫ φ k) (fun k => J ((r ≫ h) ≫ φ k)) ⊓
        LB.wchart N (fun k => h ≫ φ' k) (fun k => J' ((r ≫ h) ≫ φ' k)) :=
      ⟨Set.mem_iInter.2 fun k => hJ ((r ≫ h) ≫ φ k), Set.mem_iInter.2 fun k => hJ' ((r ≫ h) ≫ φ' k)⟩
    rw [val_of t r z J (fun k => J ((r ≫ h) ≫ φ k)) (fun k => by rw [Category.assoc]),
      val_of t' r z J' (fun k => J' ((r ≫ h) ≫ φ' k)) (fun k => by rw [Category.assoc])]
    exact (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (_, _))).trans (hv Z r z _ _ hz))
  have q : gm r z ⊤ c = gm r' z ⊤ c := Units.ext (by rw [hcv, hcv, e₂])
  rw [key, key, e₁] at q
  apply Additive.ofMul.injective
  have q' := congrArg Additive.ofMul q
  simp only [ofMul_mul, ofMul_inv] at q' ⊢
  linear_combination (norm := abel) q'

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

end GlobalTheory.PairingOfLam

namespace GlobalTheory

end GlobalTheory
