import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.NoUnifOfZeroMatrix

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.KModel

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem hasGen_lbPow (φ : K → (Y ⟶ X)) (ε : K → ℤ) (n : ℕ) :
    KerPow.HasGen (lbPow L n) φ ε ↔ KerPow.HasGen L φ (fun k => n * ε k) := by
  have mem : ∀ (j : K → PUnit.{1} → L.ι) (y : Y), y ∈ LB.wchart (lbPow L n) φ j ↔ y ∈ LB.wchart L φ (fun k => j k ⟨⟩) :=
    fun j y => ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 h k) ⟨⟩,
      fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h k⟩
  have key : ∀ (i j : K → PUnit.{1} → L.ι) (y : Y), y ∈ LB.wchart (lbPow L n) φ i → y ∈ LB.wchart (lbPow L n) φ j →
      gm (𝟙 Y) y (LB.wchart (lbPow L n) φ i ⊓ LB.wchart (lbPow L n) φ j) ((LB.LinComb (lbPow L n) φ ε).g i j) =
      gm (𝟙 Y) y (LB.wchart L φ (fun k => i k ⟨⟩) ⊓ LB.wchart L φ (fun k => j k ⟨⟩))
        ((LB.LinComb L φ (fun k => n * ε k)).g (fun k => i k ⟨⟩) (fun k => j k ⟨⟩)) := by
    intro i j y hi hj
    refine (gm_linComb (lbPow L n) φ ε (𝟙 Y) y i j hi hj).trans
      (Eq.trans ?_ (gm_linComb L φ (fun k => n * ε k) (𝟙 Y) y (fun k => i k ⟨⟩) (fun k => j k ⟨⟩) ((mem i y).1 hi) ((mem j y).1 hj)).symm)
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_mul, zpow_natCast]
    exact congrArg (· ^ ε k) ((gm_linComb L (fun _ : PUnit.{1} => 𝟙 X) (fun _ => (n : ℤ)) (𝟙 Y ≫ φ k) y (i k) (j k)
      (Set.mem_iInter.1 hi k) (Set.mem_iInter.1 hj k)).trans (by
        rw [Fintype.prod_unique, Category.comp_id, zpow_natCast]))
  constructor
  · exact KerPow.gen_transfer (M := LB.LinComb (lbPow L n) φ ε) (M' := LB.LinComb L φ (fun k => n * ε k))
      (fun j k _ => j k) (fun j y hy => (mem _ y).2 hy)
      fun i j y hi hj => (key (fun k _ => i k) (fun k _ => j k) y ((mem _ y).2 hi) ((mem _ y).2 hj)).symm
  · exact KerPow.gen_transfer (M' := LB.LinComb (lbPow L n) φ ε) (M := LB.LinComb L φ (fun k => n * ε k))
      (fun j k => j k ⟨⟩) (fun j y hy => (mem _ y).1 hy) fun i j y hi hj => key i j y hi hj

end

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} {T : Over S}









end GlobalTheory.UU.KModel
end
