import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartX
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

namespace ThetaHol

theorem isHolTo_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) :
    IsHolTo (Set.univ : Set V) (fun _ => y) := by
  intro Uo f
  by_cases h : ⊤ ≤ y ⁻¹ᵁ Uo
  · simp only [Set.mem_univ, true_and, h, Set.ofPred_true]
    exact ⟨isOpen_univ, differentiableOn_const _⟩
  · simp only [Set.mem_univ, true_and, h, Set.ofPred_false]
    exact ⟨isOpen_empty, differentiableOn_empty⟩


end ThetaHol

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem thPt_w {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (z : Fin W.g → ℂ) :
    𝟙 (Sp ℂ) ≫ (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left ≫ Xo.univ.t.G.hom := by
  exact (Category.id_comp _).trans (W.pt.trans (Over.w (W.F.ex (W.ik k) W.Pm z)).symm)

def thPt {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (z : Fin W.g → ℂ) :
    Sp ℂ ⟶ Gx (U.un k x).x :=
  (pullback.lift (𝟙 (Sp ℂ)) (W.F.ex (W.ik k) W.Pm z).left (thPt_w W z) :
    Sp ℂ ⟶ pullback (U.un k x).x Xo.univ.t.G.hom)




end Main

end ReciprocityTheory.ChartRestriction.G.PullbackSections
