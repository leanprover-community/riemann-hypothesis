module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
public import Formalism.LocalToGlobal.ProjectiveLattices.RecConj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

variable {σ : c.F →+* ℂ} {r : ℕ}

section Riemann

variable {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U)
  {a : ℝ} (ha : ∀ k (τ : (U.X k).Ψ), (τ.1 (-(U.X k).ξ0)).im = a) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1)
include hσ hU ha hx

end Riemann

theorem isCombAt_co {y y' : FrPt Xo c (CAt σ)} (e : y'.x = y.x) {g : EigFrame Z σ ((cxPt Z y).1 ≫ genι Z)}
    (hg : ∀ τ i, g.v τ i = (cxFrame Z y').v τ i) (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) :
    IsCombAt y.x (y.u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (cxFrame Z y).co g τ b' b) (y'.u τ b) := by
  obtain ⟨x, xo, u, ut, ue, ub, s, sg⟩ := y'
  dsimp only at e
  subst e
  let L := lieEquiv (S := CAt σ) Z y (x := (cxPt Z y).1 ≫ genι Z) (Category.assoc _ _ _).symm
  refine (isComb_iff (t := Xo.univ.t) (S := CAt σ) (fun i => tanOf (y.tan τ i)) _ (tanOf (ut τ b))).2 (L.injective ?_)
  exact (tan_ext (w := g.vec τ b) (hg τ b).symm).trans (((cxFrame Z y).vec_eq g τ b).trans
    ((map_sum L _ _).trans (Finset.sum_congr rfl fun _ _ => map_smul L _ _)).symm)

theorem x_eq_of_cxPt {y y' : FrPt Xo c (CAt σ)} (h : (cxPt Z y).1 = (cxPt Z y').1) : y.x = y'.x := by
  have := Z.jQ_open
  rw [← ptF_fst (S := CAt σ) y, ← ptF_fst (S := CAt σ) y']
  exact congrArg (· ≫ _) ((cancel_mono Z.jQ).1 h)

variable (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)

def IsHodgeFrame (y : CxPts (genStr Z) σ) (g : EigFrame Z σ (y.1 ≫ genι Z)) : Prop :=
  ∃ (ψ : ℂ →+* ℂ) (σ' : c.F →+* ℂ) (k : (U σ').Comp) (x : ((U σ').X k).dom),
    (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) ∧ σ' = ψ.comp σ ∧ Formalism.L2.PjFree.GoodEmb c σ' ∧ IsOrth ((U σ').X k) x.1 ∧
      (cxPt Z ((U σ').un k x)).1 = spMap ψ ≫ y.1 ∧ g.IsMap ψ (cxFrame Z ((U σ').un k x))

open Classical in
def EigMet.hodge (b : ℝ) (hb : 0 < b) (G₀ : EigMet Z σ) : EigMet Z σ where
  gram y g τ := if h : ∃ f, IsHodgeFrame U y f then (b : ℂ) • ((h.choose.co g τ)ᴴ * h.choose.co g τ) else G₀.gram y g τ
  pos y g τ := by
    split_ifs with h
    · exact (PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit
        ((isUnit_iff_isUnit_det _).2 (h.choose.isUnit_det_co g τ)))).smul (Complex.zero_lt_real.2 hb)
    · exact G₀.pos y g τ
  change y f g τ := by
    split_ifs with h
    · rw [← h.choose.co_mul f g]
      simp only [conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    · exact G₀.change y f g τ

variable {U} {y : CxPts (genStr Z) σ} {f g : EigFrame Z σ (y.1 ≫ genι Z)}

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [dualMap]

theorem isHodgeFrame_cxFrame (hσ : Formalism.L2.PjFree.GoodEmb c σ) {k : (U σ).Comp} {x : ((U σ).X k).dom}
    (hx : IsOrth ((U σ).X k) x.1) : IsHodgeFrame U (cxPt Z ((U σ).un k x)) (cxFrame Z ((U σ).un k x)) :=
  ⟨_, σ, k, x, .inl rfl, rfl, hσ, hx, by rw [show spMap (RingHom.id ℂ) = 𝟙 _ from Spec.map_id _, Category.id_comp],
    fun _ _ => by rw [spMap_dualMap_id, Category.id_comp]⟩

variable (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ))
include hU

variable {a : ℝ} (ha0 : 0 < a) (ha : ∀ σ k (τ : ((U σ).X k).Ψ), (τ.1 (-((U σ).X k).ξ0)).im = a)
include ha0 ha

variable {b : ℝ} {hb : 0 < b} {G₀ : EigMet Z σ}

end Free

end GlobalTheory.ShFam
