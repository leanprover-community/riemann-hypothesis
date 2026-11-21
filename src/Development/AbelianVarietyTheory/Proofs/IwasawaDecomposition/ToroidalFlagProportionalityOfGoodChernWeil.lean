import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodBase

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Member

theorem selfInter_Lw_interPoly : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}
    (C : FlagCpt Z e) (la : GlobalTheory.AllWt.Weight Dw),
    ((C.Y.inter (fun _ => C.Lw la) : ℤ) : ℝ) =
      C.Y.interPoly (fun x : Root Dw.mult => C.gr x.1 x.2)
        ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ C.Y.dim) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C la
  rw [← Fin.prod_const]
  have h := C.Y.interPoly_prod_sum (fun x : Root Dw.mult => C.gr x.1 x.2)
    (fun _ x => -(GlobalTheory.AllWt.exOf Dw la 0 (some x)))
  push_cast at h
  rw [h]
  congr 2
  funext i
  simp only [FlagCpt.Lw, FlagCpt.LEx, AddMonoidHom.coe_mk, ZeroHom.coe_mk, neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.Member
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Proportionality

theorem hasChernIntegral_unique {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {O : X.X.Opens} {H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ} {R : MvPolynomial (ι × ℕ) ℝ}
    {t t' : ℝ} (h : HasChernIntegral E O H R t) (h' : HasChernIntegral E O H R t') : t = t' :=
  h.2.symm.trans h'.2

theorem mumfordProportionality_of_goodChernWeil (h : GlobalTheory.Published.GoodChernWeil) : GlobalTheory.Published.MumfordProportionality := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k la
  obtain ⟨X, Eb, E', φ, f, Ob, Hm, hf, hg, hH, hG, hint⟩ := GlobalTheory.LieBase.exists_goodBase E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  obtain ⟨R, hR⟩ := GlobalTheory.AntisymmChern.antisymm_eq_chernRoots_mul_rootDiscr _ Dw.mult
    ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim)
  rw [GlobalTheory.Member.selfInter_Lw_interPoly (Φ.C k) la]
  have key := hasChernIntegral_unique (h.flag hf hg hH hG hR) (hint la R hR)
  convert key using 3 <;> exact Subsingleton.elim _ _

end GlobalTheory.Proportionality
end
end
