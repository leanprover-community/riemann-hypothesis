import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrame

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaValue_natural_algebraMap : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w := by
  first | exact @GlobalTheory.thetaValue_natural | exact GlobalTheory.thetaValue_natural | (intros; apply GlobalTheory.thetaValue_natural <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaValue_weight_triangular_frame : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), (P ∈ harmA c a n → ∀ (x : Fin n → Dw.La) (v : S), ThValAt Xo c nab y x P v → ThValAt Xo c nab y' x P (wchar (ex Dw a n) t * v)) ∧ (P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (v : S), ShortValAt Xo c nab w Λ β N P y v → ShortValAt Xo c nab w Λ β N P y' (wchar (ex Dw a n) t * v)) := by
  first | exact @GlobalTheory.thetaValue_weight | exact GlobalTheory.thetaValue_weight | (intros; apply GlobalTheory.thetaValue_weight <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem thetaRule_mem_sec : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ thGen Xo c nab a n, f ∈ sec Xo c a n := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab a n f hf
  obtain ⟨x, P, hP, hR⟩ := hf
  unfold sec secW
  refine ⟨?_, ?_⟩
  · intro p q φ y z hyz
    exact (GlobalTheory.T.thetaValue_natural_algebraMap hL hC E H Dw l Xo c nab hnab p.R q.R φ y z hyz a n x P hP _ _ (hR p y) (hR q z)).symm
  · intro p t y y' hB
    have hid : FrMap (AlgHom.id c.F p.R) y' y' := by
      have hs : spMap (AlgHom.id c.F p.R).toRingHom = 𝟙 _ := by
        simp [spMap]
      have hd : spMap (dualMap (AlgHom.id c.F p.R).toRingHom) = 𝟙 _ := by
        have : dualMap (AlgHom.id c.F p.R).toRingHom = RingHom.id _ := by
          ext z <;> simp [dualMap]
        rw [this]
        simp [spMap]
      refine ⟨?_, ?_, 𝟙 _, ?_, ?_, ?_⟩
      · rw [hs, Category.id_comp]
      · intro τ i
        rw [hd, Category.id_comp]
      · simp
      · rw [hs]
        simp
      · intro i h
        have e : (Gx y'.x).presheaf.map (homOfLE h).op = 𝟙 _ := by
          erw [CategoryTheory.Functor.map_id]
        erw [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp, e]
        rfl
    have h1 := (GlobalTheory.T.thetaValue_weight_triangular_frame hL hC E H Dw l Xo c nab hnab p.R y y' t hB n a P).1 hP x (f p y) (hR p y)
    exact GlobalTheory.T.thetaValue_natural_algebraMap hL hC E H Dw l Xo c nab hnab p.R p.R (AlgHom.id c.F p.R) y' y' hid a n x P hP _ _ (hR p y') h1

end GlobalTheory
end
