import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvRSumSmulFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOneClassSeriesDescends
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaClassSumDominantWeightIsCuspForm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedIntegralBasisHarmonicPolynomials

section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_oneClass_series_descends : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ w : (Fin n → LevQ Dw d.l₂) → c.F, DatEq d ψ w → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∃ f ∈ sec Xo c a n, IsThClsD Xo c d (fun _ : Unit => w) (fun _ => Λ) (fun _ => N) (fun _ => 1) 1 (fun _ => 1) LinearMap.id (fun _ => P) f := by
  first | exact @GlobalTheory.ClsDescent.exists_sec_oneClass | exact GlobalTheory.ClsDescent.exists_sec_oneClass | (intros; apply GlobalTheory.ClsDescent.exists_sec_oneClass <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

theorem GlobalTheory.exists_sec_isThClsD : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), (∀ j, DatEq d ψ (w j)) → LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∃ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f := by
  intro hCI E _ _ _ H Dw l Xo c n d hlev hA hN ψ hψ Cl _ w La Nc gam vol ep Vs _ _ io xs a hw hL hio
  choose f hf hth using fun j : Cl => GlobalTheory.T.exists_section_oneClass_series_descends hCI E H Dw l Xo c n d hlev hA hN ψ hψ (w j) (hw j) (La j) (Nc j)
    (hL j).1 (hL j).2.1 (hL j).2.2 a (io (xs j)) (hio j)
  refine ⟨∑ j, (vol * ((gam j : c.F))⁻¹ * ep j) • f j,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hf j), ?_⟩
  intro k _ _ _ _ hk y y₂ hy
  choose vc hvc hev using fun j => hth j k hk y y₂ hy
  refine ⟨fun j => vc j (), fun j => hvc j (), ?_⟩
  rw [GlobalTheory.evR_sum_smul_fin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hev j]
  simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, mul_one, map_one, one_mul]
  ring
end

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_levelCover_thetaClassSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), (∀ j, DatEq d ψ (w j)) → LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∃ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f := by
  atlas_forward_decl GlobalTheory.exists_sec_isThClsD
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaClassSum_dominant_weight_isCuspForm : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → l.A = 1 → d.IsLev → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → LastPos Dw a → LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f → f ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  first | exact @GlobalTheory.ClsVal.isThClsD_mem_cusp | exact GlobalTheory.ClsVal.isThClsD_mem_cusp | (intros; apply GlobalTheory.ClsVal.isThClsD_mem_cusp <;> assumption)
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ClsVal

namespace GlobalTheory.ClsVal

theorem exists_cusp_isThClsD_unique : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → Formalism.L2.Pj.IsUnf (U σ)) → l.A = 1 → CovPin Xo c (fun _ : Unit => d) → GlobalTheory.Dict.UnitC d → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (bad : ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → LastPos Dw a → (∀ j, DatEq d ψ (w j)) → RepsOK (l := d.l₂) bad La Nc gam → LinearMap.range io ≤ Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ xs : Cl → Vs, ∃ f ∈ Formalism.L2.Pj.cusp Xo c U a n, IsThClsD Xo c d w La Nc gam vol ep io xs f ∧ ∀ f' ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f' → f' = f := by
  intro hci E _ _ _ H Dw l Xo c n d r U hr hU hA hcov hunit ψ hψ Cl _ w La Nc gam bad vol ep Vs _ _ io a hD hL hw hreps
    hio xs
  obtain ⟨hlev, hA₂, hnab⟩ := hcov ()
  have hLat : LatsOK d.l₂.M La Nc := fun k => ⟨(hreps k).1, (hreps k).2.2.1, (hreps k).2.2.2.1⟩
  have hP : ∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := fun v =>
    GlobalTheory.HarmBasis.mem_HHa_of_mem_span subset_rfl (hio (LinearMap.mem_range_self io v))
  obtain ⟨f, hf, hcls⟩ := GlobalTheory.T.exists_section_of_levelCover_thetaClassSum hci E H Dw l Xo c n d hlev (hA₂.trans hA.symm) hnab ψ hψ Cl w La Nc gam vol ep
    Vs io xs a hw hLat fun j => hP _
  refine ⟨f, ?_, hcls, fun f' hf' hcls' => ?_⟩
  · rw [← Formalism.L2.PjFree.cusp_ofPj]
    exact GlobalTheory.T.thetaClassSum_dominant_weight_isCuspForm hci E H Dw l Xo c n d r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
      (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ)) hA hlev hA₂ hnab hunit Cl w La Nc gam vol ep Vs io xs a
      hD hL hLat (fun j => hP _) f hf hcls
  · exact GlobalTheory.ClassSumUnique.isThClsD_unique hci E H Dw l Xo c n d Cl w La Nc gam vol ep Vs io hlev hnab hLat a hP xs a n
      f' hf' f hf hcls' hcls

end GlobalTheory.ClsVal
end
