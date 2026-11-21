import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionsTransportLocalLatticeIsometries
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEllipticElementsOfLocalLatticeIsomet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasure

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsomPhi

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (gam centMeas orbCls torEmb)

theorem tor_mul_comm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] (a b : Tor P k) : a * b = b * a := by
  apply Subtype.ext
  show a.1 * b.1 = b.1 * a.1
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem map_isHaar_rightInv {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [MeasurableSpace (Tor P k)] [BorelSpace (Tor P k)]
    [IsTopologicalGroup (Tor P k)] (e : Tor P k ≃ₜ* H) (dt : Measure (Tor P k)) [dt.IsHaarMeasure] :
    (dt.map e).IsHaarMeasure ∧ (dt.map e).IsMulRightInvariant := by
  haveI h1 : (dt.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map dt e.toMulEquiv e.continuous e.symm.continuous
  refine ⟨h1, ⟨fun g => ?_⟩⟩
  have hc : (fun x : H => x * g) = fun x => g * x := funext fun x => by
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tor_mul_comm]
  rw [hc]
  exact map_mul_left_eq_self _ g

set_option maxHeartbeats 4000000 in
open GlobalTheory.Orb in

theorem phi_map : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  intro D V V' r P v j hj μ dt f hμ hdt hok hok'
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  obtain ⟨hX, hmv⟩ := GlobalTheory.T.unitaryTorusEllipticElements_of_localLatticeIsometry _ _ D.sp.cm.sig hcm r V.rank V'.rank P V.gram V'.gram (frameLat V) (frameLat V')
    v j hj
  unfold Phi
  rw [← finsum_comp_equiv (Equiv.setCongr hX.symm)]
  refine finsum_congr fun q => ?_
  obtain ⟨c, h2⟩ := q
  obtain ⟨x, φ, hc, h⟩ := id h2
  subst hc
  obtain ⟨φ'', h'', hγ, ht⟩ := hmv x φ h
  obtain ⟨e, he, hme⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure _ _ D.sp.cm.sig hcm r V.rank P V.gram (isHermND_gram V) (Fv D.host.F v) x φ h
  obtain ⟨e'', he'', hme''⟩ :=
    GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure _ _ D.sp.cm.sig hcm r V'.rank P V'.gram (isHermND_gram V') (Fv D.host.F v) x φ'' h''
  haveI := hμ
  haveI := hdt
  obtain ⟨i1, i2⟩ := map_isHaar_rightInv P (Fv D.host.F v) e dt
  haveI : (centMeas h dt).IsHaarMeasure := by rw [hme dt]; exact i1
  haveI : (centMeas h dt).IsMulRightInvariant := by rw [hme dt]; exact i2
  have v1 := (hok.2 x φ h).orbInt_eq
  have v2 := (hok'.2 x φ'' h'').orbInt_eq
  have hm : centMeas h'' dt = (centMeas h dt).map (centEquiv j (gam h) hγ.symm) := by
    rw [hme'', hme dt, Measure.map_map (map_continuous (centEquiv j (gam h) hγ.symm)).measurable (map_continuous e).measurable]
    congr 1
    funext t
    apply Subtype.ext
    rw [he'', ht, ← he]
    rfl
  calc orbCls (J := V'.gram) (μ.map j) dt (f ∘ j.symm) ((Equiv.setCongr hX.symm) ⟨QuotientGroup.mk x, h2⟩)
      = orbInt (μ.map j) (gam h'') (centMeas h'' dt) (f ∘ j.symm) := v2.symm
    _ = orbInt (μ.map j) (gam h'') ((centMeas h dt).map (centEquiv j (gam h) hγ.symm)) (f ∘ j.symm) := by rw [hm]
    _ = orbInt μ (gam h) (centMeas h dt) ((f ∘ j.symm) ∘ j) := (hasOrbInt_map j hγ.symm (f ∘ j.symm) 0).2
    _ = orbInt μ (gam h) (centMeas h dt) f := by
      congr 1
      funext y
      simp
    _ = orbCls (J := V.gram) μ dt f ⟨QuotientGroup.mk x, h2⟩ := v1

end GlobalTheory.IsomPhi
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableOrbitalIntegral_preserved_latticeIsometry : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  atlas_forward_decl GlobalTheory.IsomPhi.phi_map
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TraceEqTwo

theorem traceEq_of_geomExpansion : GeomExpansion → TraceEq := by
  intro hG D V lam S M T U μa μf μ _ _ fa ff hTD V' hr S' M' hlam' j hj μa' μ' _ _ fa' hR' hA'
  obtain ⟨-, hTU⟩ := GlobalTheory.T.testFunctions_transport_localLatticeIsometries D V V' hr j hj
  obtain ⟨T', U', hNF, hTF⟩ := hTU T U
  obtain ⟨hodd, hgap, hMl, hnf, hRP, hTA, hTFin⟩ := hTD
  set lam' : D.what₂.Tau → Fin V'.rank → ℤ := fun ρ i => lam ρ (i.cast hr) with hlamdef
  have hTD' : IsTestData V' lam' M' T' U' μa' (fun v => (μf v).map (j v)) μ' fa' (transfer j ff) := by
    refine ⟨hr ▸ hodd, ?_, hlam', hNF hnf, hR', hA', hTF μf ff hTFin⟩
    intro ρ i k hik
    have h := hgap ρ (i.cast hr) (k.cast hr) (by simpa using hik)
    simpa [hr, lam'] using h
  choose dta dtf dt hdt using fun (r : ℕ) (P : PPol D.sp.cm.sig r) => GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.exists_isTorusMeas P
  obtain ⟨hFin, -, hTr⟩ := hG D V lam S M T U μa μf μ fa ff ⟨hodd, hgap, hMl, hnf, hRP, hTA, hTFin⟩
    (dta _) (dtf _) (dt _) (hdt _)
  obtain ⟨hFin', -, hTr'⟩ := hG D V' lam' S' M' T' U' μa' _ μ' fa' _ hTD' (dta _) (dtf _) (dt _) (hdt _)

  have gen : ∀ (r : ℕ) (h : r = V.rank),
      (∀ (P : PPol D.sp.cm.sig r) v, PhiOK (J := V.gram) (μf v) (dtf r P v) (ff v)) ∧
      ∑ᶠ P : PPol D.sp.cm.sig r, ((GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.torVol P (dt r P)).toReal : ℂ) *
          (∏ᶠ v, Phi (J := V.gram) (μf v) (dtf r P v) (ff v)) *
          ∏ ρ : D.what₂.Tau, PhiReal P (embOverOf D ρ) (fun i => lam ρ (i.cast h)) (dta r P (placeOf D ρ)) =
        ∑ᶠ P, GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term V lam μf ff P (dta _ P) (dtf _ P) (dt _ P) := by
    intro r h
    subst h
    exact ⟨fun P v => (hFin P).2.1 v, rfl⟩
  refine ⟨_, hTr, ?_⟩
  convert hTr' using 1
  rw [← (gen _ hr).2]
  refine finsum_congr fun P => ?_
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term
  congr 2
  refine finprod_congr fun v => ?_
  exact (GlobalTheory.T.stableOrbitalIntegral_preserved_latticeIsometry D V V' _ P v (j v) (hj v) (μf v) (dtf _ P v) (ff v) (hRP.2.1 v) ((hdt _ P).2.1 v) ((gen _ hr).1 P v) ((hFin' P).2.1 v)).symm

end GlobalTheory.TraceEqTwo

end
end
