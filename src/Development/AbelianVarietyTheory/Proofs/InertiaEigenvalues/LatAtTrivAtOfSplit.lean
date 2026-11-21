import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul

section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → (∀ Q ∈ S, (p : 𝓞 E) ∉ Q.asIdeal) → (∀ Q ∉ S, ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p G.1 ∧ Bnd p (G⁻¹).1 := by
  first | exact @GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | exact GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | (intros; apply GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite <;> assumption)
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrimeLat

variable {E : Type} [Field E] [NumberField E]

theorem val_intMul_le_one (c : 𝓞 E) (z : FiniteAdeleRing (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E))
    (hz : Valued.v (z Q) ≤ 1) :
    Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) * z) Q) ≤ 1 := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, Valuation.map_mul, ← hev, ← hev]
  refine mul_le_one' ?_ hz
  exact (GlobalTheory.CharLocProd.val_algebraMap Q (c : E)).trans_le (Q.valuation_le_one c)

theorem val_smul_mulVec_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (m : ℕ)
    (hM : ∀ i j (Q : HeightOneSpectrum (𝓞 E)), Valued.v ((((m : FiniteAdeleRing (𝓞 E) E) * M i j)) Q) ≤ 1)
    (y : Fin n → FiniteAdeleRing (𝓞 E) E) (hy : ∀ j (Q : HeightOneSpectrum (𝓞 E)), Valued.v (y j Q) ≤ 1)
    (c : 𝓞 E) (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((((algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E)) * (m : FiniteAdeleRing (𝓞 E) E)) •
      (M *ᵥ y)) i Q) ≤ 1 := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  have e : (((algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E)) * (m : FiniteAdeleRing (𝓞 E) E)) • (M *ᵥ y)) i =
      ∑ j, algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) * (((m : FiniteAdeleRing (𝓞 E) E) * M i j) * y j) := by
    rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, hev, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [← hev]
  refine val_intMul_le_one c _ Q ?_
  rw [hev, map_mul, Valuation.map_mul, ← hev, ← hev]
  exact mul_le_one' (hM i j Q) (hy j Q)

end GlobalTheory.StdAtPrimeLat

open GlobalTheory.StdAtPrimeLat in

theorem GlobalTheory.StdAtPrimeLat.trivAt_hLat_of_bnd : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (p : ℕ) (g : Bridge.Gf V), Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom g.1).1 → Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom g.1)⁻¹.1 → (⟨Bridge.hLat V g⟩ : GenLat D.host.E V.rank).TrivAt p := by
  intro D ι h1 h2 V hL p g hA hB
  obtain ⟨m₁, hm₁, hA⟩ := hA
  obtain ⟨m₂, hm₂, hB⟩ := hB
  set A := (Matrix.GeneralLinearGroup.map ι.toRingHom g.1).1 with hAdef
  set B := (Matrix.GeneralLinearGroup.map ι.toRingHom g.1)⁻¹.1 with hBdef
  have hAB : A * B = 1 := Units.mul_inv _
  have memH := fun x => GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL g x
  have memS : ∀ x : Fin V.rank → D.host.E, x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank ↔
      ∀ i Q, Valued.v ((fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) i Q) ≤ 1 := by
    intro x
    rw [← hL, GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL 1 x]
    simp
  have hsm : ∀ (r : 𝓞 D.host.E) (x : Fin V.rank → D.host.E),
      (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((r • x) j)) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (r : D.host.E) •
          fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j) :=
    fun r x => funext fun j => map_mul _ (r : D.host.E) (x j)
  refine ⟨m₁ * m₂, Nat.Coprime.mul hm₁ hm₂, ?_, ?_⟩
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [memS, hsm]
    rw [memH] at hx
    have ex : (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) =
        A *ᵥ (B *ᵥ fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) := by
      rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    have ec : algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * ((m₁ * m₂ : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * (m₂ : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) *
          (m₁ : FiniteAdeleRing (𝓞 D.host.E) D.host.E) := by
      push_cast
      ring
    intro i Q
    rw [ec, ex]
    exact val_smul_mulVec_le_one A m₁ hA _ hx _ i Q
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [memH, hsm]
    rw [memS] at hx
    have ec : algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * ((m₁ * m₂ : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * (m₁ : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) *
          (m₂ : FiniteAdeleRing (𝓞 D.host.E) D.host.E) := by
      push_cast
      ring
    intro i Q
    rw [ec, Matrix.mulVec_smul]
    exact val_smul_mulVec_le_one B m₂ hB _ hx _ i Q
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_entries_integral : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (p : ℕ) (g : Bridge.Gf V), Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom g.1).1 → Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom g.1)⁻¹.1 → (⟨Bridge.hLat V g⟩ : GenLat D.host.E V.rank).TrivAt p := by
  atlas_forward_decl GlobalTheory.StdAtPrimeLat.trivAt_hLat_of_bnd
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

theorem GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (V : HSp D) (e : AE D) (g : GA D V), SuppAt e V g → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (e + cA D e)) Q = 0 → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V g).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  intro D ι V e g hS Q hQ i j
  have hent : ∀ i j, ((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
      = finPart D (Formalism.L2.Theta.mt V g i j) := fun i j => rfl
  have h1 := congrArg (fun x => ι (finPart D x) Q) (hS i j)
  simp only [map_mul] at h1
  have hm : (ι (finPart D (e + cA D e)) * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j))) Q
      = ι (finPart D (e + cA D e)) Q * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j)) Q := rfl
  rw [hm, hQ, zero_mul] at h1
  have h2 : ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q
      = ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := by
    have hs : (Formalism.L2.Theta.mt V g - 1) i j = Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := rfl
    rw [hs, map_sub, map_sub] at h1
    have hsub : (ι (finPart D (Formalism.L2.Theta.mt V g i j)) - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j))) Q
        = ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := rfl
    rw [hsub] at h1
    exact (sub_eq_zero.mp h1.symm)
  show ι (((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j) Q = _
  rw [hent, h2]
  by_cases hij : i = j
  · subst hij; simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne hij]
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (V : HSp D) (e : AE D) (g : GA D V), SuppAt e V g → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (e + cA D e)) Q = 0 → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V g).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  atlas_forward_decl GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero
end

section
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

namespace GlobalTheory

theorem idemSum_add_conj_support_finite : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q)) → ∀ (p : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite ∧ (∀ Q ∈ S, (p : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ∀ Q ∉ S, ι (finPart D (e + cA D e)) Q = 0 := by
  intro D ι hid hcj p e P he hp
  classical
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
      ∀ Q z, ev Q z = ι (finPart D z) Q :=
    ⟨fun Q => ((GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  simp only [← hev] at hid hcj ⊢
  obtain ⟨⟨es, hes, hsum⟩, horth⟩ := he
  have e2 : ∀ Q, Q ∉ P → ev Q e = 0 := fun Q hQ => by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 Q fun hh => hQ (hh ▸ h')
  refine ⟨↑P ∪ GlobalTheory.IdemSupport.cP '' ↑P, P.finite_toSet.union (P.finite_toSet.image _), ?_, ?_⟩
  · rintro Q (hQ | ⟨Q', hQ', rfl⟩)
    · exact hp Q hQ
    · rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact hp Q' hQ'
  · intro Q hQ
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_image, not_or, not_exists, not_and] at hQ
    have h1 : Q ∉ P := hQ.1
    have h2 : GlobalTheory.IdemSupport.cP Q ∉ P := fun h => hQ.2 _ h (GlobalTheory.ClassScalarValue.cP_cP Q)
    have a := hcj e (GlobalTheory.IdemSupport.cP Q)
    rw [e2 _ h2, map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at a
    rw [map_add, e2 Q h1, a, add_zero]

end GlobalTheory
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q)) → ∀ (p : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite ∧ (∀ Q ∈ S, (p : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ∀ Q ∉ S, ι (finPart D (e + cA D e)) Q = 0 := by
  atlas_forward_decl GlobalTheory.idemSum_add_conj_support_finite
end

section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StdAtPrime

theorem isIdemSum_idem (D : D7) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (hQ : GlobalTheory.ExportSeries.SplitSet Q) : IsIdemSum (idem Q) Q := by
  obtain ⟨e, he⟩ := hQ
  have : idem Q = e := by
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
    rw [hsum, GlobalTheory.ExportSeries.idem]
    exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.ExportSeries.idemAt_eq (hes PP hPP)
  rw [this]
  exact he

theorem bnd_inv_of_hLat_std (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (V : HSp D) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (p : ℕ) (k : Bridge.Gf V)
    (hk : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank) :
    Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom k.1)⁻¹.1 := by
  refine ⟨1, Nat.coprime_one_left p, fun i j Q => ?_⟩
  have hx : (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V k := by
    rw [hk]
    refine Submodule.mem_pi.2 fun i' _ => ?_
    by_cases h : i' = j
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have := (GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL k _).1 hx i Q
  have e : (fun j' => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
      ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) j')) = Pi.single j 1 := by
    funext j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [e, Matrix.mulVec_single_one] at this
  rw [Nat.cast_one, one_mul]
  exact this

set_option maxHeartbeats 1600000 in

theorem latAt_trivAt_of_split : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → StdBase B → ∀ (p bad : ℕ), p.Prime → p ∣ bad → ∀ (Q : Finset (Formalism.L2.DIV.Pl D.host.E)), GlobalTheory.ExportSeries.SplitSet Q → (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ hQ : GA D V, SuppAt (idem Q) V hQ → hQ ∈ GfC V ∧ ∀ (h h' : GA D V) (γ : GQ V) (k : Bridge.Gf V), SplitOffBad V bad h' → Formalism.UG.bc (Lev.swapAE D) k.1 ∈ Formalism.L2.DIV.St B.F.βS → finPt V (h * hQ) = Bridge.ratF V γ * finPt V h' * k → (⟨B.latAt (Bridge.ratF V γ⁻¹ * finPt V h * 1)⟩ : GenLat D.host.E V.rank).TrivAt p := by
  intro D V W B hB hS p bad hp hpb Q hQs hpQ hQ hsQ
  have hQsum := isIdemSum_idem D Q hQs
  have hinf : infPart D (idem Q) = 0 := by
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := hQsum
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun PP hPP => GlobalTheory.ExportSeries.SpecGood.infPart_eq_zero_of_isIdemAt D PP _ (hes PP hPP)
  refine ⟨GlobalTheory.WeilProduct.mem_GfC_of_supp (a := idem Q + cA D (idem Q)) ?_ hsQ, ?_⟩
  · rw [map_add, GlobalTheory.PlaceIdem.infPart_cA, hinf, map_zero, add_zero]
  intro h h' γ k hh' hk heq
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.T.placeIdempotent_components_conj_valuation D ι h1 h2 h4
  have hL0 : (B.F.ΛS : Set (Fin V.rank → D.host.E)) = L0c D V := hS.2.2.1
  have hstd : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    apply SetLike.coe_injective
    rw [GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, ← hL0, hS.2.2.2.2]
  rw [GlobalTheory.LatAtHLat.latAt_eq_hLat D V W B hL0]
  have hg : Bridge.ratF V γ⁻¹ * finPt V h * 1 = finPt V h' * k * (finPt V hQ)⁻¹ := by
    have e1 : finPt V (h * hQ) = finPt V h * finPt V hQ := map_mul _ _ _
    have e2 : finPt V h = Bridge.ratF V γ * finPt V h' * k * (finPt V hQ)⁻¹ :=
      eq_mul_inv_of_mul_eq (e1.symm.trans heq)
    have e3 : Bridge.ratF V γ⁻¹ = (Bridge.ratF V γ)⁻¹ := map_inv (Bridge.ratF V) γ
    have key : ∀ {G : Type} [Group G] (a b c d f : G), b = a * c * d * f⁻¹ → a⁻¹ * b * 1 = c * d * f⁻¹ := by
      intro G _ a b c d f hb
      rw [hb, mul_one, mul_assoc, mul_assoc, inv_mul_cancel_left, ← mul_assoc]
    exact (congrArg (fun x => x * finPt V h * 1) e3).trans (key _ _ _ _ _ e2)
  rw [hg]
  have hk1 : ∀ k : Bridge.Gf V, Formalism.UG.bc (Lev.swapAE D) k.1 ∈ Formalism.L2.DIV.St B.F.βS →
      Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    intro k hk
    have hr : Bridge.IsRatMat V 1 1 := by
      simp [Bridge.IsRatMat]
    have e4 : Bridge.ratF V 1 * 1 * k = k := by
      rw [map_one (Bridge.ratF V), one_mul, one_mul]
    have e5 : B.latAt k = B.latAt 1 := by
      ext x
      have := GlobalTheory.ExportSeries.Base.mem_latAt_iff hB.frame hr 1 k hk x
      rw [e4, inv_one, Units.val_one, Matrix.one_mulVec] at this
      exact this
    exact (GlobalTheory.LatAtHLat.latAt_eq_hLat D V W B hL0 k).symm.trans
      (e5.trans ((GlobalTheory.LatAtHLat.latAt_eq_hLat D V W B hL0 1).trans hstd))
  have hkS : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank := hk1 k hk
  have hkS' : Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    refine hk1 k⁻¹ ?_
    rw [Subgroup.coe_inv, map_inv]
    exact inv_mem hk
  set M := Matrix.GeneralLinearGroup.map (n := Fin V.rank) ι.toRingHom with hM
  have hsupp : ∀ (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (g : GA D V), IsIdemSum e P →
      (∀ PP ∈ P, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e V g →
      Bnd p (M (finPt V g).1).1 ∧ Bnd p (M (finPt V g).1)⁻¹.1 := by
    intro e P g he hp' hs
    obtain ⟨S, hSf, hSp, hS0⟩ := GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p D ι hid hcj p e P he hp'
    exact GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite p hp _ (M (finPt V g).1) S hSf hSp fun Q hQ i j => GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes D ι V e g hs Q (hS0 Q hQ) i j
  obtain ⟨-, e', P', he', hb', hs'⟩ := hh'
  have hp' : ∀ PP ∈ P', (p : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hpP
    obtain ⟨c, rfl⟩ := hpb
    exact hb' PP hPP (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpP)
  obtain ⟨b1, b1'⟩ := hsupp e' P' h' he' hp' hs'
  obtain ⟨b3, b3'⟩ := hsupp (idem Q) Q hQ hQsum hpQ hsQ
  have b2' : Bnd p (M k.1)⁻¹.1 := bnd_inv_of_hLat_std D ι h1 h2 V hstd p k hkS
  have b2 : Bnd p (M k.1).1 := by
    have := bnd_inv_of_hLat_std D ι h1 h2 V hstd p k⁻¹ hkS'
    rwa [Subgroup.coe_inv, map_inv, inv_inv] at this
  have eM : M (finPt V h' * k * (finPt V hQ)⁻¹).1 = M (finPt V h').1 * M k.1 * (M (finPt V hQ).1)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
  refine GlobalTheory.T.bounded_entries_integral D ι h1 h2 V hstd p _ ?_ ?_
  · rw [eM, Units.val_mul, Units.val_mul]
    exact bnd_mul p _ _ _ (bnd_mul p _ _ _ b1 b2) b3'
  · rw [eM, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
    exact bnd_mul p _ _ _ b3 (bnd_mul p _ _ _ b2' b1')

end GlobalTheory.StdAtPrime
end
