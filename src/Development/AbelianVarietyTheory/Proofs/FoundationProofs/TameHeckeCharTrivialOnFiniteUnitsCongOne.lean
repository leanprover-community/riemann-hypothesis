import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdelesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIdele_exists_local_approx' : ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N → ∀ x : (FiniteAdeleRing (𝓞 L) L)ˣ, ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (k : HeightOneSpectrum (𝓞 L) → Lˣ), (∀ P ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ P.valuation L (N : L) * P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k P : L)) ∧ ∀ P, P ∉ S → Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = 1 ∧ (N : 𝓞 L) ∉ P.asIdeal := by
  first | exact @GlobalTheory.finiteIdele_exists_local_approx | exact GlobalTheory.finiteIdele_exists_local_approx | (intros; apply GlobalTheory.finiteIdele_exists_local_approx <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChangeFiniteAdele_ringEquiv : ∀ D : D7, ∃ ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E, (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) ∧ (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) ∧ (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) := by
  first | exact @GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv | exact GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv | (intros; apply GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_eq_prod_localComponents_approximating : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∃ N : ℕ, 0 < N ∧ ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ), (∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧ Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤ P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E)) → (∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal) → ((c x : Circle) : ℂ) = ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.CharLocProd.char_eq_prod_locK | exact GlobalTheory.CharLocProd.char_eq_prod_locK | (intros; apply GlobalTheory.CharLocProd.char_eq_prod_locK <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem valued_natCast_le_of_mem_asIdeal {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (hm : (m : 𝓞 L) ∈ P.asIdeal) : Valued.v ((m : P.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
  have h1 : ((m : P.adicCompletion L)) = ((algebraMap (𝓞 L) L (m : 𝓞 L) : L) : P.adicCompletion L) := by
    rw [map_natCast]
    exact (map_natCast (algebraMap L (P.adicCompletion L)) m).symm
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have := (P.intValuation_le_pow_iff_mem (m : 𝓞 L) 1).2 (by simpa using hm)
  simpa using this

theorem finiteAdele_apply_sub_one_of_eq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (a b : FiniteAdeleRing (𝓞 L) L) (e : a - 1 = (m : FiniteAdeleRing (𝓞 L) L) * b) :
    a P - 1 = (m : P.adicCompletion L) * b P := by
  let ev : FiniteAdeleRing (𝓞 L) L →+* P.adicCompletion L :=
    RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) P
  have e3 : ev (a - 1) = ev ((m : FiniteAdeleRing (𝓞 L) L) * b) := congrArg ev e
  rw [ev.map_sub, ev.map_mul, ev.map_one, map_natCast ev m] at e3
  exact e3

theorem tame_heckeChar_eq_one_of_finUnit : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → (∀ P, χ.TameAt P) → ∀ m : ℕ, (∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → χ.UnrAt P) → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = m • y) → c x = 1 := by
  intro D c χ hc ht m hu x hx ⟨y, hy, hxy⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.T.exists_baseChangeFiniteAdele_ringEquiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.T.heckeChar_eq_prod_localComponents_approximating D ι h1 h2 (GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.T.finiteIdele_exists_local_approx' D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : IsUnitAt P (atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.loc P (atFin P (k P)) = 1 := by
    by_cases hm : (m : 𝓞 D.host.E) ∈ P.asIdeal
    · refine ht P _ hun ?_
      have e : ι (finPart D (x : AE D)) - 1 = (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * ι y := by
        rw [← map_one ι, ← map_sub, hxy, map_nsmul, nsmul_eq_mul]
      have e2 : ι (finPart D (x : AE D)) P - 1 = (m : P.adicCompletion D.host.E) * ι y P :=
        finiteAdele_apply_sub_one_of_eq P m _ _ e
      have c1 : Valued.v (ι (finPart D (x : AE D)) P - 1) ≤ WithZero.exp (-1 : ℤ) := by
        rw [e2, map_mul]
        calc _ ≤ WithZero.exp (-1 : ℤ) * 1 :=
              mul_le_mul' (valued_natCast_le_of_mem_asIdeal P m hm) ((h2 _).1 hy P)
          _ = _ := mul_one _
      have e4 : ((atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          (ι (finPart D (x : AE D)) P - 1) - (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4]
      exact Valuation.map_sub_le _ c1 b'
    · exact hu P hm _ hun
  show ((χ.loc P (atFin P (k P)) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory
end
