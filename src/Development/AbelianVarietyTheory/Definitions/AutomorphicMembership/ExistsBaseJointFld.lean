import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRichSmall
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBaseOfRich
import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField

noncomputable section

namespace GlobalTheory.Mem.Top.Inh

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem exists_psi (P : Pre) (l : ℕ) (hl : l.Prime) (A : Finset ℕ) :
    ∃ (Q : Finset (HeightOneSpectrum (𝓞 P.host.E))) (k : ℕ) (ψ : HChar P.host.E), IsPsi (H := P.host) l Q ψ ∧ ψ.OrderDvd (l ^ k) ∧
      Chr.IsTwist P.host (offSet P) ψ ∧ (∀ v ∈ Q, ((l : ℕ) : 𝓞 P.host.E) ∉ v.asIdeal) ∧ (∀ v ∈ Q, Ideal.absNorm v.asIdeal ∉ A) ∧
      ψ ≠ 1 := by
  classical
  obtain ⟨Q, ψ, hQ, hψ, hs, hT⟩ := GlobalTheory.Mem.PsiExist.psi_exists P.R P.host l hl
    ((insert l ((finite_offSet P).toFinset ∪ A)).erase 0) (Finset.notMem_erase _ _)
  obtain ⟨a, ha⟩ := hψ.ord
  have key : ∀ v ∈ Q, (Ideal.absNorm v.asIdeal).Prime ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 P.host.E) ∉ v.asIdeal ^ 2 ∧
      Ideal.absNorm v.asIdeal ∉ (finite_offSet P).toFinset ∪ A := fun v hv => by
    obtain ⟨p, hp, hpv⟩ := Examples₂.PlacesToy.exists_prime_mem v
    obtain ⟨h1, h2⟩ := hs v hv p hp hpv v hpv
    exact ⟨h1 ▸ hp, h1 ▸ h2, h1 ▸ fun hm => hT v hv p (Finset.mem_erase.2 ⟨hp.ne_zero, Finset.mem_insert_of_mem hm⟩) hpv⟩
  refine ⟨Q, a, ψ, hψ, ha, ⟨⟨_, pow_pos hl.pos a, ha⟩, hψ.triv, hψ.tame, fun v hv => ?_⟩,
    fun v hv => hT v hv l (Finset.mem_erase.2 ⟨hl.ne_zero, Finset.mem_insert_self _ _⟩),
    fun v hv h => (key v hv).2.2 (Finset.mem_union_right _ h), fun h => ?_⟩
  · have hv' : v ∈ Q := by_contra fun h => hv ((hψ.ram v).2 h)
    exact ⟨hψ.split v hv', (key v hv').1, (key v hv').2.1,
      fun hm => (key v hv').2.2 (Finset.mem_union_left _ ((finite_offSet _).mem_toFinset.2 hm))⟩
  · obtain ⟨v, hv⟩ := hQ
    exact ((hψ.ram v).1 (h ▸ isClsF_one.unr v)) hv

theorem exists_family (P : Pre) (f : Fr P) (pl : Finset ℕ) (A : ℕ → Finset ℕ) : ∃ Ξ : Set (HChar P.host.E),
    ∀ (B : Base) (h : B.toPre = P), ∃ T : TwDat B, T.pl = pl ∧ T.Avoids A ∧ (∀ w, B.places.resChar w ∈ pl → T.psi w ≠ 1) ∧
      T.set (h ▸ f) = h ▸ Ξ := by
  classical
  have H : ∀ l : ℕ, ∃ (Q : Finset (HeightOneSpectrum (𝓞 P.host.E))) (k : ℕ) (ψ : HChar P.host.E), l.Prime →
      IsPsi (H := P.host) l Q ψ ∧ ψ.OrderDvd (l ^ k) ∧ Chr.IsTwist P.host (offSet P) ψ ∧
      (∀ v ∈ Q, ((l : ℕ) : 𝓞 P.host.E) ∉ v.asIdeal) ∧ (∀ v ∈ Q, Ideal.absNorm v.asIdeal ∉ A l) ∧
      (l ∈ pl → ψ ≠ 1) ∧ (l ∉ pl → ψ = 1 ∧ k = 0) := fun l => by
    by_cases h : l.Prime ∧ l ∈ pl
    · obtain ⟨Q, k, ψ, h1, h2, h3, h4, h5, h6⟩ := exists_psi P l h.1 (A l)
      exact ⟨Q, k, ψ, fun _ => ⟨h1, h2, h3, h4, h5, fun _ => h6, fun hn => absurd h.2 hn⟩⟩
    · exact ⟨∅, 0, 1, fun hl => ⟨isPsi_one _, one_pow _, Chr.isTwist_one _ _, by simp, by simp,
        fun hm => absurd ⟨hl, hm⟩ h, fun _ => ⟨rfl, rfl⟩⟩⟩
  choose Q k ψ H using H
  refine ⟨{1, f.del, f.del'} ∪ {x | ∃ l : ℕ, l.Prime ∧ x = (if l = P.host.pde then f.del' else f.del) * ψ l}, ?_⟩
  rintro B rfl
  have G := fun w => H _ (B.places.resChar_prime w)
  refine ⟨{ pl := pl, Q := fun w => Q (B.places.resChar w), k := fun w => k (B.places.resChar w),
            psi := fun w => ψ (B.places.resChar w), psi_is := fun w => (G w).1, psi_ord := fun w => (G w).2.1,
            psi_tw := fun w => (G w).2.2.1, Q_l := fun w => (G w).2.2.2.1, off := fun w => (G w).2.2.2.2.2.2,
            conj := fun w => by simp only [TwFin.resChar_conj, and_self] },
    rfl, fun w => (G w).2.2.2.2.1, fun w => (G w).2.2.2.2.2.1, ?_⟩
  unfold TwDat.set
  congr 1
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, B.places.resChar_prime w, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨w, hw⟩ := GlobalTheory.Mem.PsiExist.exists_place_over B.LL hl
    have e : B.places.resChar w = l :=
      Examples₂.PlacesToy.prime_mem_unique w (Examples₂.PlacesToy.resCharW_prime _) hl (Examples₂.PlacesToy.resCharW_mem w) hw
    exact ⟨w, by subst e; rfl⟩

theorem exists_fixed (B : Base) (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ B' : Base, B'.toPre = B.toPre ∧ B'.KsC = B.KsC ∧ ∀ z ∈ S, z ∈ B'.fixedCoefficientFieldInComplex := by
  obtain ⟨B', h, h'⟩ := BaseEnl.exists_enl B S hS
  refine ⟨{ B' with LL0 := ⊤, coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm, Ks_le := le_top,
                    rootOfUnity_eightQ_mem_coeffGaloisSubfield := B'.rootOfUnity_eightQ_mem_coeffGaloisSubfield.imp fun _ hz => ⟨trivial, hz.2⟩ }, h.1, h.KsC_eq, fun z hz => ?_⟩
  obtain ⟨x, hx⟩ := h' z hz
  exact ⟨x, trivial, hx⟩

theorem exists_over (K : Ctx) : ∃ P, K.Over P := by
  obtain ⟨sp, hT, hY, hA, hV, hz, h, -⟩ := exists_diagSpaces_ofCh K.P K.Lv
  exact ⟨_, sp, hT, hY, hA, hV, hz, rfl, h.1⟩

def colsTw (B : Base) (f : Fr B.toPre) (T : TwDat B) : Cols B :=
  { ColsModel.cols B with
    Tup := T.set f
    mu0 := ⟨1, .inl (.inl rfl)⟩
    muStar := ⟨f.del, .inl (.inr (.inl rfl))⟩
    muStar' := ⟨f.del', .inl (.inr (.inr rfl))⟩
    chTw := fun u _ => ColsModel.ch B.toPre u
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun u _ => (ColsModel.member B.toPre u).P }


end GlobalTheory.Mem.Top.Inh

end
