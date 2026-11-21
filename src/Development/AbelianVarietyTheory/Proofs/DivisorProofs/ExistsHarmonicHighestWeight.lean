import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockHarmonic_representative : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W), (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) → ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := by
  first | exact @GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | exact GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | (intros; apply GlobalTheory.FockAlg.HarmLift.exists_harm2_rep <;> assumption)
end

section
section
noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.FockAlg.HarmStable MvPolynomial

namespace GlobalTheory.FockAlg.FinHarm

variable {σ : Type}

def lowDeg (σ : Type) (N : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨆ d : Fin (N + 1), homog σ d

instance [Finite σ] (N : ℕ) : FiniteDimensional ℂ (lowDeg σ N) := by
  haveI : ∀ d : ℕ, FiniteDimensional ℂ (homog σ d) := fun d =>
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  unfold lowDeg
  infer_instance

theorem mem_lowDeg_self (P : MvPolynomial σ ℂ) : P ∈ lowDeg σ P.totalDegree := by
  obtain ⟨N, hN⟩ : ∃ N, N = P.totalDegree := ⟨_, rfl⟩
  rw [← hN]
  have hs := sum_homogeneousComponent P
  rw [← hN] at hs
  rw [← hs]
  refine Submodule.sum_mem _ fun e he => ?_
  have he' : e < N + 1 := Finset.mem_range.1 he
  exact Submodule.mem_iSup_of_mem (⟨e, he'⟩ : Fin (N + 1))
    (homogeneousComponent_mem e P)

theorem DegZero.map_lowDeg {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K) (N : ℕ)
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowDeg σ N) : K P ∈ lowDeg σ N := by
  have hle : lowDeg σ N ≤ (lowDeg σ N).comap K :=
    iSup_le fun d x hx => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem d (hK d x hx))
  exact hle hP

end GlobalTheory.FockAlg.FinHarm

namespace GlobalTheory.FockAlg

open FinHarm

theorem fin_harm : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧
      (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧
      KStable (fockAct2 P Q R S) H0 := by
  intro P Q R S h hh
  have hh' : h ∈ sub2 P Q R S := by
    rw [← SetLike.mem_coe, coe_fockHarmonicsSecondMemberSubmodule]; exact hh
  refine ⟨sub2 P Q R S ⊓ lowDeg _ h.totalDegree, ?_, ⟨hh', mem_lowDeg_self h⟩, ?_, ?_, ?_⟩
  · exact Submodule.finiteDimensional_of_le inf_le_right
  · intro v hv
    rw [← coe_fockHarmonicsSecondMemberSubmodule]; exact hv.1
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.1 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct1 hY) _ hw.2⟩
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.2 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct2 hY) _ hw.2⟩

end GlobalTheory.FockAlg
end
end

open Formalism.BasicNotions.TH GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonic_mem_finiteDimensional_compactStable : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S → ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := by
  atlas_forward_decl GlobalTheory.FockAlg.fin_harm
end

section
section
namespace GlobalTheory

theorem stable_complement_of_kernel_exists
    (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
    (hι : Function.Injective ι) (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V)
    (hfin : FiniteDimensional ℂ H0) (A : Set (Module.End ℂ V))
    (h1 : ∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0)
    (h2 : ∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0)
    (h3 : ∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) :
    ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧
      ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  intro h hh
  set K : Submodule ℂ V := H0 ⊓ LinearMap.ker pr with hK
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  set K' : Submodule ℂ H := K.map ι with hK'
  haveI : FiniteDimensional ℂ K' := inferInstance
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, e, he, hsum⟩ := K'.exists_add_mem_mem_orthogonal (ι h)
  obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
  have hkH0 : k ∈ H0 := hk.1
  have hkker : pr k = 0 := hk.2
  refine ⟨h - k, H0.sub_mem hh hkH0, by simp [hkker], ?_⟩
  have horth : ∀ k' ∈ K, inner ℂ (ι k') (ι (h - k)) = 0 := by
    intro k' hk'
    have : ι (h - k) = e := by rw [map_sub, hsum]; abel
    rw [this]
    exact (Submodule.mem_orthogonal K' e).mp he _ (Submodule.mem_map_of_mem hk')
  intro a ha z hz
  set c := h - k with hc
  have hcH0 : c ∈ H0 := H0.sub_mem hh hkH0
  set d := a c - z • c with hd
  have hdK : d ∈ K := by
    refine ⟨H0.sub_mem (h1 a ha c hcH0) (H0.smul_mem z hcH0), ?_⟩
    show pr d = 0
    simp [hd, hz]
  obtain ⟨b, hb, hab⟩ := h3 a ha
  have hdorth : ∀ k' ∈ K, inner ℂ (ι k') (ι d) = 0 := by
    intro k' hk'
    have hbk : b k' ∈ K := ⟨h1 b hb k' hk'.1, h2 b hb k' hk'.1 hk'.2⟩
    have e1 : inner ℂ (ι k') (ι (a c)) = 0 := by
      rw [← inner_conj_symm, hab, inner_conj_symm]
      exact horth _ hbk
    rw [hd, map_sub, inner_sub_right, e1, map_smul, inner_smul_right, horth k' hk']
    simp
  have : ι d = 0 := inner_self_eq_zero.mp (hdorth d hdK)
  have hd0 : d = 0 := hι (by rw [this, map_zero])
  exact sub_eq_zero.mp hd0

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 → ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) → (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) → (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) → ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  atlas_forward_decl GlobalTheory.stable_complement_of_kernel_exists
end

section
noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.HarmLift

theorem lemA : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W),
    (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) →
    ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := GlobalTheory.T.exists_fockHarmonic_representative

theorem lemB : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧
      KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := GlobalTheory.T.fockHarmonic_mem_finiteDimensional_compactStable

theorem lemC : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 →
    ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) →
      (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) →
      (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) →
      ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel

theorem isKC_adjZ {p q : ℕ} {Z : Mat p q} (hZ : IsKC Z) : IsKC (adjZ Z) := by
  intro a b hab
  rw [GlobalTheory.FockAdj.adjZ_apply, hZ b a (fun h => hab (by revert h; rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock])),
    star_zero, mul_zero]

theorem trace_PC {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem trace_Eab {p q : ℕ} (a b : Ix p q) : (Eab a b).trace = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; rw [if_pos rfl, Eab, Matrix.trace_single_eq_same]
  · rw [if_neg h, Eab, Matrix.trace_single_eq_of_ne _ _ _ h]

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  simp only [Eab, Matrix.single_apply]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := e; exact absurd h hcd
  · rfl

theorem harm_lift : ∀ (P Q R S : ℕ) (x t : ℚ) (M : GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V),
    GlobalTheory.RealLift.IsLift x t M pr → ∀ (μ : Formalism.BasicNotions.TH.Ix R S → ℚ) (w : M.V),
    Formalism.BasicNotions.TH.IsHW M.act μ w → ∃ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec x (fun c => μ c - t) f := by
  intro P Q R S x t M pr ⟨hsurj, h1, h2⟩ μ w hw
  obtain ⟨g, rfl⟩ := hsurj w
  have hPC : ∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0 := by
    intro Z hZ f; rw [h1, trace_PC hZ, mul_zero, zero_smul]
  have h2' : ∀ Y f, pr (fockAct2 P Q R S Y f) = M.act Y (pr f) - ((t : ℂ) * Y.trace) • pr f := by
    intro Y f; rw [h2]; abel
  obtain ⟨h, hh, hpr⟩ := lemA P Q R S M.V pr hPC g
  obtain ⟨H0, hfin, hH0, hharm, hs1, hs2⟩ := lemB P Q R S h hh
  obtain ⟨ι, hιIP, hιinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)
  let A : Set (Module.End ℂ (Pol P Q R S)) :=
    {a | (∃ X, IsKC X ∧ a = fockAct1 P Q R S X) ∨ ∃ Y, IsKC Y ∧ a = fockAct2 P Q R S Y}
  have hadj := GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hιIP
  obtain ⟨c, hc, hcpr, hceig⟩ := lemC (Pol P Q R S) M.V _ ι hιinj pr H0 hfin A
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) v hv
      exacts [hs1 X hX v hv, hs2 Y hY v hv])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) v _ hv
      · rw [h1, hv, smul_zero]
      · rw [h2', hv, map_zero, smul_zero, sub_zero])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨_, Or.inl ⟨_, isKC_adjZ hX, rfl⟩, hadj.2.1 X⟩
      · exact ⟨_, Or.inr ⟨_, isKC_adjZ hY, rfl⟩, hadj.2.2 Y⟩)
    h hH0
  rw [hpr] at hcpr
  refine ⟨c, hharm c hc, fun X hX => hceig _ (Or.inl ⟨X, hX, rfl⟩) _ (by rw [h1]), ?_, ?_⟩
  · rintro rfl
    exact hw.1 (by rw [← hcpr, map_zero])
  · have hw2 := hw.2
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hw2 ⊢
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have hs : sameBlock a a := by rcases a with a | a <;> simp [sameBlock]
      rw [hceig _ (Or.inr ⟨_, isKC_Eab hs, rfl⟩) ((((μ a - t : ℚ)) : ℂ))]
      rw [h2', hcpr, hw2.1 a, trace_Eab, if_pos rfl, mul_one, ← sub_smul]
      push_cast; ring_nf
    · have hs : sameBlock a b := by
        revert hab; rcases a with a | a <;> rcases b with b | b <;> simp [posC, sameBlock]
      have hne : a ≠ b := by
        rintro rfl; revert hab; rcases a with a | a <;> simp [posC]
      rw [hceig _ (Or.inr ⟨_, isKC_Eab hs, rfl⟩) 0, zero_smul]
      rw [h2', hcpr, hw2.2 a b hab, trace_Eab, if_neg hne, mul_zero, zero_smul, sub_zero]

end GlobalTheory.HarmLift
end
end
