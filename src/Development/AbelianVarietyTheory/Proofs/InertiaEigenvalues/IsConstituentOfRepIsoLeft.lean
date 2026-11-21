import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoBlockEqZeroIff
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdemOrthogonal
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelOfParabolicVector

section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  first | exact @GlobalTheory.SerOSys.zIdem_centralIdempotent | exact GlobalTheory.SerOSys.zIdem_centralIdempotent | (intros; apply GlobalTheory.SerOSys.zIdem_centralIdempotent <;> assumption)
end

section
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem nontrivial_of_simpleRep {Γ : Type} [Group Γ] [Fintype Γ] (V : FDRep ℂ Γ) (h : Simple V) :
    Nontrivial V := by
  rw [FDRep.simple_iff_char_is_norm_one] at h
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h0 : ∀ g, V.character g = 0 := fun g => by
    rw [FDRep.character, Subsingleton.elim (V.ρ g) 0, map_zero]
  simp only [h0, mul_zero, Finset.sum_const_zero] at h
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne' : (Nat.card Γ : ℂ) ≠ 0) h.symm

theorem invariant_eq_bot_or_top_of_simple {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ)
    [Simple τ] (U : Submodule ℂ τ) (hU : ∀ g, ∀ x ∈ U, τ.ρ g x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let A : Subrepresentation τ.ρ := ⟨U, fun g v hv => hU g v hv⟩
  let X : FDRep ℂ Γ := FDRep.of A.toRepresentation
  let i : X ⟶ τ := ⟨InducedCategory.homMk (ModuleCat.ofHom U.subtype), fun g => by
    ext1; ext x; rfl⟩
  have hinj : Function.Injective ⇑(ConcreteCategory.hom i) := by
    intro x y h; exact Subtype.ext h
  have : Mono i := ConcreteCategory.mono_of_injective i hinj
  by_cases h0 : i = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := congrArg (fun f : X ⟶ τ => ConcreteCategory.hom f ⟨x, hx⟩) h0
    have h1 : ConcreteCategory.hom i ⟨x, hx⟩ = x := rfl
    have h2 : ConcreteCategory.hom (0 : X ⟶ τ) ⟨x, hx⟩ = 0 := rfl
    simp only [h1, h2] at this
    exact this
  · right
    have : IsIso i := (Simple.mono_isIso_iff_nonzero i).2 h0
    apply Submodule.eq_top_of_finrank_eq
    exact (FDRep.isoToLinearEquiv (asIso i)).finrank_eq

theorem zIdem_eq_of_linearEquiv {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ)
    (φ : τ ≃ₗ[ℂ] τ') (hφ : ∀ g x, φ (τ.ρ g x) = τ'.ρ g (φ x)) : zIdem τ = zIdem τ' := by
  apply MonoidAlgebra.ext
  ext γ
  rw [zIdem_coeff, zIdem_coeff, φ.finrank_eq]
  have h : τ'.ρ γ⁻¹ = φ.conj (τ.ρ γ⁻¹) := by
    ext x
    rw [LinearEquiv.conj_apply]
    simp [hφ]
  rw [h, LinearMap.trace_conj']

theorem zIdem_eq_centralIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem τ.ρ := by
  unfold zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rfl

theorem zIdem_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ),
    Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  intro Γ _ _ τ τ' hτ hτ' hne
  haveI := nontrivial_of_simpleRep τ hτ
  haveI := nontrivial_of_simpleRep τ' hτ'
  rw [zIdem_eq_centralIdem, zIdem_eq_centralIdem]
  exact Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_orthogonal Γ τ τ' τ.ρ τ'.ρ
    (invariant_eq_bot_or_top_of_simple τ) (invariant_eq_bot_or_top_of_simple τ')
    (by rintro ⟨φ, hφ⟩; exact hne (zIdem_eq_of_linearEquiv τ τ' φ hφ))

end GlobalTheory.SerOSys
end
end

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  atlas_forward_decl GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne
end

section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ = zIdem τ' → RepIso τ.ρ τ'.ρ := by
  first | exact @GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | exact GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | (intros; apply GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple <;> assumption)
end

section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralIdempotents_simpleFDRep_finite_finsum_eq_one : ∀ (Γ : Type) [Group Γ] [Fintype Γ], {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧ ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := by
  first | exact @GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one | exact GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one | (intros; apply GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one <;> assumption)
end

section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys.TwoMap

open GlobalTheory.GLp.ParLabel

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

abbrev T₀ : GL {i : Fin (a + b) // twoBlock (a + b) a i = 0} (ZMod g) ≃* GlobalTheory.GLq.Gn g a :=
  (glEquiv (ZMod g) (firstBlock a b).symm).symm

abbrev T₁ : GL {i : Fin (a + b) // twoBlock (a + b) a i = 1} (ZMod g) ≃* GlobalTheory.GLq.Gn g b :=
  (glEquiv (ZMod g) (secondBlock a b).symm).symm

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end GlobalTheory.SerOSys.TwoMap

namespace GlobalTheory.SerOSys.TwoMap

open GlobalTheory.GLp.ParLabel

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}
  (τ₀ : FDRep ℂ (GL (Fin a) (ZMod g))) (τ₁ : FDRep ℂ (GL (Fin b) (ZMod g)))

def fnl (l₀ : (τ₀ : Type) →ₗ[ℂ] ℂ) (l₁ : (τ₁ : Type) →ₗ[ℂ] ℂ) :
    ∀ c : Fin 2, (twoRep τ₀ τ₁ c : Type) →ₗ[ℂ] ℂ
  | 0 => l₀
  | 1 => l₁

def pair (x₀ : (τ₀ : Type)) (x₁ : (τ₁ : Type)) : ∀ c : Fin 2, (twoRep τ₀ τ₁ c : Type)
  | 0 => x₀
  | 1 => x₁

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GlobalTheory.GLq.Gn g (a + b)) V) (w : V)

def phi (l₀ : (τ₀ : Type) →ₗ[ℂ] ℂ) (l₁ : (τ₁ : Type) →ₗ[ℂ] ℂ) :
    PiTensorProduct ℂ (fun c => (twoRep τ₀ τ₁ c : Type)) →ₗ[ℂ] V :=
  PiTensorProduct.lift (∑ g₀ : GlobalTheory.GLq.Gn g a, ∑ g₁ : GlobalTheory.GLq.Gn g b,
    ((MultilinearMap.mkPiAlgebra ℂ (Fin 2) ℂ).compLinearMap
      (fnl τ₀ τ₁ (l₀ ∘ₗ τ₀.ρ g₀⁻¹) (l₁ ∘ₗ τ₁.ρ g₁⁻¹))).smulRight (ρ (GlobalTheory.GLp.blk a b (a + b) g₀ g₁) w))

end GlobalTheory.SerOSys.TwoMap

namespace GlobalTheory.SerOSys.TwoMap

open GlobalTheory.GLp.ParLabel

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}
  (τ₀ : FDRep ℂ (GL (Fin a) (ZMod g))) (τ₁ : FDRep ℂ (GL (Fin b) (ZMod g)))
  {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GlobalTheory.GLq.Gn g (a + b)) V) (w : V)

end GlobalTheory.SerOSys.TwoMap

namespace GlobalTheory.SerOSys.TwoMap

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

variable (τ₀ : FDRep ℂ (GL (Fin a) (ZMod g))) (τ₁ : FDRep ℂ (GL (Fin b) (ZMod g)))
  {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GlobalTheory.GLq.Gn g (a + b)) V) (w : V)

end GlobalTheory.SerOSys.TwoMap
end
end

section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem zIdem_idem_central {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (h : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent τ h

theorem zIdem_mul_eq_zero {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (hne : zIdem τ ≠ zIdem τ') : zIdem τ * zIdem τ' = 0 := GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne τ τ' h h' hne

theorem repIso_of_zIdem_eq {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (he : zIdem τ = zIdem τ') : RepIso τ.ρ τ'.ρ := GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq τ τ' h h' he

theorem zIdem_finite_sum (Γ : Type) [Group Γ] [Fintype Γ] :
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧
      ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := GlobalTheory.T.centralIdempotents_simpleFDRep_finite_finsum_eq_one Γ

section Main

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C)

def Zall (g n : ℕ) [Fact g.Prime] : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z}

def Zl (n : ℕ) (f : (ZMod g)[X]) : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f}

theorem Zl_sub (n : ℕ) (f : (ZMod g)[X]) : Zl O n f ⊆ Zall g n := fun _ ⟨τ, h1, h2, _⟩ => ⟨τ, h1, h2⟩

theorem Zall_finite (n : ℕ) : (Zall g n).Finite := (zIdem_finite_sum (GL (Fin n) (ZMod g))).1

theorem Zl_finite (n : ℕ) (f : (ZMod g)[X]) : (Zl O n f).Finite := (Zall_finite n).subset (Zl_sub O n f)

theorem eSerO_eq_sum (n : ℕ) (f : (ZMod g)[X]) : eSerO O n f = ∑ z ∈ (Zl_finite O n f).toFinset, z := by
  rw [← finsum_mem_eq_finite_toFinset_sum (fun z => z) (Zl_finite O n f)]
  rfl

theorem mul_of_mem {n : ℕ} {z z' : MonoidAlgebra ℂ (GL (Fin n) (ZMod g))} (hz : z ∈ Zall g n)
    (hz' : z' ∈ Zall g n) : z * z' = if z = z' then z' else 0 := by
  obtain ⟨τ, hτ, rfl⟩ := hz
  obtain ⟨τ', hτ', rfl⟩ := hz'
  split_ifs with h
  · rw [← h]; exact (zIdem_idem_central τ hτ).1
  · exact zIdem_mul_eq_zero τ τ' hτ hτ' h

theorem isConstituent_of_repIso_left {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {τ τ' : FDRep ℂ Γ}
    {ρ : Representation ℂ Γ V} (h : IsConstituent τ ρ) (e : RepIso τ'.ρ τ.ρ) : IsConstituent τ' ρ := by
  obtain ⟨φ, hφ, hne⟩ := h
  obtain ⟨e, he⟩ := e
  have hφ' : ∀ γ, φ ∘ₗ τ.ρ γ = ρ γ ∘ₗ φ := hφ
  refine ⟨φ ∘ₗ (e : (τ' : Type) →ₗ[ℂ] (τ : Type)), fun γ => LinearMap.ext fun x => ?_, fun h0 => hne ?_⟩
  · show φ (e (τ'.ρ γ x)) = ρ γ (φ (e x))
    rw [he]
    exact LinearMap.congr_fun (hφ' γ) (e x)
  · refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun h0 (e.symm x)
    simpa using this

theorem hasLabelO_of_repIso {n : ℕ} {τ τ' : FDRep ℂ (GL (Fin n) (ZMod g))} {f : (ZMod g)[X]}
    (h : HasLabelO O τ f) (e : RepIso τ'.ρ τ.ρ) : HasLabelO O τ' f := by
  obtain ⟨s, b, lam, hb, hl, hc, hf⟩ := h
  exact ⟨s, b, lam, hb, hl, isConstituent_of_repIso_left hc e, hf⟩

end Main

end GlobalTheory.SerOSys
end
end
