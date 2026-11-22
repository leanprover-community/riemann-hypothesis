module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TaylorLogMetric

open NumberField Formalism.BasicNotions Classical
open scoped Pointwise

def vec22 (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' →
    e N N' L L' ∈ Th D T L L' ∧ e N N' L L' ≠ 0 ∧
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M

def th22 (D : D7) (T : Tor D) (C : ℝ) (e : FamE D) : Prop :=
  (∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    normSq D T (La D T L₁ L₁') (e N N' L₁ L₁') = normSq D T (La D T L₂ L₂') (e N N' L₂ L₂')) ∧
  (∀ Lsc : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ Lsc →
    ∀ N N' L L', admitted D N N' L L' →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M → CoefIn D (e N N' L L') M →
        meanLogNormSq D T L L' M (e N N' L L') ≤ C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc) ∧
  (∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M →
      CoefIn D (e N N' L₁ L₁') M → CoefIn D (e N N' L₂ L₂') M → ∀ ρ : M →ₐ[ℚ] ℂ,
        normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₁ L₁') (fnConj D M ρ (e N N' L₁ L₁')) =
          normSq D (torConj D T M ρ) (La D (torConj D T M ρ) L₂ L₂') (fnConj D M ρ (e N N' L₂ L₂'))) ∧
  (∀ N N' L L', admitted D N N' L L' → ∀ x : VC D N N',
    normSq D T (La D T L L') (U D T x (e N N' L L')) = normSq D T (La D T L L') (e N N' L L'))

def eq22 (D : D7) (T : Tor D) (χ : IdE D → ℂ) (e : FamE D) : Prop :=
  letI := D.host.cmStar
  (∀ N N' (L : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
      pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
          (e N N' L.1 L'.1) =
        e N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1)
          (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'.1)) ∧
  (∀ N N' (L : SDLat D.host.E N) (L' L'' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L.1 L''.1 = fun z => (χ (detId D L'.1 L''.1)) ^ (-((N / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L.1 L''.1) (e N N' L.1 L'.1) z) ∧
  (∀ N N' (L L₁ : SDLat D.host.E N) (L' : SDLat D.host.E N'), Even N → Even N' →
    e N N' L₁.1 L'.1 = fun z => (χ (detId D L.1 L₁.1)) ^ (((N' / 2 : ℕ) : ℤ)) *
      Iop D T (La D T L.1 L'.1) (La D T L₁.1 L'.1) (e N N' L.1 L'.1) z)

def chiQ (D : D7) : D.Dt ⧸ D.UO →* ℂˣ :=
  QuotientGroup.lift D.UO D.chiD (fun x hx => MonoidHom.mem_ker.mpr (D.chiD_UO x hx))

def RelDetPinned (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) : Prop :=
  letI := D.host.cmStar
  Function.Injective idl ∧ (∀ 𝔞, N1 D 𝔞 ↔ ∃ x, idl x = 𝔞) ∧ (∀ x y, idl (x * y) = idl x * idl y) ∧
  (∀ z : unitary D.host.E, idl (QuotientGroup.mk (D.e1Dt z)) =
    Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) ∧
  ∀ N (L L' : SDLat D.host.E N), idl (D.relDet N L L') = detId D L.1 L'.1

def chiRec (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) : IdE D → ℂ :=
  fun 𝔞 => if h : ∃ x, idl x = 𝔞 then ((chiQ D h.choose : ℂˣ) : ℂ) else 0

theorem chiRec_idl (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : Function.Injective idl) (x : D.Dt ⧸ D.UO) :
    chiRec D idl (idl x) = ((chiQ D x : ℂˣ) : ℂ) := by
  have hx : ∃ y, idl y = idl x := ⟨x, rfl⟩
  unfold chiRec
  rw [dite_eq_left hx, h hx.choose_spec]

def DualB (D : D7) {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  ∀ τ, ((P (tauSg D τ)).map D.host.conj).transpose * P τ = 1

def adm1 (D : D7) : Prop :=
  (∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.ramificationIdxIn (𝓞 D.host.E) = 1) ∧
  (∀ x : D.host.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm D.host.K x = 1) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.condN →
    ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (Ideal.span {(p : ℤ)}) →
      (Ideal.primesOver 𝔭 (𝓞 D.host.E)).ncard = 2) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.QS * D.host.q →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2) ∧
  (∀ 𝔭 : Ideal (𝓞 D.host.K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 1 < 𝔭.ramificationIdxIn (𝓞 D.host.E) →
    ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.K) ∈ 𝔭) ∧
  (∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (D.host.d : 𝓞 D.host.E) ∈ P →
    ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      ((∀ x : 𝓞 D.host.E, ∃ y ∈ P, (y : D.host.E) = σ (x : D.host.E) - (x : D.host.E)) ↔
        (D.host.galE σ = 1 ∨
          D.host.galE σ = ((1, -1), 1))))

theorem isChi_chiRec (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : RelDetPinned D idl) :
    IsChi D (chiRec D idl) := by
  obtain ⟨hinj, hN, hmul, hz, -⟩ := h
  refine ⟨?_, ?_⟩
  · intro 𝔞 𝔟 ha hb
    obtain ⟨x, rfl⟩ := (hN 𝔞).1 ha
    obtain ⟨y, rfl⟩ := (hN 𝔟).1 hb
    rw [← hmul, chiRec_idl D idl hinj, chiRec_idl D idl hinj, chiRec_idl D idl hinj, map_mul]
    simp
  · intro z
    rw [← hz z, chiRec_idl D idl hinj]
    exact D.rest_detCharacter_on_unitary_eq z

end Formalism.MainNotions.TaylorLogMetric
