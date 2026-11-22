module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement

@[expose] public section

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp

noncomputable section
namespace GlobalTheory.KernelComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}

section Indicator
open scoped Classical

variable [Fintype n'] (q : Unif k) {P₁ : Pair k n'} {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n)
  (x : Matrix n n' k)
include he

end Indicator

theorem card_withKer (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    (withKer L).card = (withLat L).card := by
  classical
  by_cases hfull : L.IsFullLattice k
  · letI : L.IsFullLattice k := hfull
    letI := Fintype.ofFinite (Red L)
    letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
    have hc : Fintype.card (Red L) = Fintype.card (Module.Dual 𝓀[k] (Red L)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := 𝓀[k]),
        Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := Module.Dual 𝓀[k] (Red L)), Subspace.dual_finrank_eq]
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat L]
    simp [hc]
  · have hk : withKer L = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro P hP
      apply hfull
      rw [← mem_withKer.mp hP]
      exact P.ker_isLat)
    have hl : withLat L = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro P hP
      apply hfull
      rw [← mem_withLat.mp hP]
      exact P.isLat)
    simp [hk, hl]

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem exists_det (q : Unif k) (P : Pair k n) :
    ∃ d : GL n k, d • P.ker = P.lat ∧ Matrix.GeneralLinearGroup.det d = q.unit⁻¹ := by
  obtain ⟨i⟩ : Nonempty n := by
    by_contra h
    haveI := not_nonempty_iff.1 h
    exact P.fn_ne (LinearMap.ext fun y => by rw [Subsingleton.elim y 0]; simp)
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  have hdet : (Matrix.diagonal (Function.update (1 : n → k) i (q.1 : k))).det = (q.1 : k) := by
    simp [Matrix.det_diagonal, Finset.prod_update_of_mem]
  let d : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ q.ne_zero)
  have hd : ∀ (y : n → k) j, (d • y) j = Function.update (1 : n → k) i (q.1 : k) j * y j := fun y j =>
    Matrix.mulVec_diagonal _ _ _
  have h1 : d⁻¹ • (stdPair k i).ker = (stdPair k i).lat := by
    ext y
    rw [mem_smul_iff, inv_inv, Pair.mem_ker, stdPair_hasVal]
    change _ ↔ y ∈ stdLat k n
    rw [mem_stdLat]
    constructor
    · rintro ⟨h, h0⟩ j
      by_cases hj : j = i
      · subst hj
        obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)
        have h2 : (q.1 : k) * y j = q.1 * s := by simpa [hd] using congrArg Subtype.val hs
        rw [mul_left_cancel₀ q.ne_zero h2]
        exact s.2
      · simpa [hd, hj] using h j
    · intro h
      refine ⟨fun j => ?_, (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨y i, h i⟩, Subtype.ext (by simp [hd])⟩)⟩
      by_cases hj : j = i
      · subst hj
        simpa [hd] using mul_mem q.1.2 (h j)
      · simpa [hd, hj] using h j
  refine ⟨a * d⁻¹ * a⁻¹, by rw [Pair.smul_ker, Pair.smul_lat, mul_smul, mul_smul, inv_smul_smul, h1], ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, _root_.inv_inj]
  exact Units.ext hdet

theorem valuation_det (q : Unif k) (P : Pair k n) {g : GL n k} (hg : g • P.ker = P.lat) :
    valuation k ((Matrix.GeneralLinearGroup.det g * q.unit : kˣ) : k) = 1 := by
  obtain ⟨d, hd, hdet⟩ := exists_det q P
  have := valuation_det_of_fix P.ker (h := d⁻¹ * g) (by rw [mul_smul, hg, ← hd, inv_smul_smul])
  rwa [map_mul, map_inv, hdet, inv_inv, mul_comm] at this

variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)

theorem eq_of_base {φ φ' : Form k n V} (h : φ ∈ EqForm π) (h' : φ' ∈ EqForm π) (e : φ Q₀ = φ' Q₀) : φ = φ' := by
  ext Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [h g, h' g, e]

end GlobalTheory.KernelComm
