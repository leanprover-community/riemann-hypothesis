module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridgeInhab

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_eq_one_of_sub_one {x : k} (hx : valuation k (x - 1) < 1) : valuation k x = 1 := by
  have h := Valuation.map_add_eq_of_lt_right (valuation k) (x := x - 1) (y := 1) (by simpa using hx)
  simpa using h

def eta (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) (j : ℕ) : kˣ →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ m then μ j * δ⁻¹ else 1

theorem eta_mul (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) {i : ℕ} (hi : i < m) :
    eta μ m δ (i + 1) * δ = μ (i + 1) := by
  rw [eta, if_pos ⟨by omega, by omega⟩, inv_mul_cancel_right]

theorem eta_unram (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ)
    (h : ∀ i, i < m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = δ x) (j : ℕ) : IsUnram (eta μ m δ j) := by
  intro x hx
  unfold eta
  split_ifs with hj
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h i (by omega) x hx, mul_inv_cancel]
  · rfl

theorem exists_near {E : Type} [Field E] {ι : E →+* k} (hd : DenseRange ι) (x : k) :
    ∃ a : E, valuation k (ι a - x) < 1 := by
  have hU : {y | valuation k (y - x) < 1} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff]
    exact ⟨1, by rintro _ ⟨z, hz, rfl⟩; simpa using hz⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.mp (hd x) _ hU
  exact ⟨a, hy⟩

theorem tame_near {μ : kˣ →* ℂˣ} (h : IsTame μ) {x u : kˣ} (hx : valuation k (x : k) = 1)
    (hu : valuation k ((u : k) - x) < 1) : μ u = μ x := by
  have hx0 : (x : k) ≠ 0 := x.ne_zero
  have hy : valuation k (((x⁻¹ * u : kˣ) : k) - 1) < 1 := by
    have e : ((x⁻¹ * u : kˣ) : k) - 1 = (x : k)⁻¹ * ((u : k) - x) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [e, map_mul, map_inv₀, hx, inv_one, one_mul]; exact hu
  have := h _ hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

end Loc

section Arith
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem valuation_self (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) :
    LocE.vP P q (q : E) = 1 := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have hnu : ¬ IsUnit (0 : 𝓞 E ⧸ P.asIdeal) := not_isUnit_zero
  have key : ∀ z : ℤ, IsUnit (redP P ((q : E) / (q : E) ^ z)) ↔ z = 1 := by
    intro z
    constructor
    · intro h
      by_contra hz
      rcases lt_or_gt_of_ne hz with hlt | hgt
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨(-z).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = algebraMap (𝓞 E) E (((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
          rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, map_pow, map_natCast, pow_succ']
        rw [e, reduction_coe] at h
        have h1 : Ideal.Quotient.mk P.asIdeal (((q : ℕ) : 𝓞 E) ^ (k + 1)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [h1] at h; exact hnu h
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = (k : ℤ) + 2 := ⟨(z - 2).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = ((q : E) ^ (k + 1))⁻¹ := by
          have e1 : (q : E) ^ z = (q : E) ^ (k + 1) * (q : E) := by
            rw [hk, ← pow_succ, ← zpow_natCast]; congr 1
          rw [e1, div_mul_eq_div_div_swap, div_self hqE, one_div]
        have hni : ¬ IntAt P ((q : E) / (q : E) ^ z) := by
          rintro ⟨r, s, hs, hrs⟩
          apply hs
          have h2 : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
            rw [map_mul, ← hrs, e, map_pow, map_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hqE), mul_one]
          rw [(FaithfulSMul.algebraMap_injective (𝓞 E) E) h2]
          exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [reduction_eq_zero_of_not_integral P hni] at h; exact hnu h
    · rintro rfl
      rw [zpow_one, div_self hqE]
      have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      rw [h3, reduction_coe, map_one]; exact isUnit_one
  unfold LocE.vP
  have h4 : (fun z : ℤ => IsUnit (redP P ((q : E) / (q : E) ^ z))) = fun z => z = 1 := funext fun z => propext (key z)
  rw [h4]
  exact Classical.epsilon_spec (p := fun z : ℤ => z = 1) ⟨1, rfl⟩

end Arith

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

end Chain

end GlobalTheory.TwBridgeInhab
