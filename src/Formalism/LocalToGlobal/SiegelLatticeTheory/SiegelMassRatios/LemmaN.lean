import Mathlib
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

noncomputable section

namespace Formalism.L2.SG.LemmaN

open NumberField IsDedekindDomain Ideal

abbrev OP (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Type :=
  P.adicCompletionIntegers E

def red {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (OP E P)) :
    Matrix (Fin N) (Fin N) (IsLocalRing.ResidueField (OP E P)) :=
  M.map (IsLocalRing.residue (OP E P))

def Unram (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})], Q.ramificationIdx ℤ = 1

def LemmaNa : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → 3 ≤ p → Unram E p →
  ∀ (P : HeightOneSpectrum (𝓞 E)), (p : 𝓞 E) ∈ P.asIdeal →
  ∀ (N : ℕ) (β : GL (Fin N) (OP E P)), IsOfFinOrder β →
    red (β : Matrix (Fin N) (Fin N) (OP E P)) = 1 → β = 1

def LemmaNb : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → 3 ≤ p → Unram E p →
  ∀ (P : HeightOneSpectrum (𝓞 E)), (p : 𝓞 E) ∈ P.asIdeal →
  ∀ (N : ℕ) (β : GL (Fin N) (OP E P)), IsOfFinOrder β →
    IsNilpotent (red (β : Matrix (Fin N) (Fin N) (OP E P)) - 1) →
    ∃ t : ℕ, orderOf β = p ^ t

def IsProP (p : ℕ) (Q : Type) [Group Q] [TopologicalSpace Q] : Prop :=
  IsTopologicalGroup Q ∧ T2Space Q ∧ CompactSpace Q ∧ TotallyDisconnectedSpace Q ∧
    ∀ U : OpenNormalSubgroup Q, ∃ k : ℕ, (U.toOpenSubgroup : Subgroup Q).index = p ^ k

def LemmaNc : Prop :=
  ∀ (Γ : Type) [Group Γ] (β : Γ), IsOfFinOrder β →
  ∀ (g₁ g₂ : ℕ), g₁.Prime → g₂.Prime → g₁ ≠ g₂ → 3 ≤ g₁ → 3 ≤ g₂ →
  ∀ (Q₁ : Type) [Group Q₁] [TopologicalSpace Q₁], IsProP g₁ Q₁ →
  ∀ (Q₂ : Type) [Group Q₂] [TopologicalSpace Q₂], IsProP g₂ Q₂ →
  ∀ (f₁ : Γ →* Q₁) (f₂ : Γ →* Q₂), Function.Injective f₁ → Function.Injective f₂ →
    β = 1

def LemmaNcGlob : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V),
    Submodule.IsLattice E L →
  ∀ (β : V ≃ₗ[E] V), IsOfFinOrder β →
  ∀ (g₁ g₂ : ℕ), g₁.Prime → g₂.Prime → g₁ ≠ g₂ → 3 ≤ g₁ → 3 ≤ g₂ →
    (∀ PP : Ideal (𝓞 E), PP.IsPrime → (g₁ : 𝓞 E) ∈ PP → Formalism.L2.Col.UnipMod PP L β) →
    (∀ PP : Ideal (𝓞 E), PP.IsPrime → (g₂ : 𝓞 E) ∈ PP → Formalism.L2.Col.UnipMod PP L β) →
    β = 1


theorem eq_one_of_dvd_two_primes {G : Type} [Group G] {β : G} {g₁ g₂ a b : ℕ}
    (hg₁ : g₁.Prime) (hg₂ : g₂.Prime) (hne : g₁ ≠ g₂)
    (ha : orderOf β ∣ g₁ ^ a) (hb : orderOf β ∣ g₂ ^ b) : β = 1 := by
  have hcop : Nat.Coprime (g₁ ^ a) (g₂ ^ b) := Nat.coprime_pow_primes a b hg₁ hg₂ hne
  have h1 : orderOf β = 1 := Nat.eq_one_of_dvd_coprimes hcop ha hb
  exact orderOf_eq_one_iff.mp h1


theorem exists_prime_over (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    ∃ PP : Ideal (𝓞 E), PP.IsPrime ∧ (g : 𝓞 E) ∈ PP := by
  have hP : (span {(g : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hg.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hg
  have hker : (⊥ : Ideal (𝓞 E)).comap (algebraMap ℤ (𝓞 E)) ≤ span {(g : ℤ)} := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot, eq_intCast, Int.cast_eq_zero] at hx
    simp [hx]
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (span {(g : ℤ)}) ⊥ hker
  refine ⟨Q, hQ, ?_⟩
  have : ((g : ℤ)) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by rw [hQc]; exact mem_span_singleton_self _
  simpa using this

theorem lemmaNcGlob_of_exists (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V)
    (hL : Submodule.IsLattice E L) (β : V ≃ₗ[E] V) (hfin : IsOfFinOrder β)
    {g₁ g₂ : ℕ} (hg₁ : g₁.Prime) (hg₂ : g₂.Prime) (hne : g₁ ≠ g₂)
    {w₁ w₂ : Ideal (𝓞 E)} (hw₁ : w₁ ≠ ⊤) (hw₂ : w₂ ≠ ⊤) (hgw₁ : (g₁ : 𝓞 E) ∈ w₁)
    (hgw₂ : (g₂ : 𝓞 E) ∈ w₂) (h₁ : Formalism.L2.Col.UnipMod w₁ L β) (h₂ : Formalism.L2.Col.UnipMod w₂ L β) :
    β = 1 := by
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  obtain ⟨a, ha⟩ := h₁.exists_pow_eq_one hw₁ hL.fg hL.span_eq_top hg₁ hgw₁ hfin
  obtain ⟨b, hb⟩ := h₂.exists_pow_eq_one hw₂ hL.fg hL.span_eq_top hg₂ hgw₂ hfin
  exact eq_one_of_dvd_two_primes hg₁ hg₂ hne (orderOf_dvd_of_pow_eq_one ha)
    (orderOf_dvd_of_pow_eq_one hb)


theorem natCast_mem_maximalIdeal {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    {p : ℕ} (hp : (p : 𝓞 E) ∈ P.asIdeal) :
    ((p : ℕ) : OP E P) ∈ IsLocalRing.maximalIdeal (OP E P) := by
  have hv : Valued.v (((p : ℕ) : OP E P) : P.adicCompletion E) < 1 := by
    have h1 := P.valuedAdicCompletion_eq_valuation (K := E) ((p : ℕ) : 𝓞 E)
    have h2 := (P.valuation_lt_one_iff_mem (K := E) ((p : ℕ) : 𝓞 E)).mpr hp
    simp only [map_natCast] at h1 h2
    push_cast
    rw [h1]; exact h2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have hmul : ((u.val : OP E P) : P.adicCompletion E) * ((u.inv : OP E P) : P.adicCompletion E) = 1 := by
    have := congrArg (fun x : OP E P => (x : P.adicCompletion E)) u.val_inv
    push_cast at this
    exact this
  have hinv : Valued.v ((u.inv : OP E P) : P.adicCompletion E) ≤ 1 := u.inv.2
  rw [hu] at hmul
  have := congrArg Valued.v hmul
  rw [map_mul, map_one] at this
  have hlt := mul_lt_one_of_lt_of_le hv hinv
  rw [this] at hlt
  exact lt_irrefl _ hlt


end Formalism.L2.SG.LemmaN
