import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlphaDiscriminantHolds
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianRepresents

section
section
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

noncomputable section
namespace GlobalTheory.MaxLatExpo

theorem main : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ P ∈ badP h M, ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ M (P.comap (algebraMap (𝓞 F) (𝓞 K))) b a → ∃ i, vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a i) = 1 ∧ ∀ j, j ≠ i → vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a j) = 0 := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd M hM P hPb b a hJ
  have hP : P.IsMaximal := hPb.1
  have hp : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hpp := hp.isPrime
  have hl : ∀ L : Submodule (𝓞 K) V, locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = loc (K := K) P L :=
    fun L => locF_eq_loc hK hF hP L
  obtain ⟨-, -, -, hloc⟩ := GlobalTheory.MaxLatStruct.main K V h hK hs (UnimodularLocalization.nondegenerate hd) M hM
  obtain ⟨hconj, -, -, x, hxM, ⟨a0, ha0x, ha0P, ha0P2⟩, hstr⟩ := hloc P hPb
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hconj
  obtain ⟨hbX, hspan, horth, hdiag, ha⟩ := hJ
  have hL : IsLatIn (⊤ : Submodule K V) M := ⟨hM.1.1.fg, hM.1.1.span_eq_top⟩
  have hdI : dualIn h ⊤ M = dual h M := by
    ext z; simp [dualIn]
  set p := P.comap (algebraMap (𝓞 F) (𝓞 K)) with hpdef
  set S := HU.SP K p with hSdef
  have hB : ∀ z, z ∈ locF p M ↔ ∀ i, h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun z => by
    exact (Formalism.L2.SG.Pf.G2.mem_B_iff hbX hspan horth hdiag ha hpp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hA : ∀ z, z ∈ locF p (dual h M) ↔ ∀ i, h (b i) z ∈ S := fun z => by
    rw [← hdI]; exact (Formalism.L2.SG.Pf.G2.mem_locF_dualIn_iff hbX hspan horth hdiag ha hF hp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hR : ∀ c, c ∈ locR (K := K) P → c ∈ S := fun c hc => HU.mem_SP_iff_locF.2 (by rw [locF_eq_loc hK hF hP (1 : Submodule (𝓞 K) K)]; exact hc)

  obtain ⟨a0', ha0'⟩ : a0 ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
    refine (conjO_eq_iff_mem_range hF a0).1 (RingOfIntegers.ext ?_)
    rw [conjO_coe]
    change star ((a0 : K)) = (a0 : K)
    rw [ha0x]; exact hs.eq x x
  have ha0ne : a0' ≠ 0 := by
    rintro rfl
    apply ha0P2
    rw [← ha0', map_zero]; exact Submodule.zero_mem _
  have hv0 : vF p a0' = 1 := by
    have h1 := localValuationFiltration.mem_pow_vF hp ha0ne
    have h2 := localValuationFiltration.notMem_pow_vF hp ha0ne
    have hin : a0' ∈ p := by rw [hpdef, Ideal.mem_comap, ha0']; exact ha0P
    rcases Nat.lt_or_ge (vF p a0') 2 with hlt | hge
    · interval_cases hv : vF p a0'
      · rw [zero_add, pow_one] at h2; exact absurd hin h2
      · rfl
    · exfalso
      apply ha0P2
      have := localizedQuotients.ι_mem_pow (K := K) (Ideal.pow_le_pow_right hge h1)
      rwa [hext, ha0'] at this
  have hd0 : h x x = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') := by rw [ha0', ← ha0x]
  have hdne : h x x ≠ 0 := by rw [hd0]; exact Formalism.L2.SG.Pf.G2.jK_ι_ne_zero ha0ne
  have hα : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ≠ 0 := fun i => Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (ha i)
  have hy : ∀ k i, h (b k) ((algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i) = if k = i then 1 else 0 := by
    intro k i
    rw [LinearMap.map_smul, smul_eq_mul]
    split_ifs with hki
    · subst hki; rw [hdiag]; exact inv_mul_cancel₀ (hα k)
    · rw [horth k i hki, mul_zero]
  have hyA : ∀ i, (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i ∈ loc (K := K) P (dual h M) := by
    intro i
    rw [← hl, hA]
    intro k
    rw [hy]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  choose c hc hcM using fun i => hstr _ (hyA i)
  have hcS : ∀ i, c i ∈ S := fun i => hR _ (hc i)
  have hE : ∀ i k, ((if k = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b k) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S := by
    intro i k
    have h1 := hcM i
    rw [← hl] at h1
    have := (hB _).1 h1 k
    rwa [map_sub, hy, LinearMap.map_smul, smul_eq_mul] at this
  have hξ : ∀ k, h (b k) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S :=
    (hB x).1 (LocF.le_locF p M hxM)
  have hdS : h x x ∈ S := by rw [hd0]; exact HU.jK_mem_SP _

  have hle1 : ∀ i, vF p (a i) ≤ 1 := by
    intro i
    by_contra hgt
    push_neg at hgt
    have h1 : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) =
          h x x * (((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) + c i * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl]; field_simp; ring
      rw [e]
      exact S.add_mem (S.mul_mem hdS (hE i i)) (S.mul_mem (hcS i) (hξ i))
    have h1' : algebraMap (𝓞 K) K a0 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      rw [show algebraMap (𝓞 K) K a0 = h x x from ha0x]; exact h1
    have h2 := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) a0).1 h1'
    rw [hext] at h2
    exact ha0P2 (Ideal.pow_le_pow_right hgt h2)
  have huniq : ∀ i j, i ≠ j → vF p (a j) = 1 → 1 ≤ vF p (a i) → False := by
    intro i j hij hj hi
    have hci : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      have e : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) = c i * (((if j = j then (1 : K) else 0) - c j * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)))
          - c j * (((if j = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) := by
        rw [if_pos rfl, if_neg (fun e => hij e.symm)]; ring
      rw [e]
      exact S.sub_mem (S.mul_mem (hcS i) (hE j j)) (S.mul_mem (hcS j) (hE i j))
    obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 (hcS i)
    have hw1 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      rw [hw, mul_div_assoc]; exact S.mul_mem (HU.jK_mem_SP _) hci
    have hwP : w ∈ P := by
      have := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha j) w).1 hw1
      rwa [hj, pow_one, hext] at this
    have hw2 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') ∈ S :=
      (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp ha0ne w).2 (by rw [hv0, pow_one, hext]; exact hwP)
    have htne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (Formalism.L2.SG.Pf.G2.ne_zero_of_notMem ht)
    have htinv : (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ ∈ S := HU.mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ htne]⟩
    have hcd : c i * (h x x)⁻¹ ∈ S := by
      have e : c i * (h x x)⁻¹ = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ * (algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0')) := by
        rw [hw, ← hd0]; field_simp
      rw [e]; exact S.mul_mem htinv hw2
    have h1 : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = ((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))
          + (c i * (h x x)⁻¹) * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl, map_one]; ring
      rw [e]; exact S.add_mem (hE i i) (S.mul_mem hcd (hξ i))
    have h2 := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).1 h1
    rw [hext] at h2
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (Ideal.pow_le_self (by omega) h2))
  have hex : ∃ i, vF p (a i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hPb.2
    have hinv : ∀ i, algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun i =>
      (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).2 (by rw [hcon i, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
    have heq : loc (K := K) P (dual h M) = loc (K := K) P M := by
      rw [← hl, ← hl]
      ext z
      rw [hA, hB]
      constructor
      · intro hz i
        have e : h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = h (b i) z * (algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          rw [map_one]; ring
        rw [e]; exact S.mul_mem (hz i) (hinv i)
      · intro hz i
        have e : h (b i) z = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * (h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          field_simp [hα i]
        rw [e]; exact S.mul_mem (HU.jK_mem_SP _) (hz i)
    obtain ⟨σ, hσ⟩ := GlobalTheory.MaxLatStruct.star_int (K := K)
    have hinj := IsFractionRing.injective (𝓞 K) K
    have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
      fun r => ⟨σ r, hσ r⟩
    unfold IsUnimodularAt
    rw [locDual_dualAt_loc h hinj hstar, ← le_antisymm (locDual_loc_dual_le h P M)
      (locDual_dualAt_le h hstar P M hM.1.1.fg)]
    exact heq
  obtain ⟨i, hi⟩ := hex
  have hi1 : vF p (a i) = 1 := le_antisymm (hle1 i) (Nat.one_le_iff_ne_zero.2 hi)
  refine ⟨i, hi1, fun j hji => ?_⟩
  by_contra hj
  exact huniq j i hji hi1 (Nat.one_le_iff_ne_zero.2 hj)

end GlobalTheory.MaxLatExpo
end
end

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jordan_exponents_maximal_hermitian_lattice_bad_prime : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ P ∈ badP h M, ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ M (P.comap (algebraMap (𝓞 F) (𝓞 K))) b a → ∃ i, vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a i) = 1 ∧ ∀ j, j ≠ i → vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a j) = 0 := by
  atlas_forward_decl GlobalTheory.MaxLatExpo.main
end

section
section
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

noncomputable section

namespace GlobalTheory.DiscAutLenOne

open Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.fibreCountingData

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

def gen (J : JD h L 𝔭 b a) (i : Fin m) : DiscMod h ⊤ L 𝔭 :=
  Submodule.Quotient.mk ⟨phi (K := K) b a (Pi.single i 1), J.u_mem i⟩

theorem div_mem_of_zero (J : JD h L 𝔭 b a) {k : Fin m} (hk : vF 𝔭 (a k) = 0) (z : 𝓞 K) :
    haveI := J.max.isPrime; jK z / jK (ι (a k)) ∈ HU.SP K 𝔭 := by
  have := J.max.isPrime
  rw [div_mem_SP_iff J.max (J.ne k), hk, pow_zero, Ideal.one_eq_top]
  trivial

theorem div_mem_iff_one (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1) (z : 𝓞 K) :
    haveI := J.max.isPrime; jK z / jK (ι (a i)) ∈ HU.SP K 𝔭 ↔ z ∈ extP K 𝔭 ^ 1 := by
  have := J.max.isPrime
  rw [div_mem_SP_iff J.max (J.ne i), hi]

theorem smul_gen_eq_zero_iff (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1) (c : 𝓞 K) :
    c • gen J i = 0 ↔ c ∈ extP K 𝔭 ^ 1 := by
  have := J.max.isPrime
  rw [gen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.coe_smul, J.memB]
  constructor
  · intro H
    have := H i
    rw [crd_smul, J.crd_u, if_pos rfl, mul_one_div] at this
    exact (div_mem_iff_one J hi c).1 this
  · intro hc k
    rw [crd_smul, J.crd_u]
    split_ifs with hk
    · subst hk; rw [mul_one_div]; exact (div_mem_iff_one J hi c).2 hc
    · rw [mul_zero]; exact zero_mem _

theorem exists_smul_gen (J : JD h L 𝔭 b a) {i : Fin m} (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0)
    (q : DiscMod h ⊤ L 𝔭) : ∃ c : 𝓞 K, q = c • gen J i := by
  have := J.max.isPrime
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx := (J.memA x).1 x.2
  obtain ⟨z, hz⟩ := exists_sub_div_mem_SP J.max (J.ne i) (hx i)
  refine ⟨z, ?_⟩
  rw [gen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul, J.memB]
  intro k
  rw [crd_sub, crd_smul, J.crd_u]
  split_ifs with hk
  · subst hk
    have e : crd h b a (x : V) k - jK z * (1 / jK (ι (a k))) =
        (jK (ι (a k)) * crd h b a (x : V) k - jK z) / jK (ι (a k)) := by
      rw [sub_div, mul_div_cancel_left₀ _ (jK_ι_ne_zero (J.ne k))]; ring
    rw [e]; exact hz
  · rw [mul_zero, sub_zero]
    have e : crd h b a (x : V) k = (jK (ι (a k)) * crd h b a (x : V) k) * (jK 1 / jK (ι (a k))) := by
      rw [map_one]; field_simp [jK_ι_ne_zero (J.ne k)]
    rw [e]
    exact mul_mem (hx k) (div_mem_of_zero J (hj k hk) 1)

theorem end_eq_algebraMap (J : JD h L 𝔭 b a) {i : Fin m} (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0)
    (P : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) :
    ∃ c : 𝓞 K, algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c = P := by
  obtain ⟨c, hc⟩ := exists_smul_gen J hj (P (gen J i))
  refine ⟨c, LinearMap.ext fun q => ?_⟩
  obtain ⟨d, rfl⟩ := exists_smul_gen J hj q
  rw [Module.algebraMap_end_apply, map_smul, hc, smul_comm]

theorem algebraMap_eq_zero_iff (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1)
    (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0) (c : 𝓞 K) :
    algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c = 0 ↔ c ∈ extP K 𝔭 ^ 1 := by
  constructor
  · intro H
    have := LinearMap.congr_fun H (gen J i)
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply] at this
    exact (smul_gen_eq_zero_iff J hi c).1 this
  · intro hc
    refine LinearMap.ext fun q => ?_
    obtain ⟨d, rfl⟩ := exists_smul_gen J hj q
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, smul_comm,
      (smul_gen_eq_zero_iff J hi c).2 hc, smul_zero]

end GlobalTheory.DiscAutLenOne

namespace GlobalTheory.DiscAutLenOne

open Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.fibreCountingData

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

theorem cond_iff (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1)
    (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0) (c : 𝓞 K) :
    (∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
      (Submodule.Quotient.mk x' : DiscMod h ⊤ L 𝔭) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c (Submodule.Quotient.mk x) →
      (Submodule.Quotient.mk y' : DiscMod h ⊤ L 𝔭) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) ↔
      conjO K c * c - 1 ∈ extP K 𝔭 ^ 1 := by
  have := J.max.isPrime
  have hjc : jK (conjO K c * c - 1) = star (jK c) * jK c - 1 := by
    rw [map_sub, map_mul, map_one, jK_conjO]
  constructor
  · intro H
    let u : ↥(locF 𝔭 (dualIn h ⊤ L)) := ⟨_, J.u_mem i⟩
    have e1 : (Submodule.Quotient.mk (c • u) : DiscMod h ⊤ L 𝔭) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭)) c (Submodule.Quotient.mk u) := by
      rw [Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
    have H1 := H u u (c • u) (c • u) e1 e1
    rw [← HU.mem_SP_iff_locF] at H1
    have huu : h (u : V) (u : V) = 1 / jK (ι (a i)) := by
      rw [h_expand J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat, Finset.sum_eq_single i]
      · simp only [u]
        rw [J.crd_u, if_pos rfl, star_div₀, star_one, star_jK_ι J.fix]
        field_simp [jK_ι_ne_zero (J.ne i)]
      · intro k _ hk
        simp only [u]
        rw [J.crd_u, if_neg hk, star_zero, zero_mul, zero_mul]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    have e2 : h ((c • u : ↥(locF 𝔭 (dualIn h ⊤ L))) : V) ((c • u : ↥(locF 𝔭 (dualIn h ⊤ L))) : V) -
        h (u : V) (u : V) = jK (conjO K c * c - 1) / jK (ι (a i)) := by
      rw [Submodule.coe_smul, smul_eq_jK c, LinearMap.map_smulₛₗ₂, LinearMap.map_smul,
        smul_eq_mul, smul_eq_mul, starRingEnd_apply, huu, hjc]
      ring
    rw [e2] at H1
    exact (div_mem_iff_one J hi _).1 H1
  · intro hc x y x' y' hx hy
    rw [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul] at hx hy
    rw [← HU.mem_SP_iff_locF]
    have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
        (h (x' : V) (y' : V) - h (c • (x : V)) (c • (y : V))) +
          (h (c • (x : V)) (c • (y : V)) - h (x : V) (y : V)) := by ring
    rw [e]
    refine add_mem (J.h_sub_mem _ _ _ _ (Submodule.smul_mem _ c x.2) (Submodule.smul_mem _ c y.2)
      hx hy) ?_
    have e3 : h (c • (x : V)) (c • (y : V)) - h (x : V) (y : V) =
        (star (jK c) * jK c - 1) * h (x : V) (y : V) := by
      rw [smul_eq_jK c, smul_eq_jK c, LinearMap.map_smulₛₗ₂, LinearMap.map_smul,
        smul_eq_mul, smul_eq_mul, starRingEnd_apply]
      ring
    rw [e3, h_expand J.orth J.diag J.ne J.bX J.loc J.max.isPrime J.lat, Finset.mul_sum]
    refine sum_mem fun k _ => ?_
    have hxA := (J.memA x).1 x.2 k
    have hyA := (J.memA y).1 y.2 k
    have hW : jK (conjO K c * c - 1) / jK (ι (a k)) ∈ HU.SP K 𝔭 := by
      by_cases hk : k = i
      · subst hk; exact (div_mem_iff_one J hi _).2 hc
      · exact div_mem_of_zero J (hj k hk) _
    have hne := jK_ι_ne_zero (K := K) (J.ne k)
    have e4 : (star (jK c) * jK c - 1) * (star (crd h b a (x : V) k) * jK (ι (a k)) * crd h b a (y : V) k) =
        star (jK (ι (a k)) * crd h b a (x : V) k) * (jK (conjO K c * c - 1) / jK (ι (a k))) *
          (jK (ι (a k)) * crd h b a (y : V) k) := by
      rw [star_mul', star_jK_ι J.fix, hjc]
      field_simp
    rw [e4]
    exact mul_mem (mul_mem (star_mem_SP J.fix hxA) hW) hyA

theorem discAut_eq (J : JD h L 𝔭 b a) {i : Fin m} (hi : vF 𝔭 (a i) = 1)
    (hj : ∀ j, j ≠ i → vF 𝔭 (a j) = 0) :
    discAut h ⊤ L 𝔭 = normRepCount K (extP K 𝔭 ^ 1) 1 1 := by
  let Φ : (𝓞 K ⧸ extP K 𝔭 ^ 1) →+* Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) :=
    Ideal.Quotient.lift _ (algebraMap _ _) fun c hc => (algebraMap_eq_zero_iff J hi hj c).2 hc
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((algebraMap_eq_zero_iff J hi hj c).1 hz)
    · intro P
      obtain ⟨c, hc⟩ := end_eq_algebraMap J hj P
      exact ⟨Ideal.Quotient.mk _ c, hc⟩
  rw [discAut, ← NormOneGroup.card_normOne]
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective Φ hΦ) fun z => ?_)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [NormOneGroup.normOne_mk_iff J.fix 𝔭 1 c, Equiv.ofBijective_apply]
  exact (cond_iff J hi hj c).symm

end GlobalTheory.DiscAutLenOne

open GlobalTheory.DiscAutLenOne in

theorem GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ L 𝔭 b a → ∀ i, vF 𝔭 (a i) = 1 → (∀ j, j ≠ i → vF 𝔭 (a j) = 0) → discAut h ⊤ L 𝔭 = normRepCount K (extP K 𝔭 ^ 1) 1 1 := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hF h _ L hL 𝔭 h𝔭 b a hJ i hi hj
  obtain ⟨-, hloc, horth, hdiag, hne⟩ := hJ
  exact discAut_eq ⟨horth, hdiag, hne, hloc, hF, h𝔭, hL.fg, hL.span_eq_top⟩ hi hj
end
end

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discriminantModule_isometries_eq_normOne_residues : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ L 𝔭 b a → ∀ i, vF 𝔭 (a i) = 1 → (∀ j, j ≠ i → vF 𝔭 (a j) = 0) → discAut h ⊤ L 𝔭 = normRepCount K (extP K 𝔭 ^ 1) 1 1 := by
  atlas_forward_decl GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount
end

section
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

namespace GlobalTheory.Mass.MaxFormula

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] in
theorem nondegenerate_of_pos {h : V →ₗ⋆[K] V →ₗ[K] K} [NumberField K] (hd : IsTotPosDef h) :
    h.Nondegenerate := by
  have han : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x h0 φ
    simp [hx] at this
  exact ⟨fun x hx => han x (hx x), fun x hx => han x (hx x)⟩

theorem localMassFactor_eq_of_mem_badPrimes (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) {P : Ideal (𝓞 K)}
    (hP : P ∈ badP h M) :
    lamP h M (P.comap (algebraMap (𝓞 F) (𝓞 K))) =
      ((qIn P : ℝ) ^ Module.finrank K V - (-1) ^ Module.finrank K V) / ((qIn P : ℝ) + 1) := by
  have hnd := nondegenerate_of_pos hd
  obtain ⟨hc, hq2, hq, -⟩ := (GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM).2.2.2 P hP
  have hPm : P.IsMaximal := hP.1
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have h𝔭 : 𝔭.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  obtain ⟨hJ1, hJ2⟩ := jordan_splitting_exists K F V hK hF h hs
  obtain ⟨b, a, hJ⟩ := hJ1 ⊤ M (fun x _ hx => hnd.1 x fun y => hx y trivial)
    ⟨hM.1.1.fg, hM.1.1.span_eq_top⟩ hM.1.2 𝔭 h𝔭
  obtain ⟨i, hi, hj⟩ := GlobalTheory.T.jordan_exponents_maximal_hermitian_lattice_bad_prime K F V hK hF h hs hd M hM P hP b a hJ
  have hv : vd h M 𝔭 = 1 := by
    rw [hJ2 M hM.1.1 𝔭 h𝔭 b a hJ, vJof, Finset.sum_eq_single i (fun j _ => hj j) (by simp)]
    exact hi
  have hcJ : cJof 𝔭 a = 1 := by
    rw [cJof, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun h1 => by_contra fun h2 => h1 (hj j h2), ?_⟩
    rintro rfl
    rw [hi]
    exact one_ne_zero
  have hN : Ideal.absNorm 𝔭 = qIn P := by
    have := absNorm_comap_inert hK hF hPm hc
    rw [hq] at this
    exact Nat.pow_left_injective two_ne_zero this
  have hη : etaF K F 𝔭 = -1 := by rw [h𝔭def, etaF_comap hK hF hPm, if_pos hc]
  have hdisc : (discAut h ⊤ M 𝔭 : ℝ) = (qIn P : ℝ) + 1 := by
    have hq0 : (qIn P : ℝ) ≠ 0 := by exact_mod_cast (by omega : qIn P ≠ 0)
    rw [GlobalTheory.T.discriminantModule_isometries_eq_normOne_residues K F V hK hF h hs M hM.1.1 𝔭 h𝔭 b a hJ i hi hj,
      ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 le_rfl, ThirdPropositionSlot.alphaStd_one, hη, hN]
    field_simp
    ring
  have hm : 1 ≤ Module.finrank K V := by
    have := i.pos
    rwa [finrank_top] at this
  obtain ⟨m, hm'⟩ : ∃ m, Module.finrank K V = m + 1 := ⟨_, (Nat.sub_add_cancel hm).symm⟩
  have hpos := alphaStd_pos hK hF h𝔭 m
  have hq0 : (0 : ℝ) < qIn P := by exact_mod_cast (by omega : 0 < qIn P)
  rw [lamP, alpha_discriminant_holds K F V hK hF h hs hd M hM.1.1 hM.1.2 𝔭 h𝔭 b a hJ, hv, hcJ, hdisc, hm',
    Nat.add_sub_cancel, mul_one]
  have hstep : alphaStd K 𝔭 (m + 1) =
      alphaStd K 𝔭 m * (1 - (-1) ^ (m + 1) * ((qIn P : ℝ) ^ (m + 1))⁻¹) := by
    rw [alphaStd, Finset.prod_Icc_succ_top (by omega), hη, hN, zpow_neg, zpow_natCast, ← hN, ← hη]
    rfl
  rw [hstep, hN]
  field_simp

theorem lamG_eq_lamMax (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) :
    lamG F h M = lamMax h M := by
  have hst := GlobalTheory.MaxLatStruct.main K V h hK hs (nondegenerate_of_pos hd) M hM
  have hfin := hst.1
  let g : {P // P ∈ hfin.toFinset} → {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} := fun P =>
    ⟨P.1.comap (algebraMap (𝓞 F) (𝓞 K)), by
      have : P.1.IsMaximal := (hfin.mem_toFinset.1 P.2).1
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.1⟩
  have hg : Function.Injective g := by
    intro P Q hPQ
    have hP := hfin.mem_toFinset.1 P.2
    have hQ := hfin.mem_toFinset.1 Q.2
    have := (comap_eq_comap_iff hK hF hP.1 hQ.1).1 (congrArg Subtype.val hPQ)
    rw [(hst.2.2.2 P.1 hP).1, or_self] at this
    exact Subtype.ext this.symm
  rw [lamG, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin,
    tprod_eq_prod (s := hfin.toFinset.attach.image g), Finset.prod_image fun _ _ _ _ e => hg e,
    ← Finset.prod_attach hfin.toFinset]
  · exact Finset.prod_congr rfl fun P _ => localMassFactor_eq_of_mem_badPrimes hK hF hs hd hM (hfin.mem_toFinset.1 P.2)
  · intro 𝔭 h𝔭
    obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
    apply localMassFactor_of_valuation_eq_zero hK hF hs hd hM.1.1 hM.1.2 𝔭.2
    rw [← hP𝔭]
    refine (isUnimodularAt_iff_vd hK hF hs hd hM.1.1 hM.1.2 hP).1 (by_contra fun hb => h𝔭 ?_)
    exact Finset.mem_image.2 ⟨⟨P, hfin.mem_toFinset.2 ⟨hP, hb⟩⟩, Finset.mem_attach _ _,
      Subtype.ext hP𝔭⟩

theorem main : MaxMass := by
  intro K _ _ _ hK n hn
  obtain ⟨F, _, _, _, hF⟩ := exists_fixF K hK
  obtain ⟨c₁, -, hall⟩ := massConst_all binary_hermitian_represents liStat hK hF
  refine ⟨c₁ * ∏ j ∈ Finset.Icc 2 n, massRatioRightSide K j, fun V _ _ _ _ _ h hs hp hr M hM => ?_⟩
  have hd : IsTotPosDef h := fun x hx φ => hp φ x hx
  rw [hall n hn V h M hs hd hr hM.1.1 hM.1.2, lamG_eq_lamMax hK hF hs hd hM]

end GlobalTheory.Mass.MaxFormula
end
