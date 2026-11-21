import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.MeasureEqOfCos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVDxSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfCo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV

section
noncomputable section

namespace PI.VolStabSW

open Topology Filter Set

section Abs

variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]

def smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) : AddSubgroup W :=
  P.map (DistribMulAction.toAddMonoidHom W t)

omit [TopologicalSpace K] in
theorem mem_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) (z : W) :
    z ∈ smulSub t P ↔ ∃ p ∈ P, t • p = z := by
  simp only [smulSub, AddSubgroup.mem_map, DistribMulAction.toAddMonoidHom_apply]

theorem coe_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) :
    (smulSub t P : Set W) = (fun p => t • p) '' (P : Set W) := by
  ext z
  rw [SetLike.mem_coe, mem_smulSub, Set.mem_image]
  rfl

theorem isOpen_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (ht : t ≠ 0) (P : AddSubgroup W) (hP : IsOpen (P : Set W)) :
    IsOpen (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact isOpenMap_smul₀ ht _ hP

theorem isCompact_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (P : AddSubgroup W) (hP : IsCompact (P : Set W)) :
    IsCompact (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact hP.image (continuous_const_smul t)

theorem eventually_smul_sub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (S : Set W) (hS : IsCompact S) (s : ℕ → K)
    (hs : Tendsto s atTop (𝓝 0)) (N : Set W) (hN : N ∈ 𝓝 (0 : W)) :
    ∃ k, ∀ p ∈ S, s k • p ∈ N := by
  have hev : ∀ᶠ c in 𝓝 (0 : K), ∀ p ∈ S, c • p ∈ N :=
    hS.eventually_forall_of_forall_eventually fun p _ => by
      have h0 : Tendsto (fun z : K × W => z.1 • z.2) (𝓝 ((0 : K), p)) (𝓝 ((0 : K) • p)) :=
        continuous_smul.continuousAt
      rw [zero_smul] at h0
      exact h0 hN
  exact (hs.eventually hev).exists

variable [T2Space X]

theorem reach_of_approx (π : K) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLc : IsCompact (L : Set V)) (hπL : ∀ w ∈ L, π • w ∈ L)
    (D : V →+ X) (hDc : Continuous D) (hDs : ∀ (t : K) w, D (t • w) = t • D w)
    (P : AddSubgroup X) (hPc : IsCompact (P : Set X))
    (hbase : ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub π P) :
    ∀ p ∈ P, ∃ l ∈ L, D l = p := by
  classical
  have hbase' : ∀ p ∈ P, ∃ l ∈ L, ∃ q ∈ P, π • q = p - D l := fun p hp => by
    obtain ⟨l, hl, h⟩ := hbase p hp
    exact ⟨l, hl, (mem_smulSub π P _).1 h⟩
  choose! fl hfl fq hfq hrel using hbase'
  intro p hp

  let ps : ℕ → X := fun k => Nat.rec p (fun _ q => fq q) k
  have hpsS : ∀ k, ps (k + 1) = fq (ps k) := fun k => rfl
  have hpsP : ∀ k, ps k ∈ P := by
    intro k
    induction k with
    | zero => exact hp
    | succ k ih => rw [hpsS]; exact hfq _ ih
  have hπLk : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih => intro w hw; rw [pow_succ, mul_smul]; exact ih _ (hπL w hw)
  let σ : ℕ → V := fun k => ∑ i ∈ Finset.range (k + 1), π ^ i • fl (ps i)
  have hσL : ∀ k, σ k ∈ L := fun k => L.sum_mem fun i _ => hπLk i _ (hfl _ (hpsP i))
  have hrem : ∀ k, p - D (σ k) = π ^ (k + 1) • ps (k + 1) := by
    intro k
    induction k with
    | zero =>
      show p - D (∑ i ∈ Finset.range 1, π ^ i • fl (ps i)) = π ^ 1 • fq p
      rw [Finset.sum_range_one, pow_zero, one_smul, pow_one, hrel p hp]
      rfl
    | succ k ih =>
      have e1 : σ (k + 1) = σ k + π ^ (k + 1) • fl (ps (k + 1)) := Finset.sum_range_succ _ _
      rw [hpsS (k + 1), e1, map_add, hDs, sub_add_eq_sub_sub, ih, ← smul_sub,
        ← hrel _ (hpsP (k + 1)), smul_smul, ← pow_succ]

  have hsmallP : ∀ N ∈ 𝓝 (0 : X), ∀ᶠ c in 𝓝 (0 : K), ∀ q ∈ P, c • q ∈ N := fun N hN =>
    hPc.eventually_forall_of_forall_eventually fun q _ => by
      have h0 : Tendsto (fun z : K × X => z.1 • z.2) (𝓝 ((0 : K), q)) (𝓝 ((0 : K) • q)) :=
        continuous_smul.continuousAt
      rw [zero_smul] at h0
      exact h0 hN
  have hπ1 : Tendsto (fun k : ℕ => π ^ (k + 1)) atTop (𝓝 0) := hπ.comp (tendsto_add_atTop_nat 1)
  have hremT : Tendsto (fun k => p - D (σ k)) atTop (𝓝 0) := by
    refine Tendsto.congr (fun k => (hrem k).symm) ?_
    intro N hN
    exact (hπ1.eventually (hsmallP N hN)).mono fun k hk => hk _ (hpsP (k + 1))
  have hDT : Tendsto (fun k => D (σ k)) atTop (𝓝 p) := by
    simpa using (tendsto_const_nhds (x := p)).sub hremT

  obtain ⟨l, hlL, hcl⟩ := hLc (f := Filter.map σ atTop)
    (Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' hσL)))
  refine ⟨l, hlL, ?_⟩
  have h2 : MapClusterPt (D l) atTop (D ∘ σ) := MapClusterPt.continuousAt_comp hDc.continuousAt hcl
  exact eq_of_nhds_neBot ((show ClusterPt (D l) (Filter.map (D ∘ σ) atTop) from h2).neBot.mono
    (inf_le_inf_left _ hDT))

theorem filt_abstract [ContinuousMul K] (π : K) (hπ0 : π ≠ 0) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V))
    (hπL : ∀ w ∈ L, π • w ∈ L)
    (β : V → V → X) (hβc : Continuous fun q : V × V => β q.1 q.2)
    (hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w)
    (hβ2 : ∀ u w w', β u (w + w') = β u w + β u w')
    (hβs : ∀ (t : K) u w, β u (t • w) = t • β u w)
    (G : V → X) (hG : ∀ u W, G (u + W) = G u + β u W + G W)
    (hGs : ∀ (t : K) w, G (t • w) = t • t • G w)
    (x : V) (hxo : IsOpen (β x '' (L : Set V)))
    (hsmall : ∀ U ∈ 𝓝 (0 : X), ∃ N2 ∈ 𝓝 (0 : V), ∀ c : K, (∀ w ∈ L, c • w ∈ N2) →
      ∀ w ∈ L, c • G w ∈ U) :
    ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ0 : AddSubgroup V,
      (∃ c : K, c ≠ 0 ∧ Λ0 = L.map (DistribMulAction.toAddMonoidHom V c)) → (Λ0 : Set V) ⊆ N →
      ∃ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (D : V →+ X),
        Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set V)) ∧ (∀ n, IsCompact (Λ n : Set V)) ∧ Antitone Λ ∧
        (∀ n, IsOpen (H n : Set X)) ∧ (∀ n, IsCompact (H n : Set X)) ∧
        (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') ∧ (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1) := by
  classical
  have hβ0 : ∀ w, β 0 w = 0 := fun w => by simpa using hβ1 0 0 w
  have hβcont : ∀ u, Continuous fun w => β u w := fun u =>
    hβc.comp (continuous_const.prodMk continuous_id)
  have hπLk : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih => intro w hw; rw [pow_succ, mul_smul]; exact ih _ (hπL w hw)

  let Dx : V →+ X := AddMonoidHom.mk' (β x) (hβ2 x)
  let A : AddSubgroup X := L.map Dx
  have hAcoe : (A : Set X) = β x '' (L : Set V) := AddSubgroup.coe_map _ _
  have hAo : IsOpen (A : Set X) := by rw [hAcoe]; exact hxo
  have hAc : IsCompact (A : Set X) := by rw [hAcoe]; exact hLc.image (hβcont x)
  let U : AddSubgroup X := smulSub π A
  have hUo : IsOpen (U : Set X) := isOpen_smulSub π hπ0 A hAo
  have hU : (U : Set X) ∈ 𝓝 (0 : X) := hUo.mem_nhds U.zero_mem
  have hUA : ∀ a ∈ U, a ∈ A := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := (mem_smulSub π A a).1 ha
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 ha'
    exact AddSubgroup.mem_map.2 ⟨π • l, hπL l hl, hβs π x l⟩

  have hN3 : ∀ᶠ Z in 𝓝 (0 : V), ∀ w ∈ L, β Z w ∈ U :=
    hLc.eventually_forall_of_forall_eventually fun w _ => by
      have h0 : Tendsto (fun q : V × V => β q.1 q.2) (𝓝 ((0 : V), w)) (𝓝 (β 0 w)) :=
        hβc.continuousAt
      rw [hβ0] at h0
      exact h0 hU
  obtain ⟨N2, hN2, hN2'⟩ := hsmall U hU
  refine ⟨N2 ∩ {Z | ∀ w ∈ L, β Z w ∈ U}, inter_mem hN2 hN3, ?_⟩
  rintro y ⟨-, hyN3⟩ Λ0 ⟨c, hc0, rfl⟩ hΛ0N

  let Dy : V →+ X := AddMonoidHom.mk' (β y) (hβ2 y)
  have hDy : ∀ w, Dy w = β y w := fun w => rfl
  have hDys : ∀ (t : K) w, Dy (t • w) = t • Dy w := fun t w => hβs t y w
  have hβy : ∀ w, β y w = β x w + β (y - x) w := fun w => by
    rw [← hβ1, add_sub_cancel]
  have hAy : L.map Dy = A := by
    ext a
    constructor
    · intro ha
      obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 ha
      rw [hDy, hβy]
      exact A.add_mem (AddSubgroup.mem_map.2 ⟨l, hl, rfl⟩) (hUA _ (hyN3 l hl))
    · intro ha
      refine AddSubgroup.mem_map.2 ?_
      refine reach_of_approx π hπ L hLc hπL Dy (hβcont y) hDys A hAc ?_ a ha
      intro p hp
      obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hp
      refine ⟨l, hl, ?_⟩
      have e : Dx l - Dy l = -β (y - x) l := by
        show β x l - β y l = _
        rw [hβy]; abel
      rw [e]
      exact U.neg_mem (hyN3 l hl)

  have hmapS : ∀ (t : K) (P : AddSubgroup V), (smulSub t P).map Dy = smulSub t (P.map Dy) := by
    intro t P
    ext z
    simp only [AddSubgroup.mem_map, mem_smulSub]
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨Dy p, ⟨p, hp, rfl⟩, (hDys t p).symm⟩
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨t • p, ⟨p, hp, rfl⟩, hDys t p⟩
  let Λ : ℕ → AddSubgroup V := fun n => smulSub (π ^ n) (smulSub c L)
  let H : ℕ → AddSubgroup X := fun n => (Λ n).map Dy
  have hH : ∀ n, H n = smulSub (π ^ n) (smulSub c A) := fun n => by
    show (smulSub (π ^ n) (smulSub c L)).map Dy = _
    rw [hmapS, hmapS, hAy]
  have hΛ0 : Λ 0 = smulSub c L := by
    ext z
    simp only [Λ, mem_smulSub, pow_zero, one_smul]
    exact ⟨fun ⟨p, hp, e⟩ => e ▸ hp, fun h => ⟨z, h, rfl⟩⟩
  have hcL : IsOpen (smulSub c L : Set V) := isOpen_smulSub c hc0 L hLo
  have hcLc : IsCompact (smulSub c L : Set V) := isCompact_smulSub c L hLc
  refine ⟨Λ, H, Dy, hΛ0, fun n => isOpen_smulSub _ (pow_ne_zero n hπ0) _ hcL,
    fun n => isCompact_smulSub _ _ hcLc, ?_, fun n => ?_, fun n => ?_, ?_, fun n => rfl, ?_⟩
  · refine antitone_nat_of_succ_le fun n => ?_
    intro z hz
    obtain ⟨p, hp, rfl⟩ := (mem_smulSub _ _ z).1 hz
    obtain ⟨l, hl, rfl⟩ := (mem_smulSub c L p).1 hp
    refine (mem_smulSub _ _ _).2 ⟨c • (π • l), (mem_smulSub c L _).2 ⟨π • l, hπL l hl, rfl⟩, ?_⟩
    rw [smul_comm c π l, smul_smul, ← pow_succ]
  · rw [hH]
    exact isOpen_smulSub _ (pow_ne_zero n hπ0) _ (isOpen_smulSub c hc0 A hAo)
  · show IsCompact ((Λ n).map Dy : Set X)
    rw [AddSubgroup.coe_map]
    exact (isCompact_smulSub _ _ hcLc).image (hβcont y)
  · intro N' hN'
    obtain ⟨k, hk⟩ := eventually_smul_sub (smulSub c A : Set X) (isCompact_smulSub c A hAc)
      (fun k => π ^ k) hπ N' hN'
    refine ⟨k, fun z hz => ?_⟩
    rw [hH] at hz
    obtain ⟨p, hp, rfl⟩ := (mem_smulSub _ _ z).1 hz
    exact hk p hp
  · intro n Z hZ W hW
    rw [hΛ0] at hZ
    have hZN := (hΛ0N hZ).2
    obtain ⟨z, hz, rfl⟩ := (mem_smulSub c L Z).1 hZ
    obtain ⟨W', hW', rfl⟩ := (mem_smulSub _ _ W).1 hW
    obtain ⟨w, hw, rfl⟩ := (mem_smulSub c L W').1 hW'
    set t : K := π ^ n * c with ht
    have e1 : G (y + c • z + π ^ n • c • w) - G (y + c • z) - Dy (π ^ n • c • w)
        = t • (β (c • z) w + t • G w) := by
      rw [hG (y + c • z), hβ1, hDy]
      simp only [ht, hβs, hGs]
      module
    rw [e1]

    have hu1 : β (c • z) w ∈ U := hZN w hw
    have hu2 : t • G w ∈ U := by
      refine hN2' t (fun w' hw' => (hΛ0N ?_).1) w hw
      refine (mem_smulSub c L _).2 ⟨π ^ n • w', hπLk n w' hw', ?_⟩
      rw [smul_smul, ht, mul_comm]
    obtain ⟨a, ha, hae⟩ := (mem_smulSub π A _).1 (U.add_mem hu1 hu2)
    rw [← hAy] at ha
    obtain ⟨l', hl', rfl⟩ := AddSubgroup.mem_map.1 ha
    rw [← hae]
    refine AddSubgroup.mem_map.2 ⟨π ^ (n + 1) • c • l', (mem_smulSub _ _ _).2
      ⟨c • l', (mem_smulSub c L _).2 ⟨l', hl', rfl⟩, rfl⟩, ?_⟩
    rw [hDys, hDys, smul_smul, smul_smul, ht]
    congr 1
    ring

end Abs

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  show (Algebra.TensorProduct.map (AlgHom.id F R) σ) (algebraMap R (R ⊗[F] E) t) =
    algebraMap R (R ⊗[F] E) t
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    map_one]

theorem hR_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J (t • x) y = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J x (t • y) = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

instance hermSMul (σ : E →ₐ[F] E) (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun t S => ⟨t • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h := S.2 a b
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap]
    rw [h]⟩⟩

theorem coe_hermSMul (σ : E →ₐ[F] E) (n : ℕ) (t : R) (S : HermR R σ n) :
    ((t • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = t • (S : Matrix _ _ _) := rfl

instance hermModule (σ : E →ₐ[F] E) (n : ℕ) : Module R (HermR R σ n) :=
  Function.Injective.module R (HermR R σ n).subtype Subtype.coe_injective (fun _ _ => rfl)

end HermMod

theorem exists_unif_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) ∧
      π ∈ v.adicCompletionIntegers F := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
    rw [hv]
    decide
  refine ⟨π, fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

theorem gramFilt_of (hDx : DxOpen) : GramFilt := by
  intro F E _ _ _ _ σ hσ M J hJ hdet a ha1 ha2 v d b x hx
  have : FiniteDimensional F E := Module.Finite.of_basis b
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have hNE : NumberField E :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F E }
  have := locallyCompact_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Fv F v ⊗[F] E) := by
    obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
    exact h.isEmbedding.t2Space
  have : ContinuousSMul (Fv F v) (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (ContinuousSMul (Fv F v) (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : ContinuousSMul (Fv F v) (HermR (Fv F v) σ a) := by
    refine ⟨continuous_induced_rng.2 ?_⟩
    show Continuous fun p : Fv F v × HermR (Fv F v) σ a =>
      p.1 • (p.2 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  obtain ⟨π, hπ0, hπ, hπO⟩ := exists_unif_Fv v
  set L := latSub b v a M with hLdef
  have hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    (PositiveNearLattice.isClopen_latV b v a M).isOpen
  have hLc : IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    PositiveNearLattice.isCompact_latV b v a M
  have hπL : ∀ w ∈ L, π • w ∈ L := by
    intro w hw i j k
    have h := hw i j k
    show (Algebra.TensorProduct.basis (Fv F v) b).repr (π • w i j) k ∈ v.adicCompletionIntegers F
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hπO h
  let β : (Fin a → Fin M → Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) →
      HermR (Fv F v) σ a := fun u w => ⟨gramB (Fv F v) σ J u w, gramB_mem (Fv F v) σ hσ J hJ u w⟩
  have hβc : Continuous fun q : (Fin a → Fin M → Fv F v ⊗[F] E) × (Fin a → Fin M → Fv F v ⊗[F] E) =>
      β q.1 q.2 := (continuous_gramB (Fv F v) σ J).subtype_mk _
  have hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w := by
    intro u u' w
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J (u + u') w i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u' w i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hβ2 : ∀ u w w', β u (w + w') = β u w + β u w' := by
    intro u w w'
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J u (w + w') i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u w' i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hβs : ∀ (t : Fv F v) u w, β u (t • w) = t • β u w := by
    intro t u w
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J u (t • w) i j = t • gramB (Fv F v) σ J u w i j
    simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, smul_add]
  set G := gramH (Fv F v) σ hσ J hJ (n := a) with hGdef
  have hG : ∀ u W, G (u + W) = G u + β u W + G W := by
    intro u W
    apply Subtype.ext
    funext i j
    show gramR (Fv F v) σ J (u + W) i j =
      gramR (Fv F v) σ J u i j + gramB (Fv F v) σ J u W i j + gramR (Fv F v) σ J W i j
    simp only [gramR, gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hGs : ∀ (t : Fv F v) w, G (t • w) = t • t • G w := by
    intro t w
    apply Subtype.ext
    funext i j
    show gramR (Fv F v) σ J (t • w) i j = t • t • gramR (Fv F v) σ J w i j
    simp only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right]
  have hGc : Continuous G := continuous_gramH (Fv F v) σ hσ J hJ
  have hxo : IsOpen (β x '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E))) := by
    have h := hDx F E σ hσ M J hJ hdet a ha1 ha2 v d b x hx
    have e : (fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x -
        gramH (Fv F v) σ hσ J hJ W) = β x := by
      funext W
      rw [← hGdef, hG]
      abel
    rwa [e] at h

  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      exfalso
      have : (1 : E) = 0 := by
        rw [← b.sum_repr (1 : E)]
        simp
      exact one_ne_zero this
    · exact h0
  have hM : 0 < M := by omega
  let i0 : Fin a := ⟨0, ha1⟩
  let j0 : Fin M := ⟨0, hM⟩
  let k0 : Fin d := ⟨0, hd⟩
  let φ : (Fin a → Fin M → Fv F v ⊗[F] E) → Fv F v := fun Y => PositiveNearLattice.crd b (Fv F v) (Y i0 j0) k0
  have hφc : Continuous φ :=
    (PositiveNearLattice.continuous_crd b (Fv F v) k0).comp ((continuous_apply j0).comp (continuous_apply i0))
  have hφs : ∀ (t : Fv F v) Y, φ (t • Y) = t * φ Y := by
    intro t Y
    show (Algebra.TensorProduct.basis (Fv F v) b).repr (t • Y i0 j0) k0 =
      t * (Algebra.TensorProduct.basis (Fv F v) b).repr (Y i0 j0) k0
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  let e0 : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    if i = i0 ∧ j = j0 then inclR (Fv F v) (b k0) else 0
  have he0L : e0 ∈ L := by
    intro i j k
    show PositiveNearLattice.crd b (Fv F v) (e0 i j) k ∈ v.adicCompletionIntegers F
    by_cases hij : i = i0 ∧ j = j0
    · simp only [e0, if_pos hij, PositiveNearLattice.crd_incl, b.repr_self, Finsupp.single_apply]
      split_ifs
      · simp
      · simp
    · simp only [e0, if_neg hij, PositiveNearLattice.crd, map_zero, Finsupp.zero_apply]
      exact zero_mem _
  have hφe : φ e0 = 1 := by
    show PositiveNearLattice.crd b (Fv F v) (e0 i0 j0) k0 = 1
    simp [e0, PositiveNearLattice.crd_incl, b.repr_self]
  have hsmall : ∀ U ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ N2 ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E),
      ∀ c : Fv F v, (∀ w ∈ L, c • w ∈ N2) → ∀ w ∈ L, c • G w ∈ U := by
    intro U hU
    have hT : ∀ᶠ t in 𝓝 (0 : Fv F v), ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)),
        t • G w ∈ U := by
      have hP : ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)),
          ∀ᶠ q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) in 𝓝 ((0 : Fv F v), w), q.1 • G q.2 ∈ U := by
        intro w _
        have h : Tendsto (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2)
            (𝓝 ((0 : Fv F v), w)) (𝓝 (0 : HermR (Fv F v) σ a)) := by
          have hc : Continuous (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2) :=
            continuous_fst.smul (hGc.comp continuous_snd)
          have := hc.tendsto ((0 : Fv F v), w)
          simpa using this
        exact h hU
      exact hLc.eventually_forall_of_forall_eventually
        (P := fun (t : Fv F v) (w : Fin a → Fin M → Fv F v ⊗[F] E) => t • G w ∈ U) hP
    refine ⟨φ ⁻¹' {t | ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), t • G w ∈ U}, ?_, ?_⟩
    · have h0 : φ 0 = 0 := by
        have := hφs 0 0
        simpa using this
      exact hφc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hT)
    · intro c hc w hw
      have h := hc e0 he0L
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hφs, hφe, mul_one] at h
      exact h w hw
  exact filt_abstract π hπ0 hπ L hLo hLc hπL β hβc hβ1 hβ2 hβs G hG hGs x hxo hsmall

end PI.VolStabSW
end
end
