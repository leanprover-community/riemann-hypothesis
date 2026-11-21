import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleSeqOfFiniteNonempty
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterCongrRootOfUnityPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDuality

section
namespace GlobalTheory.IntegralPowerMultiple

theorem exists_pow_mul_integral {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (c : FractionRing O) :
    ∃ (n : ℕ) (a : O), algebraMap O (FractionRing O) (ϖ ^ n) * c = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb

  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, ((u⁻¹ : Oˣ) : O) * a, ?_⟩
  have hbK : algebraMap O (FractionRing O) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hu' : algebraMap O (FractionRing O) (u : O) * algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [hu, map_mul] at hbK
  rw [hu, map_mul, map_mul]
  rw [mul_div_assoc', div_eq_iff hbK]
  linear_combination (-(algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) (ϖ ^ n))) * hu'

theorem exists_pow_smul_mem : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O] {V : Type} [inst_3 : AddCommGroup V] [inst_4 : Module O V] [inst_5 : Module (FractionRing O) V] [inst_6 : IsScalarTower O (FractionRing O) V] (T : Submodule O V), Formalism.RepresentationBoundsCohomology.LOC.IsLatticeIn T → ∀ (ϖ : O), Irreducible ϖ → ∀ (v : V), ∃ (m : ℕ), ϖ ^ m • v ∈ T := by
  intro O _ _ _ V _ _ _ _ T hT ϖ hϖ v
  have hv : v ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT.2]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    rw [smul_add, pow_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem _ h₁
    · rw [mul_smul]
      exact T.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx

    obtain ⟨n, a, ha⟩ := exists_pow_mul_integral hϖ c
    refine ⟨n + m, ?_⟩
    have key : ϖ ^ (n + m) • (c • x) = a • (ϖ ^ m • x) := by
      rw [← algebraMap_smul (FractionRing O) (ϖ ^ (n + m)) (c • x), smul_smul,
        ← algebraMap_smul (FractionRing O) a, ← algebraMap_smul (FractionRing O) (ϖ ^ m) x, smul_smul,
        ← ha, pow_add, map_mul]
      congr 1
      ring
    rw [key]
    exact T.smul_mem a hm

end GlobalTheory.IntegralPowerMultiple
end

section
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.LatticeQuotBound

theorem exists_pow_smul_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (v : V) : ∃ m : ℕ, ϖ ^ m • v ∈ T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem ..)

theorem pow_smul_eq_zero_of_compact : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  intro O _ _ _ V _ _ _ _ _ _ X _ _ T hT hTo ϖ hϖ c hc
  have hopen : ∀ m : ℕ, IsOpen {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro m
    have h : IsOpen ((Submodule.Quotient.mk : V → V ⧸ T) ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
      rw [isOpen_iff_forall_mem_open]
      intro v hv
      refine ⟨(fun t => v + t) '' (T : Set V), ?_, isOpenMap_add_left v _ hTo,
        ⟨0, T.zero_mem, add_zero v⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv ⊢
      rw [Submodule.Quotient.mk_add, smul_add, hv, zero_add,
        (Submodule.Quotient.mk_eq_zero T).2 ht, smul_zero]
    exact isOpen_coinduced.mpr h
  have hcover : ∀ x, ∃ m : ℕ, x ∈ c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro x
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective T (c x)
    obtain ⟨m, hm⟩ := exists_pow_smul_mem T hT ϖ hϖ v
    refine ⟨m, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hv, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero T).2 hm]
  have hmono : Monotone (fun m : ℕ => c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
    intro a b hab x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    rw [← Nat.add_sub_cancel' hab, pow_add, mul_comm, mul_smul, hx, smul_zero]
  obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover _ (fun m => (hopen m).preimage hc)
    (fun x _ => Set.mem_iUnion.2 (hcover x)) hmono.directed_le
  exact ⟨m, fun x => hm (Set.mem_univ x)⟩

end GlobalTheory.LatticeQuotBound
end

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_quotient_torsion_bounded : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  atlas_forward_decl GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact
end

section
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.CocycleLimit

theorem exists_continuous_cocycle_lift_of_compatible : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  intro O _ G _ _ M _ _ _ _ _ _ _ ρ a r hopen hbasis w hw hstep
  set N : ℕ → Submodule O M := fun n => powSub (M := M) a n with hN

  have hclosedN : ∀ n, IsClosed ((N n : Submodule O M) : Set M) := fun n =>
    AddSubgroup.isClosed_of_isOpen (N n).toAddSubgroup (hopen n)

  have hex : ∀ g, ∃ x, ∀ k, x - w k g ∈ N (r + k) := by
    intro g
    let C : ℕ → Set M := fun k => {x | x - w k g ∈ N (r + k)}
    have hsub : ∀ k, C (k + 1) ⊆ C k := by
      intro k x hx
      have h1 : x - w (k + 1) g ∈ N (r + k) :=
        powSub_anti a (by omega : r + k ≤ r + (k + 1)) hx
      have h2 := hstep k g
      show x - w k g ∈ N (r + k)
      have : x - w k g = (x - w (k + 1) g) + (w (k + 1) g - w k g) := by abel
      rw [this]; exact (N (r + k)).add_mem h1 h2
    have hne : ∀ k, (C k).Nonempty := fun k => ⟨w k g, by simp [C, (N (r + k)).zero_mem]⟩
    have hcl : ∀ k, IsClosed (C k) := fun k =>
      (hclosedN (r + k)).preimage (continuous_id.sub continuous_const)
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hsub hne
      (hcl 0).isCompact hcl
    exact ⟨x, fun k => Set.mem_iInter.1 hx k⟩
  choose e he using hex

  have hzero : ∀ x : M, (∀ k, x ∈ N (r + k)) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨n, hn⟩ := hbasis ({x}ᶜ) (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    have : x ∈ N (r + n) := hx n
    exact hn (powSub_anti a (by omega : n ≤ r + n) this) rfl

  have hcoc : ∀ k g h, w k (g * h) - (w k g + ρ g (w k h)) ∈ N (r + k) := by
    intro k g h
    have := (hw k).2 g h
    simp only [quotRep_mk] at this
    rw [← Submodule.Quotient.mk_add] at this
    exact (Submodule.Quotient.eq _).1 this
  refine ⟨e, ⟨?_, ?_⟩, fun k g => he g k⟩
  ·
    rw [continuous_iff_continuousAt]
    intro g0 U hU
    have hV : {y : M | y + e g0 ∈ U} ∈ nhds (0 : M) :=
      (continuous_add_right (e g0)).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨n, hn⟩ := hbasis _ hV
    let q : G → M ⧸ powSub (M := M) a (r + n) := fun g => Submodule.Quotient.mk (w n g)
    have hq : Continuous q := (hw n).1
    have hsing : IsOpen ({q g0} : Set (M ⧸ powSub (M := M) a (r + n))) := by
      rw [← (Submodule.isOpenQuotientMap_mkQ (powSub (M := M) a (r + n))).isQuotientMap.isOpen_preimage]
      have : (Submodule.mkQ (powSub (M := M) a (r + n))) ⁻¹' {q g0} =
          (fun y => y - w n g0) ⁻¹' ((N (r + n) : Submodule O M) : Set M) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Submodule.mkQ_apply, q,
          SetLike.mem_coe, N]
        exact Submodule.Quotient.eq _
      rw [this]
      exact (hopen (r + n)).preimage (continuous_id.sub continuous_const)
    have hS : q ⁻¹' {q g0} ∈ nhds g0 := (hsing.preimage hq).mem_nhds rfl
    show e ⁻¹' U ∈ nhds g0
    refine Filter.mem_of_superset hS ?_
    intro g hg
    have hg' : w n g - w n g0 ∈ N (r + n) := (Submodule.Quotient.eq _).1 hg
    have hmem : e g - e g0 ∈ N (r + n) := by
      have : e g - e g0 = (e g - w n g) + (w n g - w n g0) - (e g0 - w n g0) := by abel
      rw [this]
      exact (N (r + n)).sub_mem ((N (r + n)).add_mem (he g n) hg') (he g0 n)
    have := hn (powSub_anti a (by omega : n ≤ r + n) hmem)
    simpa using this
  ·
    intro g h
    rw [← sub_eq_zero]
    apply hzero
    intro k
    have : e (g * h) - (e g + ρ g (e h)) =
        (e (g * h) - w k (g * h)) - (e g - w k g) - ρ g (e h - w k h) +
          (w k (g * h) - (w k g + ρ g (w k h))) := by
      rw [map_sub]; abel
    rw [this]
    refine (N (r + k)).add_mem ((N (r + k)).sub_mem ((N (r + k)).sub_mem (he _ k) (he _ k))
      (powSub_stable ρ a _ g _ (he h k))) (hcoc k g h)

end GlobalTheory.CocycleLimit
end
end

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_cocycle_lift_of_compatible' : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  atlas_forward_decl GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible
end

section
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.ZpHomAdic

open IsLocalRing Filter Topology

theorem isPrecomplete_of_compact {O : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] (hA : IsAdic (maximalIdeal O)) :
    IsPrecomplete (maximalIdeal O) O := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, -, hL⟩ := (isCompact_univ (X := O)).exists_clusterPt (f := Filter.map f atTop)
    (le_principal_iff.2 univ_mem)
  refine ⟨L, fun n => ?_⟩
  have hopen : IsOpen ((maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hA).1 n
  have hclosed : IsClosed ((maximalIdeal O ^ n : Ideal O) : Set O) :=
    AddSubgroup.isClosed_of_isOpen ((maximalIdeal O ^ n).toAddSubgroup) hopen
  have hS : IsClosed {y : O | f n - y ∈ maximalIdeal O ^ n} :=
    hclosed.preimage (continuous_const.sub continuous_id)
  have hmem : {y : O | f n - y ∈ maximalIdeal O ^ n} ∈ Filter.map f atTop := by
    refine Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨n, fun k hk => ?_⟩)
    have := hf hk
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  have hL' : L ∈ closure {y : O | f n - y ∈ maximalIdeal O ^ n} :=
    mem_closure_iff_clusterPt.2 (hL.mono (le_principal_iff.2 hmem))
  rw [hS.closure_eq] at hL'
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact hL'

theorem isHausdorff_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsHausdorff (maximalIdeal O) O := by
  refine ⟨fun x hx => ?_⟩
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal O)
    (maximalIdeal.isMaximal O).ne_top, Ideal.mem_iInf]
  intro n
  have := hx n
  rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this

theorem ringHom_zmod_apply {N : ℕ} [NeZero N] {R : Type*} [Ring R] (ψ : ZMod N →+* R) (z : ZMod N) :
    ψ z = ((z.val : ℕ) : R) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact map_natCast ψ _

theorem val_toZModPow_sub_mem {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {m n : ℕ} (h : m ≤ n)
    (x : ℤ_[p]) :
    ((PadicInt.toZModPow n x).val : O) - ((PadicInt.toZModPow m x).val : O) ∈
      Ideal.span {(p : O) ^ m} := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp⟩
  have h1 : (((PadicInt.toZModPow n x).val : ℕ) : ZMod (p ^ m)) =
      (((PadicInt.toZModPow m x).val : ℕ) : ZMod (p ^ m)) := by
    rw [ZMod.natCast_val, ZMod.natCast_zmod_val, PadicInt.cast_toZModPow m n h]
  rw [ZMod.natCast_eq_natCast_iff] at h1
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd.1 h1.symm)
  rw [Ideal.mem_span_singleton]
  refine ⟨(c : O), ?_⟩
  have := congrArg (fun t : ℤ => (t : O)) hc
  push_cast at this
  exact this

end GlobalTheory.ZpHomAdic

namespace GlobalTheory.ZpHomAdic
open IsLocalRing

noncomputable def zmodToQuot (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hp : (p : O) ∈ maximalIdeal O) (n : ℕ) : ZMod (p ^ n) →+* O ⧸ maximalIdeal O ^ n :=
  (Ideal.Quotient.lift (Ideal.span {((p ^ n : ℕ) : ℤ)}) (Int.castRingHom _) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_natCast, Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk (maximalIdeal O ^ n)) p,
      ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hp n), mul_zero])).comp
    (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom

theorem exists_ringHom_padicInt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] (hT : IsTopologicalRing O)
    (_hC : CompactSpace O) (_hH : T2Space O) (hA : IsAdic (maximalIdeal O))
    (hp : (p : O) ∈ maximalIdeal O) :
    ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ),
      ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} := by
  haveI := hT
  haveI : IsAdicComplete (maximalIdeal O) O :=
    { toIsHausdorff := isHausdorff_dvr, toIsPrecomplete := isPrecomplete_of_compact hA }
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI hNZ : ∀ n, NeZero (p ^ n) := fun n => ⟨pow_ne_zero _ hp0⟩
  let f : (n : ℕ) → ℤ_[p] →+* O ⧸ maximalIdeal O ^ n := fun n =>
    (zmodToQuot p O hp n).comp (PadicInt.toZModPow n)
  have hfx : ∀ n x, f n x = Ideal.Quotient.mk _ ((PadicInt.toZModPow n x).val : O) := by
    intro n x
    show zmodToQuot p O hp n _ = _
    rw [ringHom_zmod_apply, map_natCast]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal O) hle).comp (f n) = f m := by
    intro m n hle
    ext x
    rw [RingHom.comp_apply, hfx, hfx, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
    exact Ideal.span_singleton_le_iff_mem _ |>.2 (Ideal.pow_mem_pow hp m)
      (val_toZModPow_sub_mem hle x)
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal O) f hf, fun x k => ?_⟩
  set ι := IsAdicComplete.liftRingHom (maximalIdeal O) f hf
  have hι : ∀ n, ι x - ((PadicInt.toZModPow n x).val : O) ∈ maximalIdeal O ^ n := by
    intro n
    rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hfx]
  set J : Ideal O := Ideal.span {(p : O) ^ k}
  rw [← Submodule.Quotient.mk_eq_zero (p := J), ← Submodule.mem_bot O,
    ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := O ⧸ J) (maximalIdeal O)
      (maximalIdeal.isMaximal O).ne_top, Submodule.mem_iInf]
  intro n
  have hle : maximalIdeal O ^ max n k • (⊤ : Submodule O (O ⧸ J)) ≤ maximalIdeal O ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_left n k))
  refine hle ?_
  have hsplit : ι x - ((PadicInt.toZModPow k x).val : O) =
      (ι x - ((PadicInt.toZModPow (max n k) x).val : O)) +
      (((PadicInt.toZModPow (max n k) x).val : O) - ((PadicInt.toZModPow k x).val : O)) := by ring
  rw [hsplit, Submodule.Quotient.mk_add,
    (Submodule.Quotient.mk_eq_zero J).2 (val_toZModPow_sub_mem (le_max_right n k) x), add_zero,
    ← mul_one (ι x - _), ← smul_eq_mul, Submodule.Quotient.mk_smul]
  exact Submodule.smul_mem_smul (hι _) Submodule.mem_top

theorem zp_ringHom : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ), ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} :=
  fun hT hC hH hA hp => exists_ringHom_padicInt hT hC hH hA hp

end GlobalTheory.ZpHomAdic
end

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_ringHom_congr_toZModPow : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ), ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} := by
  atlas_forward_decl GlobalTheory.ZpHomAdic.zp_ringHom
end

section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicCharacter_congr_root_of_unity_pow : ∀ {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ), ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) = PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by
  first | exact @GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | exact GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | (intros; apply GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr <;> assumption)
end

section
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LatTorsFinite

theorem finite_quot_of_isOpen {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (hI : IsOpen (I : Set O)) : Finite (O ⧸ I) := by
  have hU : ∀ x : O, IsOpen ((fun y => y - x) ⁻¹' (I : Set O)) := fun x =>
    hI.preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : O => (fun y => y - x) ⁻¹' (I : Set O))
    hU (fun y _ => Set.mem_iUnion.2 ⟨y, by simp [I.zero_mem]⟩)
  refine Finite.of_surjective (fun x : t => Ideal.Quotient.mk I (x : O)) ?_
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨⟨x, hx⟩, ?_⟩
  exact (Ideal.Quotient.eq.2 hyx).symm

theorem finite_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (hO : IsTopologicalRing O) (hc : CompactSpace O)
    (hA : IsAdic (IsLocalRing.maximalIdeal O)) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hopen : IsOpen (((IsLocalRing.maximalIdeal O) ^ n : Ideal O) : Set O) :=
    (isAdic_iff.1 hA).1 n
  rw [hm, Ideal.span_singleton_pow] at hopen
  exact finite_quot_of_isOpen _ hopen

theorem finite_ker_pow_smul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hO : IsTopologicalRing O)
    (hc : CompactSpace O) (hA : IsAdic (IsLocalRing.maximalIdeal O)) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  haveI := finite_quot_pow hO hc hA hϖ n
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
      (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})

  let rep : V ⧸ T → V := fun q => Classical.choose (Submodule.Quotient.mk_surjective T q)
  have hrep : ∀ q, Submodule.Quotient.mk (p := T) (rep q) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective T q)
  have hmem : ∀ x : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)),
      ϖ ^ n • rep (x : V ⧸ T) ∈ T := by
    intro x
    have hx : (ϖ ^ n) • (x : V ⧸ T) = 0 := x.2
    rw [← hrep (x : V ⧸ T), ← Submodule.Quotient.mk_smul] at hx
    exact (Submodule.Quotient.mk_eq_zero T).1 hx

  have hinj : ∀ v w : V, ϖ ^ n • v = ϖ ^ n • w → v = w := by
    intro v w h
    have h0 : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) v,
      ← algebraMap_smul (FractionRing O) (ϖ ^ n) w] at h
    exact smul_right_injective V h0 h
  let f : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)) →
      T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T) :=
    fun x => Submodule.Quotient.mk ⟨ϖ ^ n • rep (x : V ⧸ T), hmem x⟩
  refine Finite.of_injective f ?_
  intro x y hxy
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hxy
  obtain ⟨t, -, ht⟩ := hxy
  have ht' : ϖ ^ n • (t : V) = ϖ ^ n • (rep (x : V ⧸ T) - rep (y : V ⧸ T)) := by
    rw [smul_sub]
    exact congrArg Subtype.val ht
  have hd := hinj _ _ ht'
  apply Subtype.ext
  rw [← hrep (x : V ⧸ T), ← hrep (y : V ⧸ T), Submodule.Quotient.eq, ← hd]
  exact t.2

end GlobalTheory.LatTorsFinite
end
end

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (T : Submodule O V), IsTopologicalRing O → CompactSpace O → IsAdic (IsLocalRing.maximalIdeal O) → IsLatticeIn T → ∀ ϖ : O, Irreducible ϖ → ∀ n : ℕ, Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  atlas_forward_decl GlobalTheory.LatTorsFinite.finite_ker_pow_smul
end

section
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

section PerfL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V]

theorem exists_form_of_not_mem {T : Submodule O V} (hT : IsLatticeIn T) {v : V} (hv : v ∉ T) :
    ∃ ψ : V →ₗ[FractionRing O] FractionRing O,
      (∀ t ∈ T, ψ t ∈ (1 : Submodule O (FractionRing O))) ∧
        ψ v ∉ (1 : Submodule O (FractionRing O)) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.IsTorsionFree O T := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    have h1 : (algebraMap O (FractionRing O) r) • (m : V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val h
    rcases smul_eq_zero.1 h1 with h2 | h2
    · left
      exact (IsFractionRing.injective O (FractionRing O)) (by rw [h2, map_zero])
    · right
      exact Subtype.ext h2
  haveI : Module.Free O T := Module.free_of_finite_type_torsion_free'
  let e := Module.Free.chooseBasis O T
  let w : Module.Free.ChooseBasisIndex O T → V := fun i => (e i : V)
  have hliO : LinearIndependent O w := e.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli : LinearIndependent (FractionRing O) w :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO
  have hspO : Submodule.span O (Set.range w) = T := by
    have h := congrArg (Submodule.map T.subtype) e.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range w) := by
    rw [← hT.2]
    apply Submodule.span_le.2
    intro t ht
    rw [← hspO] at ht
    exact Submodule.span_subset_span O (FractionRing O) (Set.range w) ht
  let bK := Module.Basis.mk hli hsp
  have hbK : ∀ i, bK i = w i := fun i => Module.Basis.mk_apply hli hsp i

  have hint : ∀ t ∈ T, ∀ j, bK.repr t j ∈ (1 : Submodule O (FractionRing O)) := by
    intro t ht
    rw [← hspO] at ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro j
      rw [← hbK, bK.repr_self, Finsupp.single_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => intro j; simp
    | add x y _ _ hx hy => intro j; rw [map_add, Finsupp.add_apply]; exact Submodule.add_mem _ (hx j) (hy j)
    | smul a x _ hx =>
      intro j
      rw [← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, algebraMap_smul]
      exact Submodule.smul_mem _ a (hx j)
  have hex : ∃ j, bK.repr v j ∉ (1 : Submodule O (FractionRing O)) := by
    by_contra hne
    push Not at hne
    apply hv
    rw [← bK.linearCombination_repr v, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hne j)
    rw [← ha, algebraMap_smul, hbK]
    exact Submodule.smul_mem _ a (e j).2
  obtain ⟨j, hj⟩ := hex
  exact ⟨bK.coord j, fun t ht => hint t ht j, hj⟩

theorem exists_mul_eq_inv_unif {ϖ : O} (hϖ : Irreducible ϖ) {u : FractionRing O}
    (hu : u ∉ (1 : Submodule O (FractionRing O))) :
    ∃ o : O, algebraMap O (FractionRing O) o * u = (algebraMap O (FractionRing O) ϖ)⁻¹ := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Submodule.zero_mem _)
  rcases ValuationRing.isInteger_or_isInteger O u with h | ⟨w, hw⟩
  · exact absurd (Submodule.mem_one.2 h) hu
  have hwu : ¬ IsUnit w := by
    intro hw'
    apply hu
    refine Submodule.mem_one.2 ⟨((hw'.unit⁻¹ : Oˣ) : O), ?_⟩
    have h1 : algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O) * u⁻¹ = 1 := by
      rw [← hw, ← map_mul, IsUnit.val_inv_mul, map_one]
    calc algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O)
        = algebraMap O (FractionRing O) ((hw'.unit⁻¹ : Oˣ) : O) * (u⁻¹ * u) := by
          rw [inv_mul_cancel₀ hu0, mul_one]
      _ = u := by rw [← mul_assoc, h1, one_mul]
  have hwm : w ∈ IsLocalRing.maximalIdeal O := hwu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hwm
  obtain ⟨o, rfl⟩ := hwm
  refine ⟨o, ?_⟩
  rw [map_mul] at hw
  symm
  apply inv_eq_of_mul_eq_one_right
  calc algebraMap O (FractionRing O) ϖ * (algebraMap O (FractionRing O) o * u)
      = (algebraMap O (FractionRing O) ϖ * algebraMap O (FractionRing O) o) * u := by ring
    _ = 1 := by rw [hw, inv_mul_cancel₀ hu0]

end PerfL

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT]
  [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT']
  [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  {G : Type} [Group G] [TopologicalSpace G]

theorem exists_dual_pairKO_eq_inv_unif (D : LatData O G VT VT') (hT : IsLatticeIn D.T)
    (hP : PerfectRight D.bT) (ϖ : O) (hϖ : Irreducible ϖ) (x : VT ⧸ D.T) (hx : x ≠ 0) :
    ∃ f : ↥D.T', pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective D.T x
  have hv : v ∉ D.T := fun h => hx ((Submodule.Quotient.mk_eq_zero _).2 h)
  obtain ⟨ψ, hψT, hψv⟩ := exists_form_of_not_mem hT hv
  obtain ⟨f, hf, -⟩ := hP ψ
  have hfT : f ∈ D.T' := fun t ht => by rw [hf]; exact hψT t ht
  obtain ⟨o, ho⟩ := exists_mul_eq_inv_unif hϖ (u := D.bT v f) (by rw [hf]; exact hψv)
  refine ⟨⟨o • f, D.T'.smul_mem o hfT⟩, ?_⟩
  rw [pairKO_mk]
  congr 1
  show D.bT v (o • f) = _
  rw [map_smul, Algebra.smul_def, ho]

end Main

end GlobalTheory.LocDualInt
end
end

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualLattice_pairing_eq_inv_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), IsLatticeIn D.T → PerfectRight D.bT → ∀ ϖ : O, Irreducible ϖ → ∀ x : VT ⧸ D.T, x ≠ 0 → ∃ f : ↥D.T', pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  atlas_forward_decl GlobalTheory.LocDualInt.exists_dual_pairKO_eq_inv_unif
end

section
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem linK_smul {O : Type} [CommRing O] [IsDomain O] {V : Type} [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    (φ : V →ₗ[O] FractionRing O) (c : FractionRing O) (v : V) : φ (c • v) = c * φ v :=
  (LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O) φ).map_smul c v

theorem exists_pairKO_eq_inv_unif : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), ∀ ϖ : O, Irreducible ϖ → ∀ (n : ℕ) (f : ↥D.T'), f ∉ powSub (M := ↥D.T') ϖ n → ∃ x : VT ⧸ D.T, ϖ ^ n • x = 0 ∧ pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D ϖ hϖ n f hf
  set π : (FractionRing O) := algebraMap O (FractionRing O) ϖ with hπ
  have hπ0 : π ≠ 0 := by
    rw [hπ]; exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero
  have hpn : ∀ y : VT', ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  have hpnT : ∀ y : VT, ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  set f' : VT' := (π ^ n)⁻¹ • (f : VT') with hf'
  have hff' : ϖ ^ n • f' = f := by
    rw [hpn, hf', smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul]
  clear_value f' π
  have hnot : f' ∉ D.T' := by
    intro h
    apply hf
    refine mem_powSub.2 ⟨⟨f', h⟩, ?_⟩
    ext
    simp [hff']
  have hnot' : ¬ ∀ x ∈ D.T, D.bT x f' ∈ (1 : Submodule O (FractionRing O)) := hnot
  push_neg at hnot'
  obtain ⟨v, hvT, hu⟩ := hnot'
  set u := D.bT v f' with hu_def
  have hu0 : u ≠ 0 := by
    intro h; apply hu; rw [h]; exact Submodule.zero_mem _
  have hnotint : ¬ IsLocalization.IsInteger O u := by
    rintro ⟨o, ho⟩; exact hu (Submodule.mem_one.2 ⟨o, ho⟩)
  obtain ⟨w, hw⟩ : IsLocalization.IsInteger O u⁻¹ :=
    (ValuationRing.isInteger_or_isInteger O u).resolve_left hnotint
  have hwnu : w ∉ nonunits O → False := by
    intro h
    rw [mem_nonunits_iff, not_not] at h
    obtain ⟨w', hw'⟩ := h
    apply hnotint
    refine ⟨(w'⁻¹ : Oˣ), ?_⟩
    have : algebraMap O (FractionRing O) (w' : O) * u = 1 := by
      rw [hw', hw, inv_mul_cancel₀ hu0]
    have h2 : algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * algebraMap O (FractionRing O) (w' : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) = algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * (algebraMap O (FractionRing O) (w' : O) * u) := by rw [this, mul_one]
      _ = u := by rw [← mul_assoc, h2, one_mul]
  have hwm : w ∈ IsLocalRing.maximalIdeal O := by
    by_contra h
    exact hwnu h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at hwm
  obtain ⟨o, ho⟩ := hwm
  have hkey : D.bT (o • v) f' = π⁻¹ := by
    rw [D.bT.map_smul o v, LinearMap.smul_apply, Algebra.smul_def, ← hu_def]
    have h1 : algebraMap O (FractionRing O) o * π = u⁻¹ := by rw [hπ, ← map_mul, ho, hw]
    have : algebraMap O (FractionRing O) o = u⁻¹ * π⁻¹ := by
      rw [← h1, mul_assoc, mul_inv_cancel₀ hπ0, mul_one]
    rw [this, mul_comm u⁻¹, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  refine ⟨Submodule.Quotient.mk ((π ^ n)⁻¹ • (o • v)), ?_, ?_⟩
  · rw [← Submodule.Quotient.mk_smul, hpnT, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul,
      Submodule.Quotient.mk_eq_zero]
    exact D.T.smul_mem o hvT
  · rw [pairKO_mk, ← hkey]
    congr 1
    have e1 : D.bT ((π ^ n)⁻¹ • (o • v)) f = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT.flip (f : VT')) ((π ^ n)⁻¹) (o • v)
    have e2 : D.bT (o • v) ((π ^ n)⁻¹ • (f : VT')) = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT (o • v)) ((π ^ n)⁻¹) (f : VT')
    rw [e1, hf', e2]

end GlobalTheory.LocDualInt
end
end

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_pairing_eq_inv_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), ∀ ϖ : O, Irreducible ϖ → ∀ (n : ℕ) (f : ↥D.T'), f ∉ powSub (M := ↥D.T') ϖ n → ∃ x : VT ⧸ D.T, ϖ ^ n • x = 0 ∧ pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  atlas_forward_decl GlobalTheory.LocDualInt.exists_pairKO_eq_inv_unif
end

section
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualFin

theorem ko_torsion : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ), (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ a : KO O, ∃ r : ℕ, (p : O) ^ r • a = 0 := by
  intro O _ _ _ p hp a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨o, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) hϖ
  obtain ⟨t, ht⟩ : ϖ ∣ (p : O) := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq ▸ hp)
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hπ : algebraMap O (FractionRing O) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hu0 : algebraMap O (FractionRing O) (u : O) ≠ 0 := (map_ne_zero_iff _ hinj).2 u.ne_zero
  refine ⟨m, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨o * t ^ m * ((u⁻¹ : Oˣ) : O), ?_⟩
  rw [Algebra.smul_def, hu, ht]
  simp only [map_mul, map_pow]
  have hui : algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = (algebraMap O (FractionRing O) (u : O))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [hui]
  field_simp
  ring

open GlobalTheory.TateFin GlobalTheory.TateTop GlobalTheory.Cyc.TwistLift ReciprocityTheory.Neutral.Bridge in

theorem exists_cocycle_cup_not_cob : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G], FiniteDimensional ℚ_[p] K → IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (D : LatData O G VT VT'), (∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧ ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → IsLatticeIn D.T → PerfectRight D.bT → ContAction D.ρT → IsOpen (D.T : Set VT) → T2Space VT → T2Space VT' → ContinuousConstSMul (FractionRing O) VT → ContinuousConstSMul (FractionRing O) VT' → ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Z1 D.ρA, c ∉ B1 D.ρA → ∀ r : ℕ, (∀ g, ϖ ^ r • c g = 0) → ∀ n : ℕ, r ≤ n → ∃ z ∈ Z1 (quotRep D.ρTl' ϖ n), cupMod D c ϖ n z ∉ B2 (twist D.ε (KO O)) := by
  intro hTate p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hOr hOc hOt hOa hpm hp0
    hemb i D hcyc hlat hperf hcontT hTo hT2 hT2' hcs hcs' ϖ hϖ c hc hcB r hr n hrn
  by_contra H
  push_neg at H
  apply hcB
  haveI : CompactSpace G := i.toHomeomorph.symm.compactSpace
  haveI : ContinuousMul G := ⟨by
    have h := i.symm.continuous.comp
      ((i.continuous.comp continuous_fst).mul (i.continuous.comp continuous_snd))
    refine h.congr fun q => ?_
    show i.symm (i q.1 * i q.2) = q.1 * q.2
    rw [← map_mul, ContinuousMulEquiv.symm_apply_apply]⟩
  let χ : G →* ℤ_[p]ˣ := ((cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p))).comp (i : G →* Formalism.GaloisCohomology.GK p K)
  have hχ : Continuous fun g => (χ g : ℤ_[p]) :=
    Units.continuous_val.comp ((cyclotomicCharacter.continuous p K (PadicAlgCl p)).comp i.continuous)
  have hT' : ∀ (k : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (p ^ (k + 1))) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (p ^ (k + 1))) G M)
      (hrho : ContAction rho), DualityFor (redChar χ (k + 1)) rho hrho := by
    intro k M _ _ _ _ _ rho hrho
    refine DualityFor.of_comp i.symm _ hrho ?_
    have h1 : (redChar χ (k + 1)).comp (i.symm : Formalism.GaloisCohomology.GK p K →* G) = Formalism.GaloisCohomology.cycK p K (k + 1) :=
      MonoidHom.ext fun g => congrArg (Formalism.GaloisCohomology.cycK p K (k + 1)) (i.apply_symm_apply g)
    rw [h1]
    exact hTate p K hK (k + 1) M _ (Nat.succ_pos _) (contAction_comp i.symm hrho)
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_padicInt_ringHom_congr_toZModPow hOr hOc hOt hOa hpm
  have hspan : Ideal.span {(p : O)} ≠ ⊤ := fun h =>
    (IsLocalRing.mem_maximalIdeal _).1 hpm (Ideal.span_singleton_eq_top.1 h)
  have hkrull : ∀ a b : O, (∀ k : ℕ, a - b ∈ Ideal.span {(p : O) ^ k}) → a = b := by
    intro a b h
    have h0 := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {(p : O)}) hspan
    have h1 : a - b ∈ ⨅ k, Ideal.span {(p : O)} ^ k :=
      Ideal.mem_iInf.2 fun k => by rw [Ideal.span_singleton_pow]; exact h k
    rw [h0, Ideal.mem_bot, sub_eq_zero] at h1
    exact h1
  have hιε : ∀ g, ι (χ g : ℤ_[p]) = (D.ε g : O) := by
    intro g
    refine hkrull _ _ fun k => ?_
    obtain ⟨ζ, hζ, hζa⟩ := GlobalTheory.T.cyclotomicCharacter_congr_root_of_unity_pow K (i g) k
    obtain ⟨a, ha, hεa⟩ := hcyc g k ζ hζ
    have e1 : (a : ZMod (p ^ k)) = PadicInt.toZModPow k (χ g : ℤ_[p]) := hζa a ha
    have e2 := hι (χ g : ℤ_[p]) k
    rw [← e1, ZMod.val_natCast] at e2
    have e3 : ((a : ℕ) : O) - ((a % p ^ k : ℕ) : O) ∈ Ideal.span {(p : O) ^ k} := by
      have h : ((a : ℕ) : O) = ((a / p ^ k : ℕ) : O) * (p : O) ^ k + ((a % p ^ k : ℕ) : O) := by
        have h' := congrArg (Nat.cast : ℕ → O) (Nat.div_add_mod' a (p ^ k)).symm
        push_cast at h'
        exact h'
      exact Ideal.mem_span_singleton'.2 ⟨((a / p ^ k : ℕ) : O), by rw [h]; ring⟩
    have e4 : ι (χ g : ℤ_[p]) - (D.ε g : O) = (ι (χ g : ℤ_[p]) - ((a % p ^ k : ℕ) : O)) -
        (((a : ℕ) : O) - ((a % p ^ k : ℕ) : O)) - ((D.ε g : O) - (a : O)) := by ring
    rw [e4]
    exact sub_mem (sub_mem e2 e3) hεa
  letI : Module ℤ_[p] (KO O) := Module.compHom (KO O) ι
  have hsmul : ∀ (u : ℤ_[p]) (y : KO O), u • y = ι u • y := fun _ _ => rfl
  have htor : ∀ a : KO O, ∃ r : ℕ, (p : ℤ_[p]) ^ r • a = 0 := fun a => by
    obtain ⟨r, hr⟩ := ko_torsion p hpm a
    exact ⟨r, by rw [hsmul, map_pow, map_natCast]; exact hr⟩
  have hKOd : DiscreteTopology (KO O) :=
    QuotientAddGroup.discreteTopology (N := (1 : Submodule O (FractionRing O)).toAddSubgroup) (by
      have : ((1 : Submodule O (FractionRing O)).toAddSubgroup : Set (FractionRing O)) =
          Set.range (algebraMap O (FractionRing O)) := by
        ext x; simp [Submodule.mem_one, eq_comm]
      rw [this]; exact hemb.isOpen_range)
  have hVd : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hTo
  have hclc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hc.1
  set X := LinearMap.ker (LinearMap.lsmul O (VT ⧸ D.T) (ϖ ^ n)) with hXdef
  have memX : ∀ x : VT ⧸ D.T, x ∈ X ↔ ϖ ^ n • x = 0 := fun x => by
    rw [hXdef, LinearMap.mem_ker, LinearMap.lsmul_apply]
  haveI : Finite X := GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient D.T hOr hOc hOa hlat ϖ hϖ n
  obtain ⟨hcT', hopen, -⟩ := GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis D hOc hemb hlat hperf hT2' ϖ hϖ
  haveI : CompactSpace ↥D.T' := hcT'
  haveI : Finite (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    AddSubgroup.quotient_finite_of_isOpen (powSub (M := ↥D.T') ϖ n).toAddSubgroup (hopen n)
  haveI hNd : DiscreteTopology (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    QuotientAddGroup.discreteTopology (N := (powSub (M := ↥D.T') ϖ n).toAddSubgroup) (hopen n)
  obtain ⟨t, ht⟩ : ϖ ∣ (p : O) := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq ▸ hpm)
  have hpow : ∀ {M : Type} [AddCommGroup M] [Module O M] (y : M), p ^ n • y = t ^ n • ϖ ^ n • y :=
    fun y => by rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ht, mul_pow, mul_comm, mul_smul]
  have hX : ∀ x : X, p ^ n • x = 0 := fun x => Subtype.ext (by
    rw [AddSubmonoidClass.coe_nsmul, hpow, (memX _).1 x.2, smul_zero]; rfl)
  have hN : ∀ y : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ n, p ^ n • y = 0 := fun y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hpow, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_comm]
    exact smul_mem_powSub ϖ n _
  let a : G → X → X := fun g x => ⟨D.ρA g x, by rw [memX, ← map_smul, (memX _).1 x.2, map_zero]⟩
  let a' : G → (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    fun g => (quotRep D.ρTl' ϖ n g).toAddMonoidHom
  have h1 : ∀ y, a' 1 y = y := fun y => by
    show quotRep D.ρTl' ϖ n 1 y = y
    rw [map_one]; rfl
  have hm : ∀ g h y, a' (g * h) y = a' g (a' h y) := fun g h y => by
    show quotRep D.ρTl' ϖ n (g * h) y = quotRep D.ρTl' ϖ n g (quotRep D.ρTl' ϖ n h y)
    rw [map_mul]; rfl
  have hlc : ∀ y, IsLocallyConstant fun g => a' g y := fun y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [IsLocallyConstant.iff_continuous]
    show Continuous fun g => (Submodule.Quotient.mk (D.ρTl' g t0) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ n)
    exact continuous_quot_mk.comp ((sub_contAction D.contT' D.T' D.stT').comp
      (continuous_id.prodMk continuous_const))
  let βf : X → (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ KO O := fun x =>
    ((powSub (M := ↥D.T') ϖ n).liftQ (pairKO D.bT D.T (x : VT ⧸ D.T)) (fun t0 ht0 => by
      rw [LinearMap.mem_ker]; exact pairKO_eq_zero_of_mem D ((memX _).1 x.2) ht0)).toAddMonoidHom
  let β : X →+ (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ KO O := AddMonoidHom.mk' βf (fun x x' => by
    ext y
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show pairKO D.bT D.T ((x + x' : X) : VT ⧸ D.T) t0 =
      pairKO D.bT D.T (x : VT ⧸ D.T) t0 + pairKO D.bT D.T (x' : VT ⧸ D.T) t0
    rw [Submodule.coe_add, map_add, LinearMap.add_apply])
  have he : ∀ g x y, β (a g x) (a' g y) = (χ g : ℤ_[p]) • β x y := fun g x y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show pairKO D.bT D.T (D.ρA g x) (D.ρTl' g t0) = ι (χ g : ℤ_[p]) • pairKO D.bT D.T (x : VT ⧸ D.T) t0
    rw [D.pairKO_equiv, twist_apply, hιε]
  have hs : toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) ≠ 0 := by
    intro h0
    rw [toKO, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at h0
    obtain ⟨o, ho⟩ := h0
    apply hϖ.not_isUnit
    have hinj := IsFractionRing.injective O (FractionRing O)
    have hπ : algebraMap O (FractionRing O) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    refine IsUnit.of_mul_eq_one (b := o) (hinj ?_)
    rw [map_mul, ho, map_one, mul_inv_cancel₀ hπ]
  have hβ1 : ∀ x : X, x ≠ 0 → ∃ y, β x y = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
    intro x hx
    obtain ⟨f, hf⟩ := GlobalTheory.T.exists_dualLattice_pairing_eq_inv_uniformizer D hlat hperf ϖ hϖ (x : VT ⧸ D.T) (fun h => hx (Subtype.ext h))
    exact ⟨Submodule.Quotient.mk f, hf⟩
  have hβ2 : ∀ y, y ≠ 0 → ∃ x : X, β x y = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
    intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hf : f ∉ powSub (M := ↥D.T') ϖ n := fun h => hy ((Submodule.Quotient.mk_eq_zero _).2 h)
    obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.exists_torsion_pairing_eq_inv_uniformizer D ϖ hϖ n f hf
    exact ⟨⟨x, (memX x).2 hx1⟩, hx2⟩
  have hcX : ∀ g, c g ∈ X := fun g => (memX _).2 (by
    rw [← Nat.sub_add_cancel hrn, pow_add, mul_smul, hr, smul_zero])
  let c₀ : G → X := fun g => ⟨c g, hcX g⟩
  obtain ⟨x, hx⟩ := (nondeg_torsion hχ hT' htor hX hN a a' h1 hm hlc β he hs hβ1 hβ2).1 c₀
    (IsLocallyConstant.desc _ Subtype.val hclc Subtype.val_injective)
    (fun g h => Subtype.ext (hc.2 g h)) (by
      intro c' hc'l hc'c
      obtain ⟨b, hbc, hbe⟩ := (separated_dvr_second_cohomology_mem _ _).1 (H c' ⟨hc'l.continuous, fun g h => hc'c g h⟩)
      refine ⟨b, (IsLocallyConstant.iff_continuous b).2 hbc, fun q => ?_⟩
      obtain ⟨g, h⟩ := q
      have e := congrFun hbe (g, h)
      have e2 : β (c₀ g) (a' g (c' h)) = cupMod D c ϖ n c' (g, h) := by
        conv_lhs => rw [← mk_qlift (c' h)]
        rfl
      rw [e2, ← e]
      show _ = ι (χ g : ℤ_[p]) • b h - b (g * h) + b g
      rw [hιε]
      rfl)
  exact (mem_coboundaries1 _ _).2 ⟨x, fun g => congrArg Subtype.val (hx g)⟩

end GlobalTheory.LocDualFin
end
end

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_cup_not_coboundary_finiteLevel : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G], FiniteDimensional ℚ_[p] K → IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (D : LatData O G VT VT'), (∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧ ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → IsLatticeIn D.T → PerfectRight D.bT → ContAction D.ρT → IsOpen (D.T : Set VT) → T2Space VT → T2Space VT' → ContinuousConstSMul (FractionRing O) VT → ContinuousConstSMul (FractionRing O) VT' → ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Z1 D.ρA, c ∉ B1 D.ρA → ∀ r : ℕ, (∀ g, ϖ ^ r • c g = 0) → ∀ n : ℕ, r ≤ n → ∃ z ∈ Z1 (quotRep D.ρTl' ϖ n), cupMod D c ϖ n z ∉ B2 (twist D.ε (KO O)) := by
  atlas_forward_decl GlobalTheory.LocDualFin.exists_cocycle_cup_not_cob
end

section
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem int_iso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : ReciprocityTheory.ChartRestriction.T2.IntIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO hF i D hD hinv x hx
  haveI := hD.t2'
  haveI : IsGalois K (PadicAlgCl p) := inferInstance
  haveI : CompactSpace (Formalism.GaloisCohomology.GK p K) := inferInstance
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  induction x using Submodule.Quotient.induction_on with
  | H c => ?_
  by_contra hx0
  have hcB : (c : G → VT ⧸ D.T) ∉ B1 D.ρA := fun h => hx0 ((Submodule.Quotient.mk_eq_zero _).2 h)
  obtain ⟨r, hr⟩ := GlobalTheory.T.continuous_quotient_torsion_bounded D.T hD.lat hD.openT ϖ hϖ (c : G → VT ⧸ D.T) c.2.1
  have hcyc : ∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧
      ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n} := by
    intro g n ζ hζ
    obtain ⟨a, h1, h2⟩ := hD.cyc (i g) n ζ hζ
    have e : (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) (i g) = D.ε g := by
      change D.ε (i.symm (i g)) = D.ε g
      exact congrArg D.ε (i.symm_apply_apply g)
    rw [e] at h2
    exact ⟨a, h1, h2⟩
  obtain ⟨hcpt, hopen, hbasis⟩ := GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis D hO.compact hF.emb hD.lat hD.perf hD.t2' ϖ hϖ
  haveI := hcpt
  let X : ℕ → Type := fun k => G → ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k)
  let Y : ∀ k, Set (X k) := fun k => {z | z ∈ Z1 (quotRep D.ρTl' ϖ (r + k)) ∧
    cupMod D (c : G → VT ⧸ D.T) ϖ (r + k) z ∉ B2 (twist D.ε (KO O))}
  have hle : ∀ k, r + k ≤ r + (k + 1) := fun k => by omega
  let f : ∀ k, X (k + 1) → X k := fun k z g =>
    Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (z g)
  have hfin : ∀ k, (Y k).Finite := fun k =>
    (GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen hT hK hO.p_mem i D.ρTl' (sub_contAction D.contT' _ D.stT') ϖ hϖ hopen (r + k)).subset
      (fun z hz => hz.1)
  have hne : ∀ k, (Y k).Nonempty := fun k => by
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.exists_cocycle_cup_not_coboundary_finiteLevel hT hK hO.ring hO.compact hO.t2 hO.adic hO.p_mem hO.p_ne hF.emb i D
      hcyc hD.lat hD.perf hD.contT hD.openT hD.t2 hD.t2' hD.cs hD.cs' ϖ hϖ c.1 c.2 hcB r hr (r + k)
      (by omega)
    exact ⟨z, hz, hz'⟩
  have hmap : ∀ k, ∀ z ∈ Y (k + 1), f k z ∈ Y k := by
    rintro k z ⟨hz, hnc⟩
    refine ⟨factor_mem_cocycles_pow_quot D.ρTl' ϖ (hle k) hz, ?_⟩
    have e := cupMod_factor D hr (Nat.le_add_right r k) (hle k) z
    show cupMod D (c : G → VT ⧸ D.T) ϖ (r + k)
      (fun g => Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (z g)) ∉ _
    rw [e]
    exact hnc
  obtain ⟨s, hs⟩ := GlobalTheory.exists_compatible_seq_of_finite_nonempty X f Y hfin hne hmap
  let w : ℕ → G → ↥D.T' := fun k g => qlift (s k g)
  have hwZ : ∀ k, (fun g => (Submodule.Quotient.mk (w k g) :
      ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k))) ∈ Z1 (quotRep D.ρTl' ϖ (r + k)) := by
    intro k
    have e : (fun g => (Submodule.Quotient.mk (w k g) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k))) =
        s k := funext fun g => mk_qlift _
    rw [e]
    exact (hs k).1.1
  have hstep : ∀ k g, w (k + 1) g - w k g ∈ powSub (M := ↥D.T') ϖ (r + k) := by
    intro k g
    apply (Submodule.Quotient.eq _).1
    have e1 : (Submodule.Quotient.mk (w (k + 1) g) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k)) =
        f k (s (k + 1)) g := by
      show _ = Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (s (k + 1) g)
      conv_rhs => rw [← mk_qlift (s (k + 1) g)]
      rfl
    rw [e1, (hs k).2]
    exact (mk_qlift (s k g)).symm
  obtain ⟨e, he, hew⟩ := GlobalTheory.T.exists_continuous_cocycle_lift_of_compatible' D.ρTl' ϖ r hopen hbasis w hwZ hstep
  have h1 := hx (Submodule.Quotient.mk ⟨e, he⟩)
  have h2 : ((cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩) : G × G → KO O) ∈ B2 (twist D.ε (KO O)) := by
    have h3 : D.inv (Submodule.Quotient.mk (cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩)) = D.inv 0 := by
      rw [map_zero]
      exact h1
    have h6 := (Submodule.Quotient.mk_eq_zero _).1 (hinv h3)
    exact h6
  apply (hs 0).1.2
  have h4 : cupMod D (c : G → VT ⧸ D.T) ϖ (r + 0) (s 0) = ((cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩) : G × G → KO O) := by
    funext q
    refine pairKO_eq_of_sub_mem D (hr q.1) ?_
    rw [← map_sub]
    refine powSub_stable _ ϖ r q.1 _ ?_
    have h5 := hew 0 q.2
    rw [← neg_sub]
    exact Submodule.neg_mem _ h5
  rw [h4]
  exact h2

end GlobalTheory.LocDualInt
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_localDuality_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.IntIso := by
  atlas_forward_decl GlobalTheory.LocDualInt.int_iso_of_localTateDuality
end

section
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2

noncomputable section

namespace GlobalTheory.RatDuality

section Swap

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
  {M M' P : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M'] [AddCommGroup P] [Module R P]
  [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]

theorem cupH11_add_flip (rho : Representation R G M) (rho' : Representation R G M')
    (rhoP : Representation R G P) (b : M →ₗ[R] M' →ₗ[R] P)
    (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (hb' : Continuous fun p : M' × M => b.flip p.1 p.2)
    (hbe' : ∀ g y x, b.flip (rho' g y) (rho g x) = rhoP g (b.flip y x))
    (hrho : ContAction rho) (hrho' : ContAction rho') (x : H1 rho) (y : H1 rho') :
    cupProductH1H1 rho rho' rhoP b hb hbe hrho' x y + cupProductH1H1 rho' rho rhoP b.flip hb' hbe' hrho y x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  induction y using Submodule.Quotient.induction_on with
  | H y =>
  show (Submodule.Quotient.mk (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hrho' x y) : H2 rhoP) +
    Submodule.Quotient.mk (cupCocycleZ1Z1 rho' rho rhoP b.flip hb' hbe' hrho y x) = 0
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -b (x.1 g) (y.1 g), (hb.comp (x.2.1.prodMk y.2.1)).neg, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  simp only [d1_apply, Submodule.coe_subtype, Submodule.coe_add, Pi.add_apply, cupCocycleZ1Z1_apply,
    LinearMap.flip_apply, map_neg, ← hbe, x.2.2 g h, y.2.2 g h, map_add, LinearMap.add_apply]
  abel

theorem cup_H1_flip_eq_zero (rho : Representation R G M) (rho' : Representation R G M')
    (rhoP : Representation R G P) (b : M →ₗ[R] M' →ₗ[R] P)
    (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (hb' : Continuous fun p : M' × M => b.flip p.1 p.2)
    (hbe' : ∀ g y x, b.flip (rho' g y) (rho g x) = rhoP g (b.flip y x))
    (hrho : ContAction rho) (hrho' : ContAction rho') (x : H1 rho) (y : H1 rho')
    (h : cupProductH1H1 rho rho' rhoP b hb hbe hrho' x y = 0) :
    cupProductH1H1 rho' rho rhoP b.flip hb' hbe' hrho y x = 0 := by
  have e := cupH11_add_flip rho rho' rhoP b hb hbe hb' hbe' hrho hrho' x y
  rwa [h, zero_add] at e

end Swap

theorem smul_inv_smul_frac {O : Type*} [CommRing O] [IsDomain O] {X : Type*} [AddCommGroup X]
    [Module O X] [Module (FractionRing O) X] [IsScalarTower O (FractionRing O) X] {c : O}
    (hc : c ≠ 0) (y : X) : c • ((algebraMap O (FractionRing O) c)⁻¹ • y) = y := by
  have h0 : algebraMap O (FractionRing O) c ≠ 0 := fun h =>
    hc (IsFractionRing.injective O (FractionRing O) (by simpa using h))
  rw [← algebraMap_smul (FractionRing O) c, smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem exists_smul_eq_H1_of_ne_zero {O : Type} [CommRing O] [IsDomain O] {G : Type} [Group G]
    [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul O V] [ContinuousConstSMul (FractionRing O) V]
    (ρ : Representation O G V) {c : O} (hc : c ≠ 0) (x : H1 ρ) : ∃ y, c • y = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
  have hcomm : ∀ g v, (algebraMap O (FractionRing O) c)⁻¹ • ρ g v =
      ρ g ((algebraMap O (FractionRing O) c)⁻¹ • v) := fun g v =>
    ((IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) V V).map_smul
      (ρ g) _ v).symm
  let z' : Z1 ρ := ⟨fun g => (algebraMap O (FractionRing O) c)⁻¹ • z.1 g, z.2.1.const_smul _,
    fun g h => by
      show (algebraMap O (FractionRing O) c)⁻¹ • z.1 (g * h) =
        (algebraMap O (FractionRing O) c)⁻¹ • z.1 g + ρ g ((algebraMap O (FractionRing O) c)⁻¹ • z.1 h)
      rw [z.2.2 g h, smul_add, hcomm]⟩
  refine ⟨Submodule.Quotient.mk z', ?_⟩
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  funext g
  exact smul_inv_smul_frac hc (z.1 g)

section Lat

variable {O G VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT']

theorem mem_range_j'_of_map_eq_zero (D : LatData O G VT VT') (y : H1 D.ρT')
    (hy : mapH1 D.ρT' D.ρA' D.T'.mkQ (Submodule.continuous_mkQ _) (fun _ _ => rfl) y = 0) :
    y ∈ LinearMap.range D.j' := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
  have h1 : (Submodule.Quotient.mk
      (cocycles1MapOfEquivariant D.ρT' D.ρA' D.T'.mkQ (Submodule.continuous_mkQ _) (fun _ _ => rfl) z) : H1 D.ρA') = 0 := hy
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨mb, hm⟩ := (mem_coboundaries1 _ _).1 h1
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ mb
  have hmem : ∀ g, z.1 g - (D.ρT' g m - m) ∈ D.T' := fun g => by
    have e : (Submodule.Quotient.mk (z.1 g) : VT' ⧸ D.T') =
        Submodule.Quotient.mk (D.ρT' g m - m) := hm g
    exact (Submodule.Quotient.eq _).1 e
  have hcont : Continuous fun g => z.1 g - (D.ρT' g m - m) :=
    z.2.1.sub ((D.contT'.comp (continuous_id.prodMk continuous_const)).sub continuous_const)
  let t : Z1 D.ρTl' := ⟨fun g => ⟨_, hmem g⟩, hcont.subtype_mk _, fun g h => by
    apply Subtype.ext
    show z.1 (g * h) - (D.ρT' (g * h) m - m) =
      (z.1 g - (D.ρT' g m - m)) + D.ρT' g (z.1 h - (D.ρT' h m - m))
    rw [z.2.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel⟩
  refine ⟨Submodule.Quotient.mk t, ?_⟩
  show (Submodule.Quotient.mk
    (cocycles1MapOfEquivariant D.ρTl' D.ρT' D.T'.subtype continuous_subtype_val (fun _ _ => rfl) t) : H1 D.ρT') =
      Submodule.Quotient.mk z
  rw [Submodule.Quotient.eq]
  refine (mem_coboundaries1 _ _).2 ⟨-m, fun g => ?_⟩
  show (z.1 g - (D.ρT' g m - m)) - z.1 g = D.ρT' g (-m) - -m
  rw [map_neg]
  abel

def swapLat (D : LatData O G VT VT') (hc : ContAction D.ρT)
    (inv' : H2 (twist D.ε (Formalism.NG.KO O)) →ₗ[O] Formalism.NG.KO O) : LatData O G VT' VT where
  ε := D.ε
  ρT := D.ρT'
  ρT' := D.ρT
  bT := D.bT.flip
  T := D.T'
  stT := D.stT'
  eqT := fun g x f => D.eqT g f x
  contT' := hc
  contbT := D.contbT.comp continuous_swap
  inv := inv'
  invF := D.invF

theorem pr_swapLat_q (D : LatData O G VT VT') (hc : ContAction D.ρT)
    (inv' : H2 (twist D.ε (Formalism.NG.KO O)) →ₗ[O] Formalism.NG.KO O) (y : H1 D.ρT')
    (t : H1 (swapLat D hc inv').ρTl') :
    (swapLat D hc inv').pr ((swapLat D hc inv').q y) t =
      inv' (mapH2 (twist D.ε (FractionRing O)) (twist D.ε (Formalism.NG.KO O)) (toKO O) toKO_cont
        (toKO_equiv D.ε) (cupProductH1H1 D.ρT' D.ρT (twist D.ε (FractionRing O)) D.bT.flip
          (D.contbT.comp continuous_swap) (fun g x f => D.eqT g f x) hc y
          ((swapLat D hc inv').j' t))) := by
  induction y using Submodule.Quotient.induction_on with
  | H y =>
  induction t using Submodule.Quotient.induction_on with
  | H t => rfl

end Lat

theorem perfectRight_flip {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V']
    [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) (hT : IsLatticeIn T)
    (hb : PerfectRight b) : PerfectRight b.flip := by
  classical
  obtain ⟨⟨s, hs⟩, hspan⟩ := hT
  haveI : FiniteDimensional (FractionRing O) V := ⟨⟨s, by
    rw [← Submodule.span_span_of_tower O (FractionRing O) (s : Set V), hs, hspan]⟩⟩
  let e : V' →ₗ[FractionRing O] Module.Dual (FractionRing O) V := (fracBilinear b).flip
  have he : ∀ f x, e f x = b x f := fun _ _ => rfl
  have hsurj : Function.Surjective e := fun ψ => by
    obtain ⟨f, hf, -⟩ := hb ψ
    exact ⟨f, LinearMap.ext fun x => (he f x).trans (hf x)⟩
  have hinj : Function.Injective e := fun f₁ f₂ h => by
    obtain ⟨f, -, hu⟩ := hb (e f₁)
    have h1 := hu f₁ (fun x => (he f₁ x).symm)
    have h2 := hu f₂ (fun x => by rw [← he, ← h])
    exact h1.trans h2.symm
  let E := LinearEquiv.ofBijective e ⟨hinj, hsurj⟩
  intro φ
  let x := (Module.evalEquiv (FractionRing O) V).symm (φ ∘ₗ E.symm.toLinearMap)
  have hx : ∀ ψ : Module.Dual (FractionRing O) V, ψ x = φ (E.symm ψ) := fun ψ => by
    have := LinearMap.congr_fun
      ((Module.evalEquiv (FractionRing O) V).apply_symm_apply (φ ∘ₗ E.symm.toLinearMap)) ψ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.comp_apply] at this
    exact this
  refine ⟨x, fun f => ?_, fun x' hx' => ?_⟩
  · rw [LinearMap.flip_apply, ← he, hx]
    congr 1
    exact E.symm_apply_apply f
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (FractionRing O)]
    intro ψ
    obtain ⟨f, rfl⟩ := hsurj ψ
    rw [map_sub, he, he, sub_eq_zero]
    have h1 := hx' f
    rw [LinearMap.flip_apply] at h1
    rw [h1, ← he, hx]
    congr 1
    exact (E.symm_apply_apply f).symm

theorem frac_smul_eq_zero {O : Type*} [CommRing O] [IsDomain O] {c : O} (hc : c ≠ 0)
    {x : FractionRing O} (h : c • x = 0) : x = 0 := by
  have h0 : algebraMap O (FractionRing O) c ≠ 0 := fun h' =>
    hc (IsFractionRing.injective O (FractionRing O) (by simpa using h'))
  rw [Algebra.smul_def] at h
  exact (mul_eq_zero.1 h).resolve_left h0

theorem exists_eq_of_nondeg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {A W : Type} [AddCommGroup A] [Module O A] [AddCommGroup W] [Module O W]
    (Φ : A →ₗ[O] W →ₗ[O] FractionRing O) (hA : ∀ c : O, c ≠ 0 → ∀ a : A, ∃ a', c • a' = a)
    (M : Submodule O W) (hM : M.FG) (hW : ∀ w : W, ∃ c : O, c ≠ 0 ∧ c • w ∈ M)
    (hnd : ∀ w, (∀ a, Φ a w = 0) → w = 0) (f : W →ₗ[O] FractionRing O) :
    ∃ a, ∀ w, Φ a w = f w := by
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.2 hM
  haveI : Module.IsTorsionFree O M := ⟨fun r hr m₁ m₂ h => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h' : r • m₁ = r • m₂ := h
    have hw : ((m₁ - m₂ : M) : W) = 0 := hnd _ fun a => by
      have e : r • Φ a ((m₁ - m₂ : M) : W) = 0 := by
        rw [← map_smul, ← Submodule.coe_smul, smul_sub, h', sub_self, Submodule.coe_zero, map_zero]
      exact frac_smul_eq_zero hr0 e
    exact sub_eq_zero.1 (Subtype.ext hw)⟩
  obtain ⟨n, e⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := M)
  let Ψ : A →ₗ[O] (Fin n → FractionRing O) := LinearMap.pi fun i => Φ.flip (e i : W)
  have hΨ : ∀ a i, Ψ a i = Φ a (e i : W) := fun _ _ => rfl

  let S : Submodule (FractionRing O) (Fin n → FractionRing O) :=
    { carrier := Set.range Ψ
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, map_add Ψ a b⟩
      zero_mem' := ⟨0, map_zero Ψ⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        obtain ⟨⟨u, v⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
        obtain ⟨a', ha'⟩ := hA v (nonZeroDivisors.coe_ne_zero v) a
        refine ⟨u • a', ?_⟩
        rw [← ha', map_smul, map_smul, ← algebraMap_smul (FractionRing O) (v : O) (Ψ a'),
          smul_smul, IsLocalization.mk'_spec, algebraMap_smul] }
  have hS : S = ⊤ := by
    by_contra hne
    obtain ⟨lam, hlam0, hle⟩ := Submodule.exists_le_ker_of_lt_top S (lt_top_iff_ne_top.2 hne)
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) (Finset.univ : Finset (Fin n))
      (fun i => lam (fun j => if i = j then 1 else 0))
    choose μ hμ using fun i => hd i (Finset.mem_univ i)
    let w : M := ∑ i, μ i • e i
    have hw0 : (w : W) = 0 := hnd _ fun a => by
      have hker : lam (Ψ a) = 0 := hle ⟨a, rfl⟩
      rw [LinearMap.pi_apply_eq_sum_univ] at hker
      have : Φ a (w : W) = (d : O) • ∑ i, Ψ a i • lam (fun j => if i = j then 1 else 0) := by
        simp only [w, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hΨ, smul_comm, smul_eq_mul, ← hμ i, Algebra.smul_def, mul_comm]
      rw [this, hker, smul_zero]
    have hμ0 : ∀ i, μ i = 0 := by
      have hw : w = 0 := Subtype.ext hw0
      have := (Fintype.linearIndependent_iff.1 e.linearIndependent) μ hw
      exact this
    apply hlam0
    refine LinearMap.pi_ext fun i x => ?_
    have hi : lam (fun j => if i = j then 1 else 0) = 0 := by
      have h1 := hμ i
      rw [hμ0 i, map_zero] at h1
      exact frac_smul_eq_zero (nonZeroDivisors.coe_ne_zero d) h1.symm
    have : (Pi.single i x : Fin n → FractionRing O) = x • (fun j => if i = j then 1 else 0) := by
      funext j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Pi.single_apply, Ne.symm h]
    rw [this, map_smul, hi, smul_zero, LinearMap.zero_apply]
  obtain ⟨a, ha⟩ : (fun i => f (e i : W)) ∈ S := hS ▸ Submodule.mem_top
  refine ⟨a, fun w => ?_⟩
  have hM' : (Φ a).comp M.subtype = f.comp M.subtype :=
    e.ext fun i => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      exact congrFun ha i
  obtain ⟨c, hc, hcw⟩ := hW w
  have h1 := LinearMap.congr_fun hM' ⟨c • w, hcw⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_smul] at h1
  have h2 : c • (Φ a w - f w) = 0 := by rw [smul_sub, h1, sub_self]
  exact sub_eq_zero.1 (frac_smul_eq_zero hc h2)

end GlobalTheory.RatDuality

namespace GlobalTheory

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 RatDuality

theorem ratIso_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.RatIso := by
  intro hLTD p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO hF i D hD hinj f
  haveI := hD.cs
  haveI := hD.cs'
  obtain ⟨inv', -, -⟩ := GlobalTheory.T.invIso_of_localTateDuality hLTD hK hO hF i hD.cyc
  have hlat' : IsLatticeIn D.T' := by
    refine ⟨Module.Finite.iff_fg.1 (GlobalTheory.dualLat_finite_free D.bT D.T hD.lat hD.perf).1, ?_⟩
    rw [eq_top_iff]
    intro f _
    obtain ⟨c, hc0, hcf⟩ := GlobalTheory.ContCocycleDualLattice.exists_smul_mem_dualLat D hD.lat.1 f
    rw [← inv_smul_smul_frac hc0 f]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hcf)
  have hD' : RealLatG i (swapLat D hD.contT inv'.toLinearMap) :=
    { cyc := hD.cyc
      lat := hlat'
      perf := perfectRight_flip D.bT D.T hD.lat hD.perf
      contT := D.contT'
      openT := GlobalTheory.ContCocycleDualLattice.isOpen_dualLat D hF.emb.isOpen_range hD.lat.1
      t2 := hD.t2'
      t2' := hD.t2
      cs := hD.cs'
      cs' := hD.cs }

  have hq : ∀ z : H1 D.ρT', (∀ a, cupFG D a z = 0) →
      (swapLat D hD.contT inv'.toLinearMap).q z = 0 := fun z hz =>
    GlobalTheory.T.integral_localDuality_of_localTateDuality hLTD hK hO hF i hD' inv'.injective _ fun t => by
      rw [pr_swapLat_q, cup_H1_flip_eq_zero D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT
        D.eqT (D.contbT.comp continuous_swap) (fun g x f => D.eqT g f x) hD.contT D.contT'
        ((swapLat D hD.contT inv'.toLinearMap).j' t) z (hz _), map_zero, map_zero]
  haveI : Module.Finite O (H1 D.ρTl') := GlobalTheory.T.finIso_dualLattice_of_localTateDuality hLTD hK hO i hD
  have hnd : ∀ y : H1 D.ρT', (∀ a, D.invF (cupFG D a y) = 0) → y = 0 := by
    intro y hy
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hπ0 : π ≠ 0 := hπ.ne_zero
    have hmem : ∀ n : ℕ, ∃ yn ∈ LinearMap.range D.j', π ^ n • yn = y := fun n => by
      obtain ⟨yn, hyn⟩ := exists_smul_eq_H1_of_ne_zero D.ρT' (pow_ne_zero n hπ0) y
      refine ⟨yn, mem_range_j'_of_map_eq_zero D yn (hq yn fun a => hinj ?_), hyn⟩
      rw [map_zero]
      apply frac_smul_eq_zero (pow_ne_zero n hπ0)
      have e : π ^ n • D.invF (cupFG D a yn) = D.invF (cupFG D a (π ^ n • yn)) := by
        rw [map_smul, map_smul]
      rw [e, hyn, hy]
    haveI : Module.Finite O (LinearMap.range D.j') := Module.Finite.range D.j'
    obtain ⟨y0, hy0, hy0e⟩ := hmem 0
    have hyR : y ∈ LinearMap.range D.j' := by
      rw [← hy0e]
      exact Submodule.smul_mem _ _ hy0
    have hK0 := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := LinearMap.range D.j')
      (IsLocalRing.maximalIdeal O) (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    have hπm : π ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit
    have hin : (⟨y, hyR⟩ : LinearMap.range D.j') ∈
        (⨅ i : ℕ, IsLocalRing.maximalIdeal O ^ i • ⊤ : Submodule O (LinearMap.range D.j')) := by
      rw [Submodule.mem_iInf]
      intro n
      obtain ⟨yn, hyn, hyne⟩ := hmem n
      have e : (⟨y, hyR⟩ : LinearMap.range D.j') = π ^ n • ⟨yn, hyn⟩ := Subtype.ext hyne.symm
      rw [e]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hπm n) Submodule.mem_top
    rw [hK0, Submodule.mem_bot] at hin
    exact congrArg Subtype.val hin
  obtain ⟨a, ha⟩ := exists_eq_of_nondeg ((cupFG D).compr₂ D.invF)
    (fun c hc a => exists_smul_eq_H1_of_ne_zero D.ρT hc a) (LinearMap.range D.j')
    (Module.Finite.iff_fg.1 inferInstance) (fun w => GlobalTheory.jSpan_holds hO hF i hD w) hnd f
  exact ⟨a, ha⟩

end GlobalTheory
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLocalDuality_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.RatIso := by
  atlas_forward_decl GlobalTheory.ratIso_of_localTateDuality
end
