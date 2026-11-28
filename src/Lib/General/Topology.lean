module

public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.Connected
public import Lib.Speed

/-!
# Open subgroups, a tube lemma, and procyclic images of ℓ-adic characters

This file collects auxiliary facts from topology and algebra. It characterises congruence modulo a
principal ideal `(a)` by divisibility of the difference by `a`.

## Main definitions and results

* `IsCompact.eventually_forall_mem`: a form of the tube lemma for a jointly continuous map of two
  variables, with the continuity hypothesis discharged by `fun_prop` by default.
* `New.Selmer.exists_procyclic_generator`: a continuous character of a compact group with values in
  1 + 4ℤ_ℓ has procyclic image.
* `MonoidHom.IsGeneratorModKer`: an element generates a topological group modulo the kernel of a
  homomorphism; `New.Selmer.exists_isGeneratorModKer` gives one for such a character of a profinite
  group.
-/

@[expose] public section

/-! ## Open subgroups, a tube lemma, and congruence modulo a principal ideal -/

/-- The subgroup U of G is an open subset of G. -/
@[to_additive /-- The additive subgroup U of G is an open subset of G. -/]
protected abbrev Subgroup.IsOpen {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G) :
    Prop := IsOpen (X := G) U

/-- Tube lemma for a jointly continuous f: if W is a neighbourhood of f(x₀, y) for each y in a
compact set K, then f(x, y) ∈ W for all y in K and all x near x₀. -/
lemma IsCompact.eventually_forall_mem {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {K : Set Y} {x₀ : X} (hK : IsCompact K) (f : X → Y → Z) (W : Set Z)
    (h_nhds : ∀ y ∈ K, W ∈ nhds (f x₀ y)) (hf : Continuous f.uncurry := by fun_prop) :
    ∀ᶠ x : X in nhds x₀, ∀ y ∈ K, f x y ∈ W :=
  hK.eventually_forall_of_forall_eventually fun y hy ↦ hf.continuousAt (h_nhds y hy)

/-- Two elements x and y have the same class modulo the principal ideal (a) if and only if a divides
x − y. -/
lemma Ideal.mk_span_eq_iff_dvd_sub {R : Type*} [CommRing R] {a x y : R} :
    Quotient.mk (span {a}) x = Quotient.mk (span {a}) y ↔ a ∣ x - y :=
  Quotient.eq.trans mem_span_singleton

/-! ## Procyclic images of ℓ-adic characters of compact groups -/

section ProcyclicImage

open PadicInt Filter Subgroup ZMod Nat Units

/-- A unit modulo `2^(k+2)` that is `1` modulo `4` is a power of `5`. -/
private lemma mem_zpowers_unitFive_of_reduction_eq_one {k : ℕ}
    {u : (ZMod (2 ^ (k + 2)))ˣ}
    (hu : ZMod.unitsMap (pow_dvd_pow 2 (Nat.le_add_left 2 k)) u = 1) :
    u ∈ zpowers ZMod.unitFive := by
  obtain ⟨⟨v, ⟨_, m, rfl⟩⟩, rfl⟩ := (isComplement'_zpowers_unitFive_neg_one (k + 2)).2 u
  have hv : ZMod.unitsMap (pow_dvd_pow 2 (Nat.le_add_left 2 k)) v.val = 1 := by
    obtain ⟨t, ht⟩ := mem_zpowers_iff.mp v.property
    rw [← ht, map_zpow, unitsMap_unitFive, unitFive_eq_one le_rfl, one_zpow]
  -- Reducing modulo four rules out the negative sign.
  have h_neg : (-1 : (ZMod (2 ^ 2))ˣ) ≠ 1 := by decide
  rw [map_mul, hv, one_mul, map_zpow, unitsMap_def, Units.map_neg_one, neg_one_zpow_eq_ite,
    ite_eq_left_iff] at hu
  have hm : Even m := by_contra fun hm ↦ h_neg (hu hm)
  simp [neg_one_zpow_eq_ite, hm]

/-- A character with values in `1 + 4ℤ_ℓ` has cyclic image modulo every `ℓ^(k+2)`. -/
lemma New.Selmer.isCyclic_range_toZModPow {ℓ : ℕ} {Γ : Type*} [Fact ℓ.Prime] [Group Γ]
    (κ : Γ →* ℤ_[ℓ]ˣ) (hκ_four : ∀ g : Γ, 4 ∣ (κ g).val - 1) (k : ℕ) :
    IsCyclic ((Units.map
      (toZModPow (k + 2) : ℤ_[ℓ] →+* ZMod (ℓ ^ (k + 2))).toMonoidHom).comp κ).range := by
  obtain hℓ | rfl := em' (ℓ = 2)
  · have : IsCyclic (ZMod (ℓ ^ (k + 2)))ˣ := isCyclic_units_of_prime_pow ℓ Fact.out hℓ _
    infer_instance
  refine isCyclic_of_le (H' := zpowers (unitFive (n := k + 2))) ?_
  rintro _ ⟨g, rfl⟩
  apply mem_zpowers_unitFive_of_reduction_eq_one
  apply Units.ext
  rw [ZMod.unitsMap_val]
  change ZMod.cast (toZModPow (k + 2) (κ g : ℤ_[2])) = 1
  rw [cast_toZModPow 2 (k + 2) (Nat.le_add_left 2 k)]
  have h_mem : (κ g : ℤ_[2]) - 1 ∈ RingHom.ker (toZModPow 2) := by
    rw [ker_toZModPow, Ideal.mem_span_singleton]
    norm_num
    exact hκ_four g
  simpa [RingHom.mem_ker, map_sub, sub_eq_zero] using h_mem

/-- Let ℓ be a prime and κ a continuous homomorphism from a compact group Γ to ℤ_ℓ^× with values in
1 + 4ℤ_ℓ (for odd ℓ this is no condition, as 4 is a unit of ℤ_ℓ; for ℓ = 2 it keeps κ away from
−1). Then κ has procyclic image: for some γ, every open subgroup S that contains γ and ker κ is all
of Γ. -/
lemma New.Selmer.exists_procyclic_generator {ℓ : ℕ} {Γ : Type*} [Fact ℓ.Prime] [Group Γ]
    [TopologicalSpace Γ] [CompactSpace Γ] (κ : Γ →* ℤ_[ℓ]ˣ) (hκ : Continuous κ)
    (hκ_four : ∀ g : Γ, 4 ∣ (κ g).val - 1) :
    ∃ γ : Γ, ∀ S : Subgroup Γ, κ.ker ≤ S → S.IsOpen → γ ∈ S → ∀ g : Γ, g ∈ S := by
  -- The image of κ modulo every ℓ^(k+2) is cyclic, generated by
  -- κ(γ k). A cluster point δ of the γ k works: an open S ∋ δ holds γ k for arbitrarily large k,
  -- and an open S ≥ ker κ holds the kernel of κ modulo ℓ^(k+2) for large k.
  let red (k : ℕ) : ℤ_[ℓ]ˣ →* (ZMod (ℓ ^ (k + 2)))ˣ :=
    Units.map (toZModPow (k + 2) : ℤ_[ℓ] →+* ZMod (ℓ ^ (k + 2))).toMonoidHom
  have exists_gen (k : ℕ) : ∃ γ : Γ, ∀ g : Γ,
      ∃ n : ℤ, (red k).comp κ γ ^ n = (red k).comp κ g := by
    obtain ⟨⟨_, γ, rfl⟩, hγ⟩ := (isCyclic_range_toZModPow κ hκ_four k).exists_generator
    exact ⟨γ, fun g ↦ (mem_zpowers_iff.mp (hγ ⟨_, g, rfl⟩)).imp fun n hn ↦ Subtype.ext_iff.mp hn⟩
  choose γ hγ using exists_gen
  obtain ⟨δ, hδ⟩ : ∃ δ : Γ, ClusterPt δ (atTop.map γ) := exists_clusterPt_of_compactSpace _
  refine ⟨δ, fun S S_ker S_open hδS g ↦ ?_⟩
  -- As Γ is compact, κ is a closed map, so S contains all x with κ(x) close to 1.
  have near_one : ∀ᶠ y : ℤ_[ℓ] in nhds 1, ∀ x ∈ (Units.val ∘ κ) ⁻¹' {y}, x ∈ S :=
    (Units.continuous_val.comp hκ).isClosedMap.eventually_nhds_fiber 1 fun x hx ↦
      S_open.mem_nhds (S_ker (Units.ext hx))
  obtain ⟨ε, ε_pos, hε⟩ := Metric.eventually_nhds_iff.mp near_one
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (ℓ : ℝ) ^ (-(j : ℤ)) < ε := exists_pow_neg_lt ℓ ε_pos
  obtain ⟨k, hjk, hγS⟩ : ∃ k : ℕ, j ≤ k ∧ γ k ∈ S :=
    frequently_atTop.mp (hδ.frequently (S_open.mem_nhds hδS)) j
  -- κ(x) ≡ 1 modulo ℓ^(k+2), with j ≤ k, gives |κ(x) − 1| ≤ ℓ^(−j) < ε.
  have ker_le : ((red k).comp κ).ker ≤ S := fun x hx ↦ by
    have hx_one : toZModPow (k + 2) (κ x : ℤ_[ℓ]) = 1 := by simpa [red, Units.ext_iff] using hx
    have hle : j ≤ k + 2 := le_add_right hjk
    have hx_mem : (κ x : ℤ_[ℓ]) - 1 ∈ RingHom.ker (toZModPow j) := by
      simp [← cast_toZModPow j (k + 2) hle, hx_one]
    rw [ker_toZModPow, ← norm_le_pow_iff_mem_span_pow, ← dist_eq_norm] at hx_mem
    exact hε (hx_mem.trans_lt hj) x rfl
  -- Modulo that kernel, g is a power of γ k.
  obtain ⟨n, hn⟩ := hγ k g
  have h_mem : (γ k ^ n)⁻¹ * g ∈ S := ker_le (by simp [-MonoidHom.coe_comp, hn])
  simpa using S.mul_mem (S.zpow_mem hγS n) h_mem

/-- The element γ generates Γ modulo the kernel of κ: the only closed subgroup that contains γ and
ker κ is Γ. -/
def MonoidHom.IsGeneratorModKer {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [Group A]
    (κ : Γ →* A) (γ : Γ) : Prop :=
  ∀ S : Subgroup Γ, IsClosed (S : Set Γ) → κ.ker ≤ S → γ ∈ S → S = ⊤

/-- If γ generates Γ modulo the kernel of κ, then so does γ⁻¹. -/
lemma MonoidHom.IsGeneratorModKer.inv {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [Group A]
    {κ : Γ →* A} {γ : Γ} (hγ : κ.IsGeneratorModKer γ) : κ.IsGeneratorModKer γ⁻¹ :=
  fun S S_closed S_ker h_mem ↦ hγ S S_closed S_ker (inv_mem_iff.1 h_mem)

/-- Let γ generate the compact group Γ modulo the closed kernel of κ. Then every g is a product
h q with h in ker κ and q in the closure of the powers of γ. -/
lemma MonoidHom.IsGeneratorModKer.exists_mul_eq {Γ A : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [Group A] {κ : Γ →* A} {γ : Γ}
    (hγ : κ.IsGeneratorModKer γ) (h_ker : IsClosed (κ.ker : Set Γ)) (g : Γ) :
    ∃ h ∈ κ.ker, ∃ q ∈ (zpowers γ).topologicalClosure, h * q = g := by
  have h_closed : IsClosed (↑(κ.ker ⊔ (zpowers γ).topologicalClosure) : Set Γ) := by
    simpa [normal_mul] using h_ker.mul_right_of_isCompact (isClosed_topologicalClosure _).isCompact
  have h_top : κ.ker ⊔ (zpowers γ).topologicalClosure = ⊤ :=
    hγ _ h_closed le_sup_left (mem_sup_right (le_topologicalClosure _ (mem_zpowers γ)))
  exact mem_sup_of_normal_left.1 (h_top.ge (mem_top g))

/-- If γ generates Γ modulo the kernel of a continuous character κ with values in ℤ_ℓ^×, then
κ(γ)^a − 1 divides κ(g)^a − 1 for every g. -/
lemma MonoidHom.IsGeneratorModKer.pow_sub_one_dvd {ℓ : ℕ} {Γ : Type*} [Fact ℓ.Prime] [Group Γ]
    [TopologicalSpace Γ] {κ : Γ →* ℤ_[ℓ]ˣ} {γ : Γ} (hγ : κ.IsGeneratorModKer γ)
    (hκ : Continuous κ) (a : ℕ) (g : Γ) : (κ γ ^ a).val - 1 ∣ (κ g ^ a).val - 1 := by
  -- The g with this property form the kernel S of κ^a modulo the closed ideal (κ(γ)^a − 1).
  let I : Ideal ℤ_[ℓ] := .span {(κ γ ^ a).val - 1}
  let S : Subgroup Γ := ((Units.map (Ideal.Quotient.mk I).toMonoidHom).comp (κ ^ a)).ker
  have mem_S (x : Γ) : x ∈ S ↔ (κ x ^ a).val - 1 ∈ I := by
    simp [S, Units.ext_iff, ← Ideal.Quotient.eq]
  have S_closed : IsClosed (S : Set Γ) := by
    rw [show (S : Set Γ) = (fun x ↦ (κ x ^ a).val - 1) ⁻¹' I from Set.ext mem_S]
    exact (IsNoetherianRing.isClosed_ideal I).preimage (by fun_prop)
  have ker_le : κ.ker ≤ S := fun x hx ↦ by simp [mem_S, mem_ker.1 hx]
  have h_top : S = ⊤ := hγ S S_closed ker_le ((mem_S γ).2 (Ideal.mem_span_singleton_self _))
  exact Ideal.mem_span_singleton.1 ((mem_S g).1 (h_top.ge (mem_top g)))

/-- A profinite group has a generator modulo the kernel of a continuous character with values in
1 + 4ℤ_ℓ. -/
lemma New.Selmer.exists_isGeneratorModKer {ℓ : ℕ} {Γ : Type*} [Fact ℓ.Prime] [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {κ : Γ →* ℤ_[ℓ]ˣ} (hκ : Continuous κ) (hκ_four : ∀ g : Γ, 4 ∣ (κ g).val - 1) :
    ∃ γ : Γ, κ.IsGeneratorModKer γ := by
  obtain ⟨γ, hγ⟩ := exists_procyclic_generator κ hκ hκ_four
  refine ⟨γ, fun S S_closed S_ker hγS ↦ ?_⟩
  -- A closed subgroup is the intersection of the open subgroups that contain it.
  have h_inf : S = sInf {N : Subgroup Γ | IsOpen (N : Set Γ) ∧ S ≤ N} :=
    ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨S, S_closed⟩
  rw [h_inf, sInf_eq_top]
  exact fun N ⟨N_open, hSN⟩ ↦ (eq_top_iff' N).2 (hγ N (S_ker.trans hSN) N_open (hSN hγS))

end ProcyclicImage
