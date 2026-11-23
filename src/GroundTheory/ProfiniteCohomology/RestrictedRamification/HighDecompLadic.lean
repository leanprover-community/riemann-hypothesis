module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighProcyclic
public import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import GroundTheory.LocalFields.MaximalUnramified
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerDivisor
import GroundTheory.ProfiniteCohomology.CohomologyTwoIntAddEquivQZSymmApply
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ABHNPrep
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteSetOfNsmulEqZeroQZ
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalDefs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalVal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.LocalField
  GroundTheory.LocalField.Abstract

open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K)
  (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})

section Hom

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hS : ∀ w : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ w.asIdeal → w ∈ S)

theorem val_intCast_nsmul_eq_zsmul {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n] {c : A} (hc : n • c = 0)
    (k : ℤ) : ((k : ZMod n).val) • c = k • c := by
  have h1 : (((k : ZMod n).val : ℕ) : ℤ) = k % n := ZMod.val_intCast k
  rw [← natCast_zsmul, h1]
  conv_rhs => rw [← Int.emod_add_mul_ediv k n]
  rw [add_smul, mul_comm, mul_smul, natCast_zsmul, hc, smul_zero, add_zero]

theorem dvd_of_nsmul_mk_one_div_eq_zero {N m : ℕ} (hN : N ≠ 0) (h : m • QZ.mk (1 / (N : ℚ)) = 0) : N ∣ m := by
  have h2 : QZ.mk ((m : ℚ) * (1 / (N : ℚ))) = 0 := by
    have e := map_nsmul QZ.mkHom m (1 / (N : ℚ))
    rw [nsmul_eq_mul] at e
    exact e.trans h
  obtain ⟨n, hn⟩ := (QZ.mk_eq_zero_iff _).1 h2
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have e1 : (n : ℚ) * (N : ℚ) = m := by rw [hn]; field_simp
  have e2 : n * (N : ℤ) = m := by exact_mod_cast e1
  exact Int.natCast_dvd_natCast.1 ⟨n, by rw [← e2, mul_comm]⟩

private theorem exists_nsmul_order_of_bijective {A B : Type*} [AddMonoid A] [AddMonoid B]
    (f : A →+ B) (hf : Function.Bijective f) {n : ℕ} {y : B}
    (hy : n • y = 0) (horder : ∀ m : ℕ, m • y = 0 → n ∣ m) :
    ∃ x : A, n • x = 0 ∧ ∀ m : ℕ, m • x = 0 → n ∣ m := by
  obtain ⟨x, rfl⟩ := hf.2 y
  refine ⟨x, hf.1 ?_, fun m hm => horder m ?_⟩
  · rw [f.map_nsmul, hy, f.map_zero]
  · rw [← f.map_nsmul, hm, f.map_zero]

theorem exists_localGaloisCohomology_order {ℓ : ℕ} (hℓ : ℓ.Prime) (w : HeightOneSpectrum (𝓞 K.1)) (b : ℕ) :
    ∃ t : localGaloisCohomology K 2 (.inr w), ℓ ^ b • t = 0 ∧ ∀ m : ℕ, m • t = 0 → ℓ ^ b ∣ m := by
  exact exists_nsmul_order_of_bijective (placeInv (K := K) (.inr w))
    (placeInv_bijective_inr (K := K) w) (QZ.nsmul_mk_one_div (ℓ ^ b))
    (fun _ => dvd_of_nsmul_mk_one_div_eq_zero (pow_ne_zero b hℓ.ne_zero))

private theorem nsmul_order_of_ker_le {A B C D : Type*}
    [AddMonoid A] [AddMonoid B] [AddMonoid C] [AddMonoid D]
    (e : A ≃+ B) (f : A →+ C) (r : B →+ D)
    (hker : ∀ y, f y = 0 → r (e y) = 0) {x : B} {t : D} {n : ℕ}
    (hx : n • x = 0) (ht : r x = t) (horder : ∀ m : ℕ, m • t = 0 → n ∣ m) :
    n • f (e.symm x) = 0 ∧ ∀ m : ℕ, m • f (e.symm x) = 0 → n ∣ m := by
  constructor
  · rw [← f.map_nsmul, ← map_nsmul e.symm, hx, map_zero, map_zero]
  · intro m hm
    apply horder m
    have hz : f (m • e.symm x) = 0 := (f.map_nsmul _ _).trans hm
    have hr := hker _ hz
    rwa [map_nsmul e, e.apply_symm_apply, r.map_nsmul, ht] at hr

set_option maxHeartbeats 8000000 in
include hℓ hS in
theorem exists_char_order_gsDecomp (b : ℕ) :
    ∃ χ : Additive Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) →ₜ+ QZ,
      ℓ ^ b • χ = 0 ∧ (∀ m : ℕ, m • χ = 0 → ℓ ^ b ∣ m) ∧
        ∀ h, gsDecomp K S ιs v h = 1 → χ (Additive.ofMul h) = 0 := by
  let lift := cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2
  let loc := (gsLocalRes S (ιs.fin v.1) 2).hom.toAddMonoidHom
  let val := (cohomologyMapAlong (decompHomS (v.1.adicCompletion K.1) S (ιs.fin v.1))
    (continuous_decompHomS (Kv := v.1.adicCompletion K.1) S (ιs.fin v.1))
    (ordEmbMor S (ιs.fin v.1) v.2) 2).hom.toAddMonoidHom
  let equiv := gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)
  let char := equiv.toAddMonoidHom.comp val
  have hker (y) (hy : char y = 0) : loc (lift y) = 0 :=
    (gsLocalRes_eq_zero_iff S (ιs.fin v.1) v.2 y).2
      (equiv.injective (hy.trans equiv.map_zero.symm))
  refine (exists_localGaloisCohomology_order K hℓ v.1 b).elim fun t ht => ?_
  refine (exists_gsLocalRes_eq_single K S ℓ hℓ hS ιs v.1 v.2 t b ht.1).elim fun x hx => ?_
  have hord := nsmul_order_of_ker_le lift char loc hker hx.1 hx.2.1 ht.2
  exact ⟨char (lift.symm x), hord.1, hord.2, fun h hh =>
    gvChar_decompHomS_eq_zero S (ιs.fin v.1) (lift.symm x) (ordEmbMor S (ιs.fin v.1) v.2) h hh⟩

private theorem char_eq_proj_nsmul {G : Type*} [Group G] [TopologicalSpace G]
    (deg : G →* Multiplicative ℤ̂) (hdeg : Continuous deg) (σ : G)
    (hσ : deg σ = Multiplicative.ofAdd 1)
    (eq_univ : ∀ E : Set G, IsClosed E → (∀ k : ℤ, σ ^ k ∈ E) →
      (∀ g ∈ E, ∀ h, deg h = 1 → g * h ∈ E) → E = Set.univ)
    (n : ℕ+) (χ : Additive G →ₜ+ QZ) (hχ : (n : ℕ) • χ = 0)
    (hker : ∀ h, deg h = 1 → χ (Additive.ofMul h) = 0) (g : G) :
    χ (Additive.ofMul g) = (ProfiniteInteger.proj n (Multiplicative.toAdd (deg g))).val •
      χ (Additive.ofMul σ) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let proj := ProfiniteInteger.proj n
  let c := χ (Additive.ofMul σ)
  have hc : (n : ℕ) • c = 0 := by
    change (n : ℕ) • χ (Additive.ofMul σ) = 0
    rw [← ContinuousAddMonoidHom.nsmul_apply, hχ]
    rfl
  let E : Set G := {g | χ (Additive.ofMul g) = (proj (Multiplicative.toAdd (deg g))).val • c}
  have hclosed : IsClosed E :=
    isClosed_eq (χ.continuous.comp continuous_ofMul)
      ((continuous_of_discreteTopology (f := fun z : ZMod n => z.val • c)).comp
        ((ProfiniteInteger.continuous_proj n).comp (continuous_toAdd.comp hdeg)))
  have hpow (k : ℤ) : σ ^ k ∈ E := by
    change χ (Additive.ofMul (σ ^ k)) = (proj (Multiplicative.toAdd (deg (σ ^ k)))).val • c
    rw [ofMul_zpow, map_zsmul, deg.map_zpow, hσ, ← ofAdd_zsmul, toAdd_ofAdd, zsmul_one, map_intCast]
    exact (val_intCast_nsmul_eq_zsmul hc k).symm
  have hmul (g : G) (hg : g ∈ E) (h : G) (hh : deg h = 1) : g * h ∈ E := by
    change χ (Additive.ofMul (g * h)) = (proj (Multiplicative.toAdd (deg (g * h)))).val • c
    rw [ofMul_mul, map_add (f := χ), hker h hh, add_zero, deg.map_mul, hh, mul_one]
    exact hg
  exact Set.eq_univ_iff_forall.mp (eq_univ E hclosed hpow hmul) g

set_option maxHeartbeats 4000000 in
theorem char_eq_proj_nsmul_of_gsDecomp {ℓ : ℕ} (hℓ : ℓ.Prime) (b : ℕ)
    (χ : Additive Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) →ₜ+ QZ)
    (hχk : ℓ ^ b • χ = 0) (hB : ∀ h, gsDecomp K S ιs v h = 1 → χ (Additive.ofMul h) = 0)
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hσ : unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1)
    (g : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)) :
    χ (Additive.ofMul g) = (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
      (Multiplicative.toAdd (unramifiedDegree
        (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) : ZMod (ℓ ^ b)).val •
          χ (Additive.ofMul σ) := by
  exact char_eq_proj_nsmul (unramifiedDegree _ _) continuous_unramifiedDegree σ hσ
    (eq_univ_of_unramifiedDegree v.1 σ hσ) ⟨ℓ ^ b, pow_pos hℓ.pos b⟩ χ hχk
    (fun h hh => hB h (gsDecomp_eq_one_of_unramifiedDegree_eq_one K S ιs v h hh)) g

private theorem zmod_eq_zero_of_char_eq_nsmul {G : Type*} [Group G] [TopologicalSpace G]
    {n : ℕ} [NeZero n] (χ : Additive G →ₜ+ QZ)
    (horder : ∀ m : ℕ, m • χ = 0 → n ∣ m) (c : QZ) (proj : G → ZMod n)
    (hchar : ∀ g, χ (Additive.ofMul g) = (proj g).val • c) (g : G)
    (hg : χ (Additive.ofMul g) = 0) : proj g = 0 := by
  have hzero : (proj g).val • c = 0 := (hchar g).symm.trans hg
  have hsmul : (proj g).val • χ = 0 := by
    refine DFunLike.ext _ _ fun y => ?_
    rw [ContinuousAddMonoidHom.nsmul_apply, ← ofMul_toMul y, hchar, smul_comm, hzero, smul_zero]
    rfl
  exact (ZMod.val_eq_zero (proj g)).1
    (Nat.eq_zero_of_dvd_of_lt (horder _ hsmul) (ZMod.val_lt (proj g)))

set_option maxHeartbeats 4000000 in
include hℓ hS in
theorem proj_unramifiedDegree_eq_zero_of_gsDecomp_eq_one (b : ℕ)
    (g : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hg : gsDecomp K S ιs v g = 1) :
    ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩ (Multiplicative.toAdd (unramifiedDegree
      (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) = 0 := by
  let : NeZero (ℓ ^ b) := ⟨pow_ne_zero b hℓ.ne_zero⟩
  let deg := unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1))
  let proj g := ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩ (Multiplicative.toAdd (deg g))
  refine (exists_unramifiedDegree_eq_one (K := K) (v := v.1)).elim fun σ hσ => ?_
  refine (exists_char_order_gsDecomp K S ιs v hℓ hS b).elim fun χ hχ => ?_
  exact zmod_eq_zero_of_char_eq_nsmul χ hχ.2.1 (χ (Additive.ofMul σ)) proj
    (char_eq_proj_nsmul_of_gsDecomp K S ιs v hℓ b χ hχ.1 hχ.2.2 σ hσ) g (hχ.2.2 g hg)

private theorem exists_range_hom_zmod {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (f : G →* H)
    (hf : Topology.IsQuotientMap f.rangeRestrict)
    (deg : G →* Multiplicative ℤ̂) (hdeg : Continuous deg) (n : ℕ+)
    (hker : ∀ g, f g = 1 → ProfiniteInteger.proj n (Multiplicative.toAdd (deg g)) = 0)
    (σ : G) (hσ : deg σ = Multiplicative.ofAdd 1) :
    ∃ φ : f.range →* Multiplicative (ZMod n),
      IsOpen (φ.ker : Set f.range) ∧ φ (f.rangeRestrict σ) = Multiplicative.ofAdd 1 := by
  let proj g := ProfiniteInteger.proj n (Multiplicative.toAdd (deg g))
  let ψ := (ProfiniteInteger.proj n).toAddMonoidHom.toMultiplicative.comp deg
  have hker' : f.ker ≤ ψ.ker := fun g hg =>
    MonoidHom.mem_ker.mpr (congrArg Multiplicative.ofAdd (hker g (MonoidHom.mem_ker.mp hg)))
  let e := QuotientGroup.quotientKerEquivRange f
  let φ := (QuotientGroup.lift _ ψ hker').comp e.symm.toMonoidHom
  have hφ (g : G) : φ (f.rangeRestrict g) = ψ g := by
    have he : e.symm (f.rangeRestrict g) = (g : G ⧸ f.ker) := e.symm_apply_apply (g : G ⧸ f.ker)
    change QuotientGroup.lift _ ψ hker' (e.symm (f.rangeRestrict g)) = ψ g
    rw [he, QuotientGroup.lift_mk]
  refine ⟨φ, ?_, ?_⟩
  · rw [← hf.isOpen_preimage]
    have hpreimage : f.rangeRestrict ⁻¹' (φ.ker : Set f.range) = proj ⁻¹' {0} := by
      refine Set.ext fun g => ?_
      change φ (f.rangeRestrict g) = 1 ↔ proj g ∈ ({0} : Set (ZMod n))
      rw [hφ, Set.mem_singleton_iff]
      exact Iff.rfl
    rw [hpreimage]
    exact (isOpen_discrete _).preimage
      ((ProfiniteInteger.continuous_proj n).comp (continuous_toAdd.comp hdeg))
  · rw [hφ]
    change Multiplicative.ofAdd (ProfiniteInteger.proj n (Multiplicative.toAdd (deg σ))) = _
    rw [hσ, toAdd_ofAdd, map_one]

set_option maxHeartbeats 4000000 in
include hℓ hS in
theorem exists_hom_zmod_pow_rangeRestrict_gsDecomp
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hσ : unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1) (b : ℕ) :
    ∃ φ : (gsDecomp K S ιs v).range →* Multiplicative (ZMod (ℓ ^ b)),
      IsOpen (φ.ker : Set (gsDecomp K S ιs v).range) ∧
        φ ((gsDecomp K S ιs v).rangeRestrict σ) = Multiplicative.ofAdd 1 := by
  exact exists_range_hom_zmod (gsDecomp K S ιs v) (isQuotientMap_rangeRestrict_gsDecomp K S ιs v)
    (unramifiedDegree _ _) continuous_unramifiedDegree ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
    (proj_unramifiedDegree_eq_zero_of_gsDecomp_eq_one K S ιs v hℓ hS b) σ hσ


set_option maxHeartbeats 4000000 in
include hℓ hS in
theorem exists_isPrimePowGenerator_gsDecomp :
    ∃ σ : (gsDecomp K S ιs v).range, IsPrimePowGenerator ℓ σ := by
  refine (exists_unramifiedDegree_eq_one (K := K) (v := v.1)).elim fun σ hσ => ?_
  exact ⟨(gsDecomp K S ιs v).rangeRestrict σ, isTopologicalGenerator_rangeRestrict_gsDecomp K S ιs v σ hσ,
    fun b => exists_hom_zmod_pow_rangeRestrict_gsDecomp K S ιs v hℓ hS σ hσ b⟩

instance isDiscreteRep_res_range_gsDecomp :
    IsDiscreteRep (Rep.res (gsDecomp K S ιs v).range.subtype (trivRep (galUnramifiedOutside K.1 ℚ̄ S) QZ)) :=
  isDiscreteRep_res_subtype _ _

instance totallyDisconnectedSpace_range_gsDecomp : TotallyDisconnectedSpace (gsDecomp K S ιs v).range :=
  have := galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S
  inferInstance


set_option maxHeartbeats 4000000 in
include hℓ hS in
theorem eq_zero_of_pow_nsmul_cohomology_range_gsDecomp {p : ℕ} (hp : 2 ≤ p)
    (x : cohomology (Rep.res (gsDecomp K S ιs v).range.subtype
      (trivRep (galUnramifiedOutside K.1 ℚ̄ S) QZ)) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  exact (exists_isPrimePowGenerator_gsDecomp K S ιs v hℓ hS).elim fun _ hσ =>
    hσ.eq_zero_of_pow_nsmul hℓ _ isAddTorsion_QZ hp x hx

end Hom

end

end GroundTheory.ProfCoh
