import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNorms

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

namespace GlobalTheory.LKTorus

variable (L : Type) [Field L] [NumberField L]

def simTA (c : L →ₐ[ℚ] L) : Subgroup (AfE ℚ L)ˣ where
  carrier := {x | ∃ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, x * conjId c x = idF ℚ L t}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    rw [map_mul, map_mul, ← hs, ← ht]
    exact mul_mul_mul_comm x y (conjId c x) (conjId c y)
  inv_mem' := by
    rintro x ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    rw [map_inv, map_inv, ← hs, mul_inv]

def ratT (c : L →ₐ[ℚ] L) : Subgroup (simTA L c) :=
  ((simT ℚ c).map (ratId ℚ L)).subgroupOf (simTA L c)

theorem ratId_mem_simTA (c : L →ₐ[ℚ] L) {a : Lˣ} (ha : a ∈ simT ℚ c) : ratId ℚ L a ∈ simTA L c := by
  obtain ⟨t, ht⟩ := ha
  refine ⟨Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom t, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, ratId, conjId, idF, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  simp only [inclE, sigR, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Algebra.TensorProduct.includeRight_apply]
  rw [ht, Algebra.algebraMap_eq_smul_one (A := L), Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 ℚ) ℚ),
    TensorProduct.smul_tmul]

theorem conjId_ratId (c : L →ₐ[ℚ] L) (a : Lˣ) :
    conjId c (ratId ℚ L a) = ratId ℚ L (Units.map (c : L →+* L).toMonoidHom a) := by
  apply Units.ext
  simp [conjId, ratId, sigR, inclE]

theorem idF_map_algebraMap (r : ℚˣ) :
    idF ℚ L (Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom r) =
      ratId ℚ L (Units.map (algebraMap ℚ L).toMonoidHom r) := by
  apply Units.ext
  simp only [idF, ratId, inclE, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.coe_coe,
    AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
  rw [Algebra.algebraMap_eq_smul_one (A := L), Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 ℚ) ℚ),
    TensorProduct.smul_tmul]

theorem sigR_mem_RInt (c : L →ₐ[ℚ] L) {y : AfE ℚ L} (hy : y ∈ RInt ℚ L) :
    sigR c (FiniteAdeleRing (𝓞 ℚ) ℚ) y ∈ RInt ℚ L := by
  have hle : RInt ℚ L ≤ (RInt ℚ L).comap (sigR c (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    refine (Subring.closure_le).2 ?_
    rintro g (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨d, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨⟨c (algebraMap (𝓞 L) L b), ⟨RingOfIntegers.mapRingHom (c : L →+* L) b, ?_⟩⟩, ?_⟩)
      · rfl
      · simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨d, ?_⟩)
      simp [sigR]
  exact hle hy

theorem conjId_mem_intU (c : L →ₐ[ℚ] L) {k : (AfE ℚ L)ˣ} (hk : k ∈ intU ℚ L) : conjId c k ∈ intU ℚ L := by
  rw [intU, Submonoid.mem_units_iff] at hk ⊢
  refine ⟨sigR_mem_RInt L c hk.1, ?_⟩
  rw [← map_inv]
  exact sigR_mem_RInt L c hk.2

theorem idF_mem_intU {u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hu : (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ)
    (hu' : ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ) : idF ℚ L u ∈ intU ℚ L := by
  rw [intU, Submonoid.mem_units_iff]
  refine ⟨Subring.subset_closure (Or.inr ⟨⟨_, hu⟩, rfl⟩), ?_⟩
  rw [← map_inv]
  exact Subring.subset_closure (Or.inr ⟨⟨_, hu'⟩, rfl⟩)

end GlobalTheory.LKTorus
end
end

section
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Topology Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongOpen

variable (L : Type) [Field L] [NumberField L]

local notation "A" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem rsmul_tmul (a y : A) (x : L) :
    letI : Algebra A (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    a • (x ⊗ₜ[ℚ] y : AfE ℚ L) = x ⊗ₜ (a * y) := by
  letI : Algebra A (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
  rw [Algebra.smul_def]
  show (Algebra.TensorProduct.includeRight a : AfE ℚ L) * _ = _
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable {L} {d : ℕ} (b : Module.Basis (Fin d) ℤ (𝓞 L))

def coordSub : AddSubgroup (AfE ℚ L) where
  carrier := {t | ∃ z : Fin d → A, (∀ i, z i ∈ intAd ℚ) ∧ ∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i = t}
  zero_mem' := ⟨0, fun _ => zero_mem _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨z + z', fun i => add_mem (hz i) (hz' i), by
      simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨-z, fun i => neg_mem (hz i), by simp [TensorProduct.tmul_neg]⟩

theorem mem_coordSub {t : AfE ℚ L} :
    t ∈ coordSub b ↔ ∃ z : Fin d → A, (∀ i, z i ∈ intAd ℚ) ∧ ∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i = t :=
  Iff.rfl

theorem tmul_mem (x : 𝓞 L) {y : A} (hy : y ∈ intAd ℚ) :
    ((x : L) ⊗ₜ[ℚ] y : AfE ℚ L) ∈ coordSub b := by
  refine ⟨fun i => ((b.repr x i : ℤ) : A) * y, fun i => mul_mem (intCast_mem _ _) hy, ?_⟩
  have hx : ((x : 𝓞 L) : L) = ∑ i, ((b.repr x i : ℚ)) • ((b i : 𝓞 L) : L) := by
    conv_lhs => rw [← b.sum_repr x]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul, Algebra.smul_def, map_intCast]
  rw [hx, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e2 : (((b.repr x i : ℤ) : A) * y) = ((b.repr x i : ℚ)) • y := by
    rw [Algebra.smul_def, map_intCast]
  show _ ⊗ₜ[ℚ] (((b.repr x i : ℤ) : A) * y) = _
  rw [e2, TensorProduct.smul_tmul]

theorem mul_mem' {s t : AfE ℚ L} (hs : s ∈ coordSub b) (ht : t ∈ coordSub b) : s * t ∈ coordSub b := by
  obtain ⟨z, hz, rfl⟩ := hs
  obtain ⟨z', hz', rfl⟩ := ht
  rw [Finset.sum_mul_sum]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  have := tmul_mem b (b i * b j) (mul_mem (hz i) (hz' j))
  simpa using this

def coordRing : Subring (AfE ℚ L) :=
  { coordSub b with
    one_mem' := by
      have := tmul_mem b (1 : 𝓞 L) (one_mem (intAd ℚ))
      simpa [Algebra.TensorProduct.one_def] using this
    mul_mem' := fun hs ht => mul_mem' b hs ht }

theorem rInt_le : RInt ℚ L ≤ coordRing b := by
  show Subring.closure _ ≤ _
  rw [Subring.closure_le]
  rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
  · exact tmul_mem b a (one_mem _)
  · have := tmul_mem b (1 : 𝓞 L) hy
    exact (by simpa using this : _ ∈ coordSub b)

end GlobalTheory.CongOpen

namespace GlobalTheory.CongOpen

theorem exists_congN_subset : ∀ (L : Type) [Field L] [NumberField L],
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ V : Set (AfE ℚ L)ˣ, IsOpen V → (1 : (AfE ℚ L)ˣ) ∈ V → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ congN ℚ L N, u ∈ V := by
  intro L _ _
  letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
  intro V hV h1
  haveI hMT : IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := ⟨rfl⟩
  haveI : ContinuousAdd (AfE ℚ L) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
  haveI : ContinuousSMul (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) :=
    IsModuleTopology.toContinuousSMul (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (Module.Basis (Fin d) ℤ (𝓞 L)) :=
    ⟨_, ⟨(RingOfIntegers.basis L).reindex (Fintype.equivFin _)⟩⟩
  let φ : (Fin d → FiniteAdeleRing (𝓞 ℚ) ℚ) → AfE ℚ L := fun z => ∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i
  have hφs : ∀ z, φ z = ∑ i, z i • (((b i : 𝓞 L) : L) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    intro z
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rsmul_tmul, mul_one]
  have hφc : Continuous φ := by
    have : φ = fun z => ∑ i, z i • (((b i : 𝓞 L) : L) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) := funext hφs
    rw [this]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hφn : ∀ (n : ℕ) z, φ ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) • z) = (n : AfE ℚ L) * φ z := by
    intro n z
    rw [hφs, hφs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_smul, Algebra.smul_def (n : FiniteAdeleRing (𝓞 ℚ) ℚ), map_natCast]

  have hV1 : V ∈ 𝓝 (1 : (AfE ℚ L)ˣ) := hV.mem_nhds h1
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, map_one] at hV1
  obtain ⟨O, hO, hOV⟩ := Filter.mem_comap.1 hV1
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 hO
  have hW₂' : MulOpposite.op ⁻¹' W₂ ∈ 𝓝 (1 : AfE ℚ L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW₂
  have hU : (fun z => 1 + φ z) ⁻¹' (W₁ ∩ MulOpposite.op ⁻¹' W₂) ∈ 𝓝 (0 : Fin d → FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    refine (continuous_const.add hφc).continuousAt.preimage_mem_nhds ?_
    have h0 : 1 + φ 0 = 1 := by simp [φ]
    show _ ∈ 𝓝 (1 + φ 0)
    rw [h0]
    exact inter_mem hW₁ hW₂'
  obtain ⟨n, hn, hnU⟩ := GlobalTheory.SWQ.FinAnnih.exists_nat_smul_mem _ hU
  refine ⟨n, hn, fun u hu => ?_⟩

  have key : ∀ w : RInt ℚ L, (w : RInt ℚ L) - 1 ∈ Ideal.span {((n : ℕ) : RInt ℚ L)} →
      ((w : AfE ℚ L)) ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ := by
    intro w hw
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hw
    obtain ⟨z, hz, hza⟩ := (mem_coordSub b).1 (rInt_le b a.2)
    have hwe : (w : AfE ℚ L) = 1 + φ ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) • z) := by
      rw [hφn]
      have := congrArg (fun t : RInt ℚ L => (t : AfE ℚ L)) ha
      push_cast at this
      show _ = 1 + (n : AfE ℚ L) * (∑ i, ((b i : 𝓞 L) : L) ⊗ₜ[ℚ] z i)
      rw [hza, mul_comm, this]
      ring
    rw [hwe]
    exact hnU z hz
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
  rw [mem_kerRed] at hu'
  have hinv : ((u'⁻¹ : (RInt ℚ L)ˣ) : RInt ℚ L) - 1 ∈ Ideal.span {((n : ℕ) : RInt ℚ L)} := by
    have e : ((u'⁻¹ : (RInt ℚ L)ˣ) : RInt ℚ L) - 1 =
        -((u'⁻¹ : (RInt ℚ L)ˣ) : RInt ℚ L) * ((u' : RInt ℚ L) - 1) := by
      rw [mul_sub, neg_mul, Units.inv_mul]
      ring
    rw [e]
    exact Ideal.mul_mem_left _ _ hu'
  apply hOV
  rw [Set.mem_preimage, Units.embedProduct_apply]
  refine hW ⟨(key _ hu').1, ?_⟩
  have := (key _ hinv).2
  simpa [Units.coe_map, map_inv] using this

end GlobalTheory.CongOpen
end
end

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_units_basis_of_nbhds : ∀ (L : Type) [Field L] [NumberField L],
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ V : Set (AfE ℚ L)ˣ, IsOpen V → (1 : (AfE ℚ L)ˣ) ∈ V → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ congN ℚ L N, u ∈ V := by
  atlas_forward_decl GlobalTheory.CongOpen.exists_congN_subset
end

section
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongNIndex

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embO : 𝓞 E →+* RInt F E :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeLeft : E →ₐ[F] AfE F E).toRingHom.comp (algebraMap (𝓞 E) E))
    (RInt F E) fun o => Subring.subset_closure (Set.mem_union_left _ ⟨⟨_, RingHom.mem_range.2 ⟨o, rfl⟩⟩, rfl⟩)

def redO (N : ℕ) : 𝓞 E →+* RInt F E ⧸ Ideal.span {(N : RInt F E)} :=
  (Ideal.Quotient.mk _).comp (embO F E)

theorem one_tmul_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ intAd F) :
    (1 : E) ⊗ₜ[F] a ∈ RInt F E :=
  Subring.subset_closure (Set.mem_union_right _ ⟨⟨a, ha⟩, rfl⟩)

theorem mk_mem_range (N : ℕ) (hN : 0 < N) (z : RInt F E) :
    Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) z ∈ (redO F E N).range := by
  let T : Subring (RInt F E) := (redO F E N).range.comap (Ideal.Quotient.mk _)
  have hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have key : RInt F E ≤ T.map (RInt F E).subtype := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · exact ⟨embO F E o, ⟨o, rfl⟩, rfl⟩
    · obtain ⟨x, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 y hy
      refine ⟨embO F E (algebraMap (𝓞 F) (𝓞 E) x) + (N : RInt F E) * ⟨_, one_tmul_mem F E (a := a) ha⟩,
        ⟨algebraMap (𝓞 F) (𝓞 E) x, ?_⟩, ?_⟩
      · show redO F E N _ = Ideal.Quotient.mk _ _
        rw [map_add, map_mul, hN0, zero_mul, add_zero]
        rfl
      · show ((algebraMap F E (x : F)) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) + (N : AfE F E) * ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] y
        rw [e, TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F),
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
          TensorProduct.tmul_smul, nsmul_eq_mul]
  obtain ⟨w, hw, e⟩ := key z.2
  have : w = z := Subtype.ext e
  subst this
  exact hw

theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (RInt F E ⧸ Ideal.span {(N : RInt F E)}) := by
  haveI : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := by
    apply Ideal.finiteQuotientOfFreeOfNeBot
    simp [Ideal.span_singleton_eq_bot]; omega
  have hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  let φ : 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)} →+* RInt F E ⧸ Ideal.span {(N : RInt F E)} :=
    Ideal.Quotient.lift _ (redO F E N) fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : RInt F E)})), hN0, mul_zero]
  refine Finite.of_surjective φ fun q => ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨o, ho⟩ := mk_mem_range F E N hN z
  exact ⟨Ideal.Quotient.mk _ o, ho⟩

def toU : intU F E ≃* (RInt F E)ˣ := Submonoid.unitsEquivUnitsType (RInt F E).toSubmonoid

theorem exists_finset (N : ℕ) (hN : 0 < N) :
    ∃ S : Finset (AfE F E)ˣ, ∀ k ∈ intU F E, ∃ s ∈ S, s⁻¹ * k ∈ congN F E N := by
  classical
  haveI := finite_quot F E N hN
  let I := Ideal.span {(N : RInt F E)}
  let f : (AfE F E)ˣ → (RInt F E ⧸ I)ˣ := fun k =>
    if h : k ∈ intU F E then Units.map (Ideal.Quotient.mk I).toMonoidHom (toU F E ⟨k, h⟩) else 1
  let g : (RInt F E ⧸ I)ˣ → (AfE F E)ˣ := fun q =>
    if h : ∃ k ∈ intU F E, f k = q then h.choose else 1
  refine ⟨(Set.finite_range g).toFinset, fun k hk => ?_⟩
  have hex : ∃ k' ∈ intU F E, f k' = f k := ⟨k, hk, rfl⟩
  have hg : g (f k) = hex.choose := dif_pos hex
  obtain ⟨hs, hfs⟩ := hex.choose_spec
  refine ⟨g (f k), (Set.finite_range g).mem_toFinset.2 ⟨_, rfl⟩, ?_⟩
  rw [hg]
  set s := hex.choose
  refine ⟨(toU F E ⟨s, hs⟩)⁻¹ * toU F E ⟨k, hk⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    have h1 : f s = _ := dif_pos hs
    have h2 : f k = _ := dif_pos hk
    rw [← h1, ← h2, hfs]
  · ext
    simp only [map_mul, map_inv, Units.val_mul]
    rfl

end GlobalTheory.CongNIndex

theorem GlobalTheory.congN_finite_index : ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N →
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ k ∈ intU ℚ L, ∃ s ∈ S, s⁻¹ * k ∈ congN ℚ L N :=
  fun L _ _ N hN => GlobalTheory.CongNIndex.exists_finset ℚ L N hN
end
end

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_units_finite_cosets : ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N →
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ k ∈ intU ℚ L, ∃ s ∈ S, s⁻¹ * k ∈ congN ℚ L N := by
  atlas_forward_decl GlobalTheory.congN_finite_index
end

section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideles_finite_class_decomposition : ∀ (L : Type) [Field L] [NumberField L],
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ x : (AfE ℚ L)ˣ, ∃ s ∈ S, ∃ a : Lˣ, ∃ k ∈ intU ℚ L, x = s * ratId ℚ L a * k := by
  first | exact @GlobalTheory.ClassCover.exists_finset_cover | exact GlobalTheory.ClassCover.exists_finset_cover | (intros; apply GlobalTheory.ClassCover.exists_finset_cover <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

noncomputable section
namespace GlobalTheory.RatIdele

theorem exists_rat_mul_intUnit : ∀ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∃ (r : ℚˣ) (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
    (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧ ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧
    t = Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom r * u := by
  intro t
  obtain ⟨k, u, hu, he⟩ := GlobalTheory.TwV.Xc.ClsPow.exists_pow_eq_diag_mul t
  have hc : Fintype.card (ClassGroup (𝓞 ℚ)) = 1 := by
    have := Rat.classNumber_eq
    rwa [NumberField.classNumber] at this
  rw [hc, pow_one] at he
  have hinv : ∀ P : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) P) = 1 := by
    intro P
    have e : (((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) P) *
        ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) P) = 1 :=
      congrArg (fun s : FiniteAdeleRing (𝓞 ℚ) ℚ => s P) (Units.inv_mul u)
    have e2 := congrArg Valued.v e
    rw [map_mul, hu P, mul_one, map_one] at e2
    exact e2
  refine ⟨k, u, ?_, ?_, he⟩
  · intro P
    show (u : FiniteAdeleRing (𝓞 ℚ) ℚ) P ∈ P.adicCompletionIntegers ℚ
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu P]
  · intro P
    show ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) P ∈ P.adicCompletionIntegers ℚ
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hinv P]

end GlobalTheory.RatIdele
end
end

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_finite_idele_factorization : ∀ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∃ (r : ℚˣ) (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
    (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧ ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧
    t = Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom r * u := by
  atlas_forward_decl GlobalTheory.RatIdele.exists_rat_mul_intUnit
end

section
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

namespace GlobalTheory.RatIdInt

theorem mem_RInt_iff_isIntegral (L : Type) [Field L] [NumberField L] (x : L) :
    (x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ RInt ℚ L ↔ IsIntegral ℤ x := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv ℚ L
  constructor
  · intro hx
    have hv := (h2 _).1 hx
    rw [h1] at hv
    have hr : x ∈ (algebraMap (𝓞 L) L).range := by
      apply HeightOneSpectrum.mem_integers_of_valuation_le_one
      intro P
      have := hv P
      rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    obtain ⟨y, rfl⟩ := hr
    exact RingOfIntegers.isIntegral_coe y
  · intro hx
    apply Subring.subset_closure
    exact Or.inl ⟨⟨x, ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩

theorem ratId_mem_intU_iff : ∀ (L : Type) [Field L] [NumberField L] (a : Lˣ),
    ratId ℚ L a ∈ intU ℚ L ↔ IsIntegral ℤ (a : L) ∧ IsIntegral ℤ ((a⁻¹ : Lˣ) : L) := by
  intro L _ _ a
  rw [intU, Submonoid.mem_units_iff, ← map_inv]
  exact and_congr (mem_RInt_iff_isIntegral L (a : L)) (mem_RInt_iff_isIntegral L ((a⁻¹ : Lˣ) : L))

end GlobalTheory.RatIdInt
end

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_idele_integral_iff_unit : ∀ (L : Type) [Field L] [NumberField L] (a : Lˣ),
    ratId ℚ L a ∈ intU ℚ L ↔ IsIntegral ℤ (a : L) ∧ IsIntegral ℤ ((a⁻¹ : Lˣ) : L) := by
  atlas_forward_decl GlobalTheory.RatIdInt.ratId_mem_intU_iff
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_units_finitely_many_norms : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∃ S : Finset L, ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) → c ε = ε →
      ∃ f ∈ S, ∃ η : Lˣ, IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ (ε : L) = f * ((η : L) * c η) := by
  first | exact @GlobalTheory.units_fixed_eq_mul_mul_conj | exact GlobalTheory.units_fixed_eq_mul_mul_conj | (intros; apply GlobalTheory.units_fixed_eq_mul_mul_conj <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

namespace GlobalTheory.LKTorus

theorem cover_of_label {G : Type} [Group G] {ι : Type} (S : Finset ι) (T B : Subgroup G) (X : Set G)
    (lab : G → ι → Prop) (hlab : ∀ x ∈ X, x ∈ T → ∃ i ∈ S, lab x i)
    (hB : ∀ x y i, x ∈ X → y ∈ X → x ∈ T → y ∈ T → lab x i → lab y i → y⁻¹ * x ∈ B) :
    ∃ S' : Finset G, (∀ s ∈ S', s ∈ T) ∧ ∀ x ∈ X, x ∈ T → ∃ s ∈ S', s⁻¹ * x ∈ B ∧ s⁻¹ * x ∈ T := by
  classical
  let pick : ι → G := fun i => if h : ∃ y ∈ X, y ∈ T ∧ lab y i then h.choose else 1
  have hpick : ∀ i, (∃ y ∈ X, y ∈ T ∧ lab y i) → pick i ∈ X ∧ pick i ∈ T ∧ lab (pick i) i := by
    intro i h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  refine ⟨S.image pick, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    by_cases h : ∃ y ∈ X, y ∈ T ∧ lab y i
    · exact (hpick i h).2.1
    · simp only [pick, dif_neg h]; exact one_mem T
  · intro x hx hxT
    obtain ⟨i, hi, hl⟩ := hlab x hx hxT
    obtain ⟨h1, h2, h3⟩ := hpick i ⟨x, hx, hxT, hl⟩
    exact ⟨pick i, Finset.mem_image_of_mem _ hi, hB x (pick i) i hx h1 hxT h2 hl h3,
      mul_mem (inv_mem h2) hxT⟩

theorem finite_doubleCoset_of_involutive (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L)
    (hc : ∀ x, c (c x) = x) :
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ U : Subgroup (simTA L c), IsOpen (U : Set (simTA L c)) →
      Finite (DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c))) := by
  letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
  intro U hU
  classical

  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.1 hU
  have h1V : (1 : (AfE ℚ L)ˣ) ∈ V := by
    have h : (1 : simTA L c) ∈ (U : Set (simTA L c)) := one_mem U
    rw [← hVU] at h
    exact h
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.T.congruence_units_basis_of_nbhds L V hV h1V
  have hcongU : ∀ (x : (AfE ℚ L)ˣ) (hx : x ∈ simTA L c), x ∈ congN ℚ L N → (⟨x, hx⟩ : simTA L c) ∈ U := by
    intro x hx hxN
    have h : (⟨x, hx⟩ : simTA L c) ∈ Subtype.val ⁻¹' V := hNV x hxN
    rw [hVU] at h
    exact h

  obtain ⟨S₃, hS₃⟩ := GlobalTheory.T.ideles_finite_class_decomposition L
  let B1 : Subgroup (AfE ℚ L)ˣ := (ratId ℚ L).range ⊔ intU ℚ L
  obtain ⟨S₁, hS₁T, hS₁⟩ := cover_of_label S₃ (simTA L c) B1 Set.univ (fun x s => s⁻¹ * x ∈ B1)
    (fun x _ _ => by
      obtain ⟨s, hs, a, k, hk, rfl⟩ := hS₃ x
      refine ⟨s, hs, ?_⟩
      rw [mul_assoc, inv_mul_cancel_left]
      exact mul_mem (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right hk))
    (fun x y s _ _ _ _ hx hy => by
      have e : y⁻¹ * x = (s⁻¹ * y)⁻¹ * (s⁻¹ * x) := by group
      rw [e]
      exact mul_mem (inv_mem hy) hx)

  obtain ⟨S₆, hS₆⟩ := GlobalTheory.T.fixed_units_finitely_many_norms L c hc
  let B2 : Subgroup (AfE ℚ L)ˣ := (simT ℚ c).map (ratId ℚ L) ⊔ intU ℚ L
  let lab : (AfE ℚ L)ˣ → L → Prop := fun y f => ∃ (a : Lˣ) (k : (AfE ℚ L)ˣ) (r : ℚˣ) (η : Lˣ),
    k ∈ intU ℚ L ∧ IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ y = ratId ℚ L a * k ∧
      (a : L) * c a = algebraMap ℚ L r * (f * ((η : L) * c η))
  have hlab : ∀ y ∈ (B1 : Set (AfE ℚ L)ˣ), y ∈ simTA L c → ∃ f ∈ S₆, lab y f := by
    intro y hy hyT
    obtain ⟨z, ⟨a, rfl⟩, k, hk, rfl⟩ := Subgroup.mem_sup.1 hy
    obtain ⟨t, ht⟩ := hyT
    obtain ⟨r, u, hu1, hu2, rfl⟩ := GlobalTheory.T.rational_finite_idele_factorization t
    let ε : Lˣ := a * Units.map (c : L →+* L).toMonoidHom a * (Units.map (algebraMap ℚ L).toMonoidHom r)⁻¹
    have key : ratId ℚ L ε = idF ℚ L u * (k * conjId c k)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      have e1 : ratId ℚ L ε * (k * conjId c k) =
          (ratId ℚ L a * k * conjId c (ratId ℚ L a * k)) * (ratId ℚ L (Units.map (algebraMap ℚ L).toMonoidHom r))⁻¹ := by
        simp only [ε, map_mul, map_inv, conjId_ratId]
        simp only [mul_comm, mul_left_comm, mul_assoc]
      rw [e1, ht, map_mul, idF_map_algebraMap, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    have hεU : ratId ℚ L ε ∈ intU ℚ L := by
      rw [key]
      exact mul_mem (idF_mem_intU L hu1 hu2) (inv_mem (mul_mem hk (conjId_mem_intU L c hk)))
    obtain ⟨hε1, hε2⟩ := (GlobalTheory.T.principal_idele_integral_iff_unit L ε).1 hεU
    have hεc : c (ε : L) = ε := by
      simp only [ε, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
        RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_inv₀, hc,
        AlgHom.commutes]
      ring
    obtain ⟨f, hf, η, hη1, hη2, hεf⟩ := hS₆ ε hε1 hε2 hεc
    refine ⟨f, hf, a, k, r, η, hk, hη1, hη2, rfl, ?_⟩
    rw [← hεf]
    have hr : algebraMap ℚ L (r : ℚ) ≠ 0 := by simp
    simp only [ε, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    field_simp

  have hB : ∀ x y f, x ∈ (B1 : Set (AfE ℚ L)ˣ) → y ∈ (B1 : Set (AfE ℚ L)ˣ) → x ∈ simTA L c → y ∈ simTA L c →
      lab x f → lab y f → y⁻¹ * x ∈ B2 := by
    rintro x y f - - - - ⟨a, k, r, η, hk, hη1, hη2, rfl, ha⟩ ⟨a', k', r', η', hk', hη1', hη2', rfl, ha'⟩
    have hf : f ≠ 0 := by
      rintro rfl
      rw [zero_mul, mul_zero] at ha
      exact mul_ne_zero a.ne_zero ((map_ne_zero c).2 a.ne_zero) ha
    let b : Lˣ := a * a'⁻¹ * η' * η⁻¹
    have hb : b ∈ simT ℚ c := by
      refine ⟨r * r'⁻¹, ?_⟩
      have hη0 : (η : L) * c η ≠ 0 := mul_ne_zero η.ne_zero ((map_ne_zero c).2 η.ne_zero)
      have hη0' : (η' : L) * c η' ≠ 0 := mul_ne_zero η'.ne_zero ((map_ne_zero c).2 η'.ne_zero)
      have hr' : algebraMap ℚ L (r' : ℚ) ≠ 0 := by simp
      have e : (b : L) * c b = ((a : L) * c a) * ((a' : L) * c a')⁻¹ * ((η' : L) * c η') * ((η : L) * c η)⁻¹ := by
        simp only [b, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
        ring
      rw [e, ha, ha']
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
      field_simp
    have hab : a = b * (η * η'⁻¹) * a' := by
      apply Units.ext
      simp only [b, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    have hint : ratId ℚ L (η * η'⁻¹) ∈ intU ℚ L := by
      rw [GlobalTheory.T.principal_idele_integral_iff_unit]
      constructor
      · simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hη2' ⊢
        exact hη1.mul hη2'
      · simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hη2 ⊢
        exact hη1'.mul hη2
    have e2 : (ratId ℚ L a' * k')⁻¹ * (ratId ℚ L a * k) = ratId ℚ L b * (ratId ℚ L (η * η'⁻¹) * (k'⁻¹ * k)) := by
      rw [hab, map_mul, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e2]
    exact mul_mem (Subgroup.mem_sup_left ⟨b, hb, rfl⟩)
      (Subgroup.mem_sup_right (mul_mem hint (mul_mem (inv_mem hk') hk)))
  obtain ⟨S₂, hS₂T, hS₂⟩ := cover_of_label S₆ (simTA L c) B2 (B1 : Set (AfE ℚ L)ˣ) lab hlab hB

  obtain ⟨S₄, hS₄⟩ := GlobalTheory.T.integral_units_finite_cosets L N hN
  obtain ⟨S₅, hS₅T, hS₅⟩ := cover_of_label S₄ (simTA L c) (congN ℚ L N) (intU ℚ L : Set (AfE ℚ L)ˣ)
    (fun k s => s⁻¹ * k ∈ congN ℚ L N) (fun k hk _ => hS₄ k hk)
    (fun x y s _ _ _ _ hx hy => by
      have e : y⁻¹ * x = (s⁻¹ * y)⁻¹ * (s⁻¹ * x) := by group
      rw [e]
      exact mul_mem (inv_mem hy) hx)

  let rep : (S₁ × S₂ × S₅) → DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c)) :=
    fun p => DoubleCoset.mk (ratT L c) U ⟨p.1.1 * p.2.1.1 * p.2.2.1,
      mul_mem (mul_mem (hS₁T _ p.1.2) (hS₂T _ p.2.1.2)) (hS₅T _ p.2.2.2)⟩
  refine Finite.of_surjective rep ?_
  intro q
  induction q using Quotient.inductionOn' with
  | h x =>
  obtain ⟨x, hxT⟩ := x
  obtain ⟨s₁, hs₁, hy1, hyT⟩ := hS₁ x (Set.mem_univ _) hxT
  obtain ⟨s₂, hs₂, hz2, hzT⟩ := hS₂ _ hy1 hyT
  obtain ⟨γ, ⟨b, hb, rfl⟩, k, hk, hγk⟩ := Subgroup.mem_sup.1 hz2
  have hγT : ratId ℚ L b ∈ simTA L c := ratId_mem_simTA L c hb
  have hkT : k ∈ simTA L c := by
    have e : k = (ratId ℚ L b)⁻¹ * (s₂⁻¹ * (s₁⁻¹ * x)) := by rw [← hγk, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem hγT) hzT
  obtain ⟨s₅, hs₅, hw, hwT⟩ := hS₅ k hk hkT
  refine ⟨(⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩, ⟨s₅, hs₅⟩), ?_⟩
  show DoubleCoset.mk (ratT L c) U _ = DoubleCoset.mk (ratT L c) U _
  rw [DoubleCoset.eq]
  refine ⟨⟨ratId ℚ L b, hγT⟩, (Subgroup.mem_subgroupOf).2 ⟨b, hb, rfl⟩, ⟨s₅⁻¹ * k, hwT⟩, hcongU _ hwT hw, ?_⟩
  apply Subtype.ext
  have hx : x = s₁ * (s₂ * (ratId ℚ L b * k)) := by
    rw [hγk]
    group
  simp only [Subgroup.coe_mul]
  rw [hx]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem finite_doubleCoset (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L)
    (hc : ∀ (τ : L →+* ℂ) (x : L), τ (c x) = (starRingEnd ℂ) (τ x)) :
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ U : Subgroup (simTA L c), IsOpen (U : Set (simTA L c)) →
      Finite (DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c))) := by
  have hinv : ∀ x, c (c x) = x := by
    let τ : L →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := L)).toRingHom
    intro x
    apply τ.injective
    rw [hc, hc, Complex.conj_conj]
  exact finite_doubleCoset_of_involutive L c hinv

end GlobalTheory.LKTorus
end
end
