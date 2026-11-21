import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveSublatticesGenusDefiniteLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEmbeddedDataWithGivenFixedLattice
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantOrderCommonFixedLatticeEmbeddedDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIsometriesFixingSubspaceDefiniteLatticesLe
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexCongruenceSubgroupLeAbsNormPow
import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCMFieldOfStar

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem finrank_sub_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) L ≤ Module.finrank K V := by
  apply Module.finrank_le_of_rank_le
  apply rank_le
  intro s hs
  have h := hs.map' L.subtype (Submodule.ker_subtype L)
  rw [LinearIndependent.iff_fractionRing (R := 𝓞 K) (K := K)] at h
  simpa using h.fintype_card_le_finrank

theorem sublat_count {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG) (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.Finite ∧
      (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ) ≤
        (x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) L := inferInstance
  have : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K L x hx
  have hsub : {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x} ⊆
      (Submodule.map L.subtype) '' {N : Submodule (𝓞 K) L | N.toAddSubgroup.index = x} := by
    rintro N ⟨hN, hi⟩
    refine ⟨N.comap L.subtype, ?_, ?_⟩
    · exact hi
    · rw [Submodule.map_comap_subtype, inf_eq_right.2 hN]
  refine ⟨(h1.image _).subset hsub, ?_⟩
  have h3 := (Set.ncard_le_ncard hsub (h1.image _)).trans (Set.ncard_image_le h1)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x Module.finrank_pos hx
  have h5 : ((Module.finrank (𝓞 K) L : ℕ) : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast finrank_sub_le L
  calc (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ)
      ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ Module.finrank (𝓞 K) L := by
        exact_mod_cast h3.trans h2
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) L :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ (((Module.finrank (𝓞 K) L : ℕ) : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

theorem encard_isDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  intro K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x hx
  have hfib := GlobalTheory.DegCnt.DatCount.main K V H hK hP L₀ g j D₀ hL hD hG hg
  obtain ⟨hfin, hcnt⟩ := sublat_count L₀ hL.1.fg x hx
  set S := {N : Submodule (𝓞 K) V | N ≤ L₀ ∧ idx L₀ N = x} with hS
  have hsub : {d | IsDat H g L₀ j x d} ⊆
      ⋃ La ∈ hfin.toFinset, {d | IsDat H g L₀ j x d ∧ fixLat d.2 = La} := by
    intro d hd
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
    refine ⟨fixLat d.2, ⟨?_, hd.2.2.2.1⟩, hd, rfl⟩
    intro y hy
    exact (hd.2.2.1.1 hy).2
  have h1 := (Set.encard_le_encard hsub).trans (Finset.set_encard_biUnion_le _ _)
  have h2 : ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤
      ∑ La ∈ hfin.toFinset, ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) := by
    refine (ENat.toENNReal_le.2 h1).trans (le_of_eq ?_)
    exact map_sum ENat.toENNRealRingHom _ _
  refine h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun La _ => hfib La x).trans ?_)
  rw [nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  gcongr
  rw [← ENNReal.ofReal_natCast, ← Set.ncard_eq_toFinset_card S hfin]
  exact ENNReal.ofReal_le_ofReal hcnt

end GlobalTheory.DegCnt
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_embedded_hermData_index_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  atlas_forward_decl GlobalTheory.DegCnt.encard_isDat_le
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.PairNoFix

theorem encard_le_of_fibres {α β : Type} (S : Set α) (T : Set β) (f : α → β) (hf : ∀ a ∈ S, f a ∈ T)
    (c : ℝ≥0∞) (hc : ∀ b ∈ T, ((({a ∈ S | f a = b}).encard : ℕ∞) : ℝ≥0∞) ≤ c) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ ((T.encard : ℕ∞) : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const,
    ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun a : S => (⟨f a, hf a a.2⟩ : T))]
  refine ENNReal.tsum_le_tsum fun b => ?_
  rw [ENNReal.tsum_set_one]
  refine le_trans ?_ (hc b b.2)
  rw [← (Subtype.val_injective.encard_image _)]
  refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.2, congrArg Subtype.val ha⟩

theorem arith (k f : ℕ) (c e : ℝ) (hc : 0 ≤ c) (x x' D q A : ℝ) (hx : 1 ≤ x) (hx' : 1 ≤ x') (hD : 1 ≤ D)
    (hq : 0 < q) (hA : 0 ≤ A) (h : 1 ≤ q ^ (2 * k * f) * D * x * x') (m : ℕ) (hm : (m : ℝ) = e) :
    (x ^ ((k : ℝ) + c) * (x * D) ^ m) * (x' ^ ((k : ℝ) + c) * (x' * D) ^ m) * A ^ (4 * k * f) ≤
      (x * x') ^ ((k : ℝ) / 2) * (x * x' * D ^ 2) ^ (c + e) * (q ^ (k * f) * A ^ (4 * f) * D * x * x') ^ k := by
  subst hm
  have x0 : 0 < x := by linarith
  have x0' : 0 < x' := by linarith
  have D0 : 0 < D := by linarith
  have h1 : 1 ≤ (x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k := by
    have hs : ((x * x') ^ ((k : ℝ) / 2)) ^ 2 = (x * x') ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1; push_cast; ring
    have h2 : 1 ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) ^ 2 := by
      rw [mul_pow, hs]
      have : (x * x') ^ k * ((q ^ (k * f) * D) ^ k) ^ 2 = (q ^ (2 * k * f) * D * x * x') ^ k * D ^ k := by
        ring
      rw [this]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h) (one_le_pow₀ hD)
    exact (one_le_sq_iff₀ (by positivity)).1 h2
  have h3 : x ^ c * x' ^ c ≤ (x * x' * D ^ 2) ^ c := by
    rw [← Real.mul_rpow x0.le x0'.le]
    refine Real.rpow_le_rpow (by positivity) ?_ hc
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD)
  rw [Real.rpow_add x0, Real.rpow_add x0', Real.rpow_add (by positivity : 0 < x * x' * D ^ 2)]
  simp only [Real.rpow_natCast]
  calc x ^ k * x ^ c * (x * D) ^ m * (x' ^ k * x' ^ c * (x' * D) ^ m) * A ^ (4 * k * f)
      = 1 * (x ^ c * x' ^ c) * ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by ring
    _ ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) * (x * x' * D ^ 2) ^ c *
        ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by gcongr
    _ = _ := by ring

theorem main : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx'
  rcases Set.eq_empty_or_nonempty {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥} with he | ⟨p₀, hp₀, hfix⟩
  · rw [he]; simp
  have h43 := GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx' p₀ hp₀
  rw [hfix] at h43
  have hone : GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (⊥ : Submodule K V))
      (GlobalTheory.Mass.latIn ⊥ (fixLat p₀.1.2)) = 1 := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN
    rw [AddSubgroup.relIndex_eq_one]
    intro y _
    rw [Subsingleton.elim y 0]
    exact zero_mem _
  rw [hone, finrank_bot, Nat.sub_zero, Nat.cast_one] at h43
  have hD1 : 1 ≤ D₀ := by
    rcases Nat.eq_zero_or_pos D₀ with h | h
    · rw [h] at h43; norm_num at h43
    · exact h
  have hcf : 0 ≤ cf K := by
    unfold cf
    have : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    have := Real.logb_nonneg (b := 2) (by norm_num) this
    linarith
  have hA := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x hx
  have hB := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x' hx'
  have hcnt := encard_le_of_fibres {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}
    ({d | IsDat H g L₀ j x d} ×ˢ {d | IsDat H g L₀ j x' d}) (fun p => (p.1, p.2.1))
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    (((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)))
    (by
      rintro ⟨d, d'⟩ ⟨hd, hd'⟩
      have h := GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hPD ⊥ d'.1 d.1 hd'.1.1 hd.1.1
      rw [finrank_bot, Nat.sub_zero] at h
      refine le_trans (ENat.toENNReal_le.2 ?_) h
      refine Set.encard_le_encard_of_injOn (f := fun p => p.2.2) ?_ ?_
      · rintro ⟨a, b, η⟩ ⟨⟨hp, -⟩, he⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨hp.2.2.1, hp.2.2.2.1, ?_⟩
        intro y hy
        rw [(Submodule.mem_bot K).1 hy, map_zero]
      · rintro ⟨a, b, η⟩ ⟨-, he⟩ ⟨a', b', η'⟩ ⟨-, he'⟩ hη
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
        simp only at hη
        rw [hη])
  rw [Set.encard_prod, ENat.toENNReal_mul] at hcnt
  refine hcnt.trans ((mul_le_mul_left (mul_le_mul' hA hB) _).trans ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  exact arith _ _ _ _ hcf _ _ _ _ _ (by exact_mod_cast hx) (by exact_mod_cast hx') (by exact_mod_cast hD1)
    (by positivity) (by positivity) h43 _ (by push_cast; ring)

end GlobalTheory.PairNoFix
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairs_isometry_no_fixed_vector_count_bound : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  atlas_forward_decl GlobalTheory.PairNoFix.main
end

section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_embeddedData_with_given_fixedLattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (La : Submodule (𝓞 K) V) (x : ℕ), ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) ≤ ((x : ℝ≥0∞) * D₀) ^ (3 * (2 * j + 1)) := by
  first | exact @GlobalTheory.DegCnt.DatCount.main | exact GlobalTheory.DegCnt.DatCount.main | (intros; apply GlobalTheory.DegCnt.DatCount.main <;> assumption)
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem trip_fixLat_inf_eq_and_pairing : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by
  intro K V _ _ _ _ _ _ _ _ H _ _ L₀ g j D₀ _ _ _ _ x x' p hp
  obtain ⟨h1, -, -, -, h5⟩ := hp
  have hmem : ∀ (Γ : Submodule (𝓞 K) (V × V)) (y : V), y ∈ fixLat Γ ↔ (y, y) ∈ Γ := fun _ _ => Iff.rfl
  refine ⟨?_, ?_⟩
  · ext y
    have hf : y ∈ rs (𝓞 K) (fixSp p.2.2) ↔ p.2.2 y = y := by
      simp [fixSp, sub_eq_zero]
    rw [Submodule.mem_inf, Submodule.mem_inf, hmem, hmem, hf, h5]
    refine and_congr_left fun h => ?_
    rw [h]
  · intro y hy y' hy'
    rw [hmem] at hy hy'
    rw [h5] at hy'
    obtain ⟨t, ht⟩ := h1.2.2.1.2.2.2.2.2.2 _ hy _ hy'
    refine ⟨-t, ?_⟩
    simp only [map_mul, map_natCast] at ht
    rw [map_sub]
    have : ((-t : 𝓞 K) : K) = -(algebraMap (𝓞 K) K t) := map_neg (algebraMap (𝓞 K) K) t
    rw [this]
    linear_combination -ht

end GlobalTheory.DegCnt
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedLattice_inf_eq_and_pairing_of_isometry : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by
  atlas_forward_decl GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.TraceCount

theorem exists_gen_mod {R W : Type} [CommRing R] [IsDomain R] [AddCommGroup W] [Module R W] (C : Submodule R W)
    [Module.Finite R C] [Module.Projective R C] (m : ℕ) [Finite (R ⧸ Ideal.span {(m : R)})] :
    ∃ c : Fin (Module.finrank R C) → W, (∀ i, c i ∈ C) ∧
      ∀ y ∈ C, ∃ (r : Fin (Module.finrank R C) → R) (d : W), d ∈ C ∧ y = ∑ i, r i • c i + m • d := by
  obtain ⟨⟨v, hv⟩, -⟩ := GlobalTheory.CongIndex.quot_smul_top_span_card (R := R) (N := C) (Ideal.span {(m : R)})
  choose c hc using fun i => Submodule.Quotient.mk_surjective _ (v i)
  refine ⟨fun i => c i, fun i => (c i).2, fun y hy => ?_⟩
  have h1 : (Submodule.Quotient.mk ⟨y, hy⟩ : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) ∈
      Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h1
  have h2 : (Submodule.Quotient.mk (∑ i, r i • c i) : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) =
      Submodule.Quotient.mk ⟨y, hy⟩ := by
    rw [← hr, ← Submodule.mkQ_apply, map_sum]
    simp [hc]
  have h3 := (Submodule.Quotient.eq _).1 h2.symm
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨d, -, hd⟩ := h3
  refine ⟨r, d, d.2, ?_⟩
  have h4 := congrArg Subtype.val hd
  simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum, Nat.cast_smul_eq_nsmul] at h4
  rw [eq_sub_iff_add_eq] at h4
  rw [← h4, add_comm]
  simp

theorem fibre_count {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (L M : Submodule R V) (C : Submodule R W) (m s : ℕ)
    (hm : M.toAddSubgroup.relIndex (L ⊓ LinearMap.ker f).toAddSubgroup = m) (hm0 : m ≠ 0)
    (c : Fin s → W) (hc : ∀ i, c i ∈ C)
    (hgen : ∀ y ∈ C, ∃ (r : Fin s → R) (d : W), d ∈ C ∧ y = ∑ i, r i • c i + m • d) :
    {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M}.encard ≤ (m ^ s : ℕ) := by
  set S := {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  have hlift : ∀ La : S, ∀ y ∈ C, ∃ a ∈ La.1, f a = y := fun La y hy => by
    have : y ∈ La.1.map f := La.2.2.1.symm ▸ hy
    exact this
  choose a ha hfa using fun (La : S) (i : Fin s) => hlift La (c i) (hc i)
  set K₀ := (L ⊓ LinearMap.ker f).toAddSubgroup with hK₀
  have hmem : ∀ (La : S) i, a La i - a ⟨L₁, hL₁⟩ i ∈ K₀ := fun La i =>
    ⟨sub_mem (La.2.1 (ha La i)) (hL₁.1 (ha ⟨L₁, hL₁⟩ i)), by simp [hfa]⟩
  let Φ : S → (Fin s → K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := fun La i => QuotientAddGroup.mk ⟨_, hmem La i⟩
  have hle : ∀ La La' : S, Φ La = Φ La' → La.1 ≤ La'.1 := by
    intro La La' h y hy
    have hML : M ≤ La'.1 := La'.2.2.2 ▸ inf_le_left
    have h1 : ∀ i, a La i ∈ La'.1 := fun i => by
      have h2 := QuotientAddGroup.eq.1 (congrFun h i)
      rw [AddSubgroup.mem_addSubgroupOf] at h2
      have h3 : -(a La i - a ⟨L₁, hL₁⟩ i) + (a La' i - a ⟨L₁, hL₁⟩ i) ∈ La'.1 := hML h2
      have h4 := sub_mem (ha La' i) h3
      convert h4 using 1
      abel
    have hfy : f y ∈ C := La.2.2.1 ▸ Submodule.mem_map_of_mem hy
    obtain ⟨r, d, hd, hyd⟩ := hgen _ hfy
    obtain ⟨b, hb, hfb⟩ := hlift La d hd
    obtain ⟨b', hb', hfb'⟩ := hlift La' d hd
    have h5 : y - (∑ i, r i • a La i + m • b) ∈ M := by
      rw [← La.2.2.2]
      refine ⟨sub_mem hy (add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha La i))
        (nsmul_mem hb _)), ?_⟩
      simp [hfa, hfb, ← hyd]
    have h6 : m • (b - b') ∈ M := by
      have h7 : b - b' ∈ K₀ := ⟨sub_mem (La.2.1 hb) (La'.2.1 hb'), by simp [hfb, hfb']⟩
      have h8 := AddSubgroup.nsmul_index_mem (M.toAddSubgroup.addSubgroupOf K₀) ⟨_, h7⟩
      rw [AddSubgroup.mem_addSubgroupOf] at h8
      have h9 : (M.toAddSubgroup.addSubgroupOf K₀).index = m := hm
      rw [h9] at h8
      exact h8
    have h10 := add_mem (hML h5) (add_mem (Submodule.sum_mem _ fun i (_ : i ∈ Finset.univ) =>
      Submodule.smul_mem _ (r i) (h1 i)) (add_mem (hML h6) (nsmul_mem hb' m)))
    convert h10 using 1
    rw [smul_sub]
    abel
  have hΦ : Function.Injective Φ := fun La La' h => Subtype.ext (le_antisymm (hle _ _ h) (hle _ _ h.symm))
  have hcard : Nat.card (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) = m := hm
  have : Finite (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := Nat.finite_of_card_ne_zero (hcard ▸ hm0)
  have hfin : Finite S := Finite.of_injective Φ hΦ
  have h11 := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h11
  rw [← (Set.toFinite S).cast_ncard_eq]
  exact_mod_cast h11

theorem relIndex_eq_mul {V W : Type} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (A L : AddSubgroup V)
    (h : A ≤ L) : A.relIndex L = (A ⊓ f.ker).relIndex (L ⊓ f.ker) * (A.map f).relIndex (L.map f) := by
  have h1 := AddSubgroup.relIndex_mul_relIndex A (A ⊔ (L ⊓ f.ker)) L le_sup_left (sup_le h inf_le_left)
  rw [← h1, AddSubgroup.relIndex_sup_left, AddSubgroup.relIndex_map_map]
  congr 1
  · rw [← AddSubgroup.inf_relIndex_right A, ← AddSubgroup.inf_relIndex_right (A ⊓ f.ker), inf_assoc,
      inf_eq_right.2 (inf_le_right : L ⊓ f.ker ≤ f.ker)]
  · have h2 : L ⊔ f.ker = L ⊔ (A ⊔ f.ker) := by rw [← sup_assoc, sup_eq_left.2 h]
    rw [h2, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (A ⊔ f.ker), sup_inf_assoc_of_le _ h,
      inf_comm]

theorem encard_le_mul {α β : Type} (g : α → β) (S : Set α) (T : Set β) (hT : T.Finite) (k : ℕ)
    (hg : ∀ a ∈ S, g a ∈ T) (hk : ∀ b ∈ T, {a | a ∈ S ∧ g a = b}.encard ≤ k) :
    S.encard ≤ (T.ncard * k : ℕ) := by
  have hfin : S.Finite := by
    refine (hT.biUnion fun b hb => Set.finite_of_encard_le_coe (hk b hb)).subset fun a ha => ?_
    exact Set.mem_biUnion (hg a ha) ⟨ha, rfl⟩
  rw [← hfin.cast_ncard_eq, Nat.cast_le, Set.ncard_eq_toFinset_card _ hfin, Set.ncard_eq_toFinset_card _ hT,
    mul_comm]
  refine Finset.card_le_mul_card_image_of_maps_to (f := g) (fun a ha => by simpa using hg a (by simpa using ha)) k
    fun b hb => ?_
  have h1 := hk b (by simpa using hb)
  have h2 : {a | a ∈ S ∧ g a = b} = ((hfin.toFinset.filter fun a => g a = b : Finset α) : Set α) := by
    ext a; simp
  rw [h2, Set.encard_coe_eq_coe_finsetCard] at h1
  exact_mod_cast h1

theorem proj_rank {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) :
    Module.Finite (𝓞 K) C ∧ Module.Projective (𝓞 K) C ∧ Module.finrank (𝓞 K) C ≤ Module.finrank K W := by
  have : Module.Finite (𝓞 K) C := Module.Finite.iff_fg.2 hC
  have : Module.IsTorsionFree (𝓞 K) W := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K W
  have : Module.Flat (𝓞 K) C := inferInstance
  have : Module.FinitePresentation (𝓞 K) C := Module.finitePresentation_of_finite _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation,
    (GlobalTheory.CongIndex.finrank_le_finrank_span C).trans (Submodule.finrank_le _)⟩

theorem sub_count {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) (j : ℕ) (hj : 1 ≤ j) :
    {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.Finite ∧
    (({N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.ncard : ℕ) : ℝ) ≤
      (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ Module.finrank K W := by
  obtain ⟨h1, h2, h3⟩ := proj_rank C hC
  obtain ⟨h4, h5⟩ := Formalism.SLP.Final.submoduleIndexCountO K C j hj
  have h6 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) j Module.finrank_pos hj
  have hsub : {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j} ⊆
      (fun N : Submodule (𝓞 K) C => N.map C.subtype) '' {N | N.toAddSubgroup.index = j} := by
    rintro N ⟨hN, hNj⟩
    refine ⟨N.comap C.subtype, hNj, ?_⟩
    simp only [Submodule.map_comap_subtype]
    exact inf_eq_right.2 hN
  refine ⟨(h4.image _).subset hsub, ?_⟩
  have h7 := ((Set.ncard_le_ncard hsub (h4.image _)).trans (Set.ncard_image_le h4)).trans h5
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  calc _ ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList j).length * (j : ℝ) ^ Module.finrank (𝓞 K) C := by
        exact_mod_cast h7
    _ ≤ _ := mul_le_mul h6 (pow_le_pow_right₀ hj1 h3) (by positivity) (by positivity)

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L₀ M : Submodule (𝓞 K) V) (U : Submodule K V) (x : ℕ), Submodule.IsLattice K L₀ → 1 ≤ x → ((({La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) := by
  intro K V _ _ _ _ _ _ _ _ L₀ M U x hL hx
  set S := {La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  let f : V →ₗ[𝓞 K] (V ⧸ U) := U.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker f = rs (𝓞 K) U := by
    ext v
    simp [f]
  have hker' : f.toAddMonoidHom.ker = (LinearMap.ker f).toAddSubgroup := rfl
  set m := M.toAddSubgroup.relIndex (L₀ ⊓ LinearMap.ker f).toAddSubgroup with hm
  have hidx : ∀ La ∈ S, x = m * (La.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup := by
    intro La hLa
    have h1 := relIndex_eq_mul f.toAddMonoidHom La.toAddSubgroup L₀.toAddSubgroup hLa.1
    have h2 : La.toAddSubgroup.relIndex L₀.toAddSubgroup = x := hLa.2.1
    have h3 : La ⊓ LinearMap.ker f = M := hker ▸ hLa.2.2
    rw [← h2, h1, hm, ← h3]
    rfl
  set j := (L₁.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup with hj
  have hxj : x = m * j := hidx L₁ hL₁
  have hm0 : m ≠ 0 := fun h => by rw [h] at hxj; omega
  have hj0 : j ≠ 0 := fun h => by rw [h] at hxj; omega
  have hC : (L₀.map f).FG := (Submodule.IsLattice.fg (self := hL)).map f
  have hs : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U := by
    have := U.finrank_quotient_add_finrank
    omega
  set s := Module.finrank K V - Module.finrank K U with hsdef
  obtain ⟨hT, hTc⟩ := sub_count (L₀.map f) hC j (Nat.one_le_iff_ne_zero.2 hj0)
  rw [hs] at hTc
  have hfinq : Finite (𝓞 K ⧸ Ideal.span {(m : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hm0)
  have hcount := encard_le_mul (fun La : Submodule (𝓞 K) V => La.map f) S _ hT (m ^ s)
    (fun La hLa => ⟨Submodule.map_mono hLa.1,
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) ((hidx La hLa).symm.trans hxj)⟩)
    (fun N hN => by
      have hCf : Module.Finite (𝓞 K) (L₀.map f) := Module.Finite.iff_fg.2 hC
      have hNfg : N.FG := Submodule.FG.of_le_of_isNoetherian hN.1
      obtain ⟨h1, h2, h3⟩ := proj_rank N hNfg
      obtain ⟨c, hc, hgen⟩ := exists_gen_mod N m
      have h4 := fibre_count f L₀ M N m _ hm.symm hm0 c hc hgen
      refine le_trans (Set.encard_le_encard ?_) (h4.trans ?_)
      · rintro La ⟨hLa, hN'⟩
        exact ⟨hLa.1, hN', hker ▸ hLa.2.2⟩
      · exact_mod_cast Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm0) (hs ▸ h3))
  refine le_trans (ENat.toENNReal_le.2 hcount) ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hjx : (j : ℝ) ≤ x := by exact_mod_cast hxj ▸ Nat.le_mul_of_pos_left j (Nat.pos_of_ne_zero hm0)
  have hlog : 0 ≤ Real.logb 2 (Module.finrank ℚ K) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K))
  have hxr : (x : ℝ) = m * j := by exact_mod_cast hxj
  push_cast
  calc _ ≤ ((j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ s) * (m : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hTc (by positivity)
    _ = (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s := by rw [hxr, mul_pow]; ring
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hjx hlog) (by positivity)
    _ = (x : ℝ) ^ (Real.logb 2 (Module.finrank ℚ K) + (s : ℝ)) := by
        rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by
        have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
        unfold cf
        linarith)

end GlobalTheory.TraceCount
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_sublattices_index_fixed_trace_le : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L₀ M : Submodule (𝓞 K) V) (U : Submodule K V) (x : ℕ), Submodule.IsLattice K L₀ → 1 ≤ x → ((({La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) := by
  atlas_forward_decl GlobalTheory.TraceCount.main
end

section
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.FixedSpaceCount

theorem encard_le_mul {α β : Type*} (S : Set α) (T : Set β) (f : α → β) (a b : ℝ≥0∞)
    (hm : ∀ s ∈ S, f s ∈ T) (hT : ((T.encard : ℕ∞) : ℝ≥0∞) ≤ a)
    (hb : ∀ t ∈ T, ((({s ∈ S | f s = t}).encard : ℕ∞) : ℝ≥0∞) ≤ b) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ a * b := by
  have hS : S = ⋃ t : T, {s ∈ S | f s = t} := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨⟨f s, hm s h⟩, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  calc ((S.encard : ℕ∞) : ℝ≥0∞) = ∑' _ : (⋃ t : T, {s ∈ S | f s = t} : Set α), (1 : ℝ≥0∞) := by
        rw [← hS, ENNReal.tsum_set_one]
    _ ≤ ∑' t : T, ∑' _ : ({s ∈ S | f s = t} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_iUnion_le_tsum (fun _ => 1) _
    _ ≤ ∑' _ : T, b := ENNReal.tsum_le_tsum fun t => by
        rw [ENNReal.tsum_set_one]; exact hb t t.2
    _ = ((T.encard : ℕ∞) : ℝ≥0∞) * b := ENNReal.tsum_set_const _ _
    _ ≤ a * b := by gcongr

section

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] in

theorem finrank_le [NumberField K] (N : Submodule (𝓞 K) V) : Module.finrank (𝓞 K) N ≤ Module.finrank K V := by
  apply Module.finrank_le_of_rank_le
  rw [Module.finrank_eq_rank, IsLocalization.rank_eq K (𝓞 K)⁰ le_rfl]
  exact Submodule.rank_le N

theorem cf_nonneg (K : Type) [Field K] [NumberField K] : 0 ≤ cf K := by
  have h : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have := Real.logb_nonneg (b := 2) one_lt_two h
  unfold cf
  linarith

theorem sub_count [IsTotallyComplex K] (N : Submodule (𝓞 K) V) (hN : N.FG) (y : ℕ) (hy : 1 ≤ y) :
    ((({M : Submodule (𝓞 K) V | M ≤ N ∧ GlobalTheory.Mass.idxN N M = y}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((y : ℝ) ^ ((Module.finrank K V : ℝ) + cf K)) := by
  haveI : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.2 hN
  haveI : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  haveI : Module.Projective (𝓞 K) N := by
    haveI : Module.FinitePresentation (𝓞 K) N := Module.finitePresentation_of_finite _ _
    exact Module.Flat.projective_of_finitePresentation
  have hf : Module.finrank ℚ K = 2 * InfinitePlace.nrComplexPlaces K := IsTotallyComplex.finrank K
  obtain ⟨hfin, hc⟩ := Formalism.HermitianLatticeCounting.P.sublattice_count_alt K N _ y hf hy
  have h1 : ({M : Submodule (𝓞 K) V | M ≤ N ∧ GlobalTheory.Mass.idxN N M = y}).encard ≤
      ({M : Submodule (𝓞 K) N | M.toAddSubgroup.index = y}).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun M => M.comap N.subtype) ?_ ?_
    · rintro M ⟨-, h⟩
      exact h
    · rintro M ⟨h, -⟩ M' ⟨h', -⟩ e
      have := congrArg (Submodule.map N.subtype) e
      simpa [Submodule.map_comap_subtype, inf_eq_right.2 h, inf_eq_right.2 h'] using this
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal (hc.trans ?_)
  have e : (1 + Real.logb 2 (2 * (InfinitePlace.nrComplexPlaces K : ℝ))) = cf K := by
    unfold cf; rw [hf]; push_cast; rfl
  rw [e]
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hy) ?_
  have : (Module.finrank (𝓞 K) N : ℝ) ≤ Module.finrank K V := by exact_mod_cast finrank_le N
  linarith

omit [FiniteDimensional K V] in

theorem isLattice_of_idx {L M : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hM : M ≤ L)
    (h : idx L M ≠ 0) : Submodule.IsLattice K M := by
  refine ⟨?_, ?_⟩
  · haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL.fg
    exact Submodule.FG.of_le_of_isNoetherian hM
  · rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro v hv
    have h1 : idx L M • v ∈ M := AddSubgroup.nsmul_relIndex_mem M.toAddSubgroup (K := L.toAddSubgroup) hv
    have h2 : ((idx L M : K)⁻¹) • (idx L M • v) = v := by
      rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (by exact_mod_cast h), one_smul]
    rw [← h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

omit [FiniteDimensional K V] [NumberField K] in

theorem idx_latIn_le (U : Submodule K V) (L M : Submodule (𝓞 K) V) (h : idx L M ≠ 0) :
    GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) ≤ idx L M := by
  have e : GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) =
      (M.toAddSubgroup.comap U.subtype.toAddMonoidHom).relIndex
        (L.toAddSubgroup.comap U.subtype.toAddMonoidHom) := rfl
  rw [e, AddSubgroup.relIndex_comap]
  exact AddSubgroup.relIndex_le_of_le_right (AddSubgroup.map_comap_le _ _) h

omit [FiniteDimensional K V] [NumberField K] in

theorem inf_eq_map (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    M ⊓ rs (𝓞 K) U = (GlobalTheory.Mass.latIn U M).map (U.subtype.restrictScalars (𝓞 K)) := by
  ext v
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨v, h2⟩, h1, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.2⟩

variable [StarRing K]

omit [FiniteDimensional K V] in

theorem hRes_nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hP : GlobalTheory.Mass.PD h) (U : Submodule K V) :
    (GlobalTheory.Mass.hRes h U).Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x : U, GlobalTheory.Mass.hRes h U x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have := hP τ x (fun e => hne (Subtype.ext e))
    have e : h x x = 0 := hx
    rw [e] at this
    simp at this
  exact ⟨fun x hx => key x (hx x), fun x hx => key x (hx x)⟩

omit [FiniteDimensional K V] in

theorem fixLat_le {H : HermSpace K V} {g : ℕ} {L₀ : Submodule (𝓞 K) V} {j x : ℕ}
    {d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)} (hd : IsDat H g L₀ j x d) : fixLat d.2 ≤ L₀ :=
  fun _ hv => (hd.2.2.1.1 hv).2

theorem disc_trace (H : HermSpace K V) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hP : GlobalTheory.Mass.PD H.B.flip)
    {L M : Submodule (𝓞 K) V} (hL : GlobalTheory.Mass.IsIntLat H.B.flip L) (hM : M ≤ L) (h : idx L M ≠ 0)
    (U : Submodule K V) :
    GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) ≠ 0 ∧
    GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U M) =
      GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L) *
        GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) ^ 2 := by
  have hM' : GlobalTheory.Mass.IsIntLat H.B.flip M :=
    ⟨isLattice_of_idx hL.1 hM h, fun x hx y hy => hL.2 x (hM hx) y (hM hy)⟩
  have hs : (GlobalTheory.Mass.hRes H.B.flip U).IsSymm := ⟨fun x y => H.herm y x⟩
  exact (GlobalTheory.Mass.DiscOrder.main K U _ hK hs (hRes_nondeg _ hP U) _
    (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hM' U)).2.2.1 _ (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hL U)
    (Submodule.comap_mono hM)

theorem dat_count (H : HermSpace K V) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hP : GlobalTheory.Mass.PD H.B.flip)
    (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ) (hL : GlobalTheory.Mass.IsIntLat H.B.flip L₀)
    (hD : GlobalTheory.Mass.discN H.B.flip L₀ = D₀) (hG : GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1) (hg : 2 ≤ g)
    (x : ℕ) (hx : 1 ≤ x) (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) *
        ((x : ℝ≥0∞) * D₀) ^ (3 * (2 * j + 1)) := by
  haveI : IsTotallyComplex K := hK.1
  refine encard_le_mul _ _ (fun d => fixLat d.2) _ _ ?_ (GlobalTheory.T.encard_sublattices_index_fixed_trace_le K V L₀ M U x hL.1 hx) ?_
  · rintro d ⟨hd, hM⟩
    exact ⟨fixLat_le hd, hd.2.2.2.1, hM⟩
  · intro La _
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_))
      (GlobalTheory.T.card_embeddedData_with_given_fixedLattice K V H hK hP L₀ g j D₀ hL hD hG hg La x)
    rintro d ⟨⟨hd, -⟩, h⟩
    exact ⟨hd, h⟩

end

theorem pow_bound (A c : ℝ) (n y x x' u k : ℕ) (hn : 1 ≤ n) (hy : 1 ≤ y) (hx : y ≤ x) (hx' : 1 ≤ x')
    (hu : u ≤ k) (hc : 0 ≤ c) (hA : (n : ℝ) * (y : ℝ) ^ 2 ≤ A) :
    (y : ℝ) ^ ((u : ℝ) + c) ≤ (A / n) ^ ((k : ℝ) / 2) * ((x : ℝ) * x') ^ c := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1 : (y : ℝ) ≤ x := by exact_mod_cast hx
  have hx2 : (1 : ℝ) ≤ x' := by exact_mod_cast hx'
  rw [Real.rpow_add (by linarith)]
  have h1 : (y : ℝ) ^ (u : ℝ) ≤ (A / n) ^ ((k : ℝ) / 2) := by
    calc (y : ℝ) ^ (u : ℝ) ≤ (y : ℝ) ^ (k : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hy1 (by exact_mod_cast hu)
      _ = ((y : ℝ) ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          congr 1
          push_cast
          ring
      _ ≤ (A / n) ^ ((k : ℝ) / 2) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [le_div_iff₀ hn1]
          linarith
  have h2 : (y : ℝ) ^ c ≤ ((x : ℝ) * x') ^ c :=
    Real.rpow_le_rpow (by linarith) (by nlinarith) hc
  exact mul_le_mul h1 h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (y : ℝ) ^ (u : ℝ)).trans h1)

theorem prod_bound (B c : ℝ) (x x' D s e C : ℕ) (hB : 0 ≤ B) (hx : 1 ≤ x) (hx' : 1 ≤ x') :
    (x : ℝ≥0∞) * ENNReal.ofReal (B * ((x : ℝ) * x') ^ c) *
      (ENNReal.ofReal ((x : ℝ) ^ (2 * (s : ℝ) + c)) * ((x : ℝ≥0∞) * D) ^ e *
        (ENNReal.ofReal ((x' : ℝ) ^ (2 * (s : ℝ) + c)) * ((x' : ℝ≥0∞) * D) ^ e * (C : ℝ≥0∞) ^ C)) ≤
    ENNReal.ofReal (B * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * c + 1) * ((x : ℝ) * x' * (D : ℝ) ^ 2) ^ e *
      (C : ℝ) ^ C) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx2 : (1 : ℝ) ≤ x' := by exact_mod_cast hx'
  have e1 : ∀ a : ℕ, ((a : ℝ≥0∞) * D) ^ e = ENNReal.ofReal (((a : ℝ) * D) ^ e) := fun a => by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  have e2 : (C : ℝ≥0∞) ^ C = ENNReal.ofReal ((C : ℝ) ^ C) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  rw [e1, e1, e2, ← ENNReal.ofReal_natCast x, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e3 : ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * c + 1) =
      (x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c * ((x : ℝ) * x') := by
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_add (by positivity),
      ← Real.rpow_add_one (by positivity)]
    congr 1
    ring
  have e4 : ((x : ℝ) * x' * (D : ℝ) ^ 2) ^ e = ((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e := by
    rw [← mul_pow]; congr 1; ring
  rw [e3, e4]
  have h : (x : ℝ) ≤ x * x' := by nlinarith
  calc _ = (B * ((x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c) *
        (((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e) * (C : ℝ) ^ C) * x := by ring
    _ ≤ (B * ((x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c) *
        (((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e) * (C : ℝ) ^ C) * (x * x') := by gcongr
    _ = _ := by ring

theorem main : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' s n : ℕ) (U : Submodule K V), 1 ≤ x → 1 ≤ x' → 1 ≤ n → Module.finrank K U + s = (Module.finrank K V) → GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L₀) = n → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U}).encard : ℕ∞) : ℝ≥0∞) ≤ if (n : ℝ) ≤ (D₀ : ℝ) * x * x' then ENNReal.ofReal (((2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' / n) ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * cf K + 1) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (3 * (2 * j + 1)) * ((4 * s * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * s * (Formalism.HermitianLatticesTheory.fDeg K))) else 0 := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x x' s n U hx hx' hn hs hdisc
  haveI : IsTotallyComplex K := hK.1
  have hsub : Module.finrank K V - Module.finrank K U = s := by omega
  set A : ℝ := (2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' with hA
  set N := GlobalTheory.Mass.latIn U L₀ with hN
  have key : ∀ p ∈ {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U},
      GlobalTheory.Mass.latIn U (fixLat p.1.2) ≤ N ∧ 1 ≤ GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) ∧
      GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) ≤ x ∧
      (n : ℝ) * (GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) : ℝ) ^ 2 ≤ A := by
    rintro p ⟨hp, hU⟩
    have hi : idx L₀ (fixLat p.1.2) = x := hp.1.2.2.2.1
    have hi0 : idx L₀ (fixLat p.1.2) ≠ 0 := by omega
    obtain ⟨h1, h2⟩ := disc_trace H hK hP hL (fixLat_le hp.1) hi0 U
    have h3 := GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hP L₀ g j D₀ hL hD hG hg x x' hx hx' p hp
    rw [hU, hsub, h2, hdisc] at h3
    refine ⟨Submodule.comap_mono (fixLat_le hp.1), Nat.one_le_iff_ne_zero.2 h1,
      hi ▸ idx_latIn_le U _ _ hi0, ?_⟩
    push_cast at h3
    exact h3
  split_ifs with hcase
  · have hA0 : 0 ≤ A := by positivity
    refine le_trans ?_ (prod_bound ((A / n) ^ ((Module.finrank K V : ℝ) / 2)) (cf K) x x' D₀ s (3 * (2 * j + 1))
      (4 * s * Formalism.HermitianLatticesTheory.fDeg K) (by positivity) hx hx')
    refine encard_le_mul _ {M : Submodule (𝓞 K) U | M ≤ N ∧ 1 ≤ GlobalTheory.Mass.idxN N M ∧ GlobalTheory.Mass.idxN N M ≤ x ∧
      (n : ℝ) * (GlobalTheory.Mass.idxN N M : ℝ) ^ 2 ≤ A}
      (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) =>
        GlobalTheory.Mass.latIn U (fixLat p.1.2)) _ _ key ?_ ?_
    · refine encard_le_mul _ {y : ℕ | 1 ≤ y ∧ y ≤ x ∧ (n : ℝ) * (y : ℝ) ^ 2 ≤ A} (GlobalTheory.Mass.idxN N) _ _
        (fun M h => h.2) ?_ ?_
      · have h1 : {y : ℕ | 1 ≤ y ∧ y ≤ x ∧ (n : ℝ) * (y : ℝ) ^ 2 ≤ A} ⊆ (Finset.Icc 1 x : Finset ℕ) := by
          rintro y ⟨a, b, -⟩
          simp [a, b]
        refine (ENat.toENNReal_le.2 (Set.encard_le_encard h1)).trans ?_
        rw [Set.encard_coe_eq_coe_finsetCard]
        simp
      · rintro y ⟨a, b, c⟩
        have hfg : N.FG := (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hL U).1.fg
        refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) ((sub_count N hfg y a).trans
          (ENNReal.ofReal_le_ofReal (pow_bound A (cf K) n y x x' _ _ hn a b hx' (by omega) (cf_nonneg K) c)))
        rintro M ⟨h, e⟩
        exact ⟨h.1, e⟩
    · intro M _
      have c1 := dat_count H hK hP L₀ g j D₀ hL hD hG hg x hx U (M.map (U.subtype.restrictScalars (𝓞 K)))
      have c2 := dat_count H hK hP L₀ g j D₀ hL hD hG hg x' hx' U (M.map (U.subtype.restrictScalars (𝓞 K)))
      rw [hsub] at c1 c2
      refine encard_le_mul _ _ (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.1) _ _ ?_ c1 ?_
      · rintro p ⟨⟨hp, -⟩, e⟩
        exact ⟨hp.1, by rw [inf_eq_map, e]⟩
      intro d hd
      refine encard_le_mul _ _ (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.2.1) _ _ ?_ c2 ?_
      · rintro p ⟨⟨⟨hp, hU⟩, e⟩, -⟩
        have h42 := (GlobalTheory.T.fixedLattice_inf_eq_and_pairing_of_isometry K V H hK hP L₀ g j D₀ hL hD hG hg x x' p hp).1
        rw [hU] at h42
        exact ⟨hp.2.1, by rw [← h42, inf_eq_map, e]⟩
      intro d' hd'
      have c3 := GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hP U d'.1 d.1 hd'.1.1.1 hd.1.1.1
      rw [hsub] at c3
      refine le_trans (ENat.toENNReal_le.2 ?_) c3
      refine Set.encard_le_encard_of_injOn (f := fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.2.2) ?_ ?_
      · rintro p ⟨⟨⟨⟨hp, hU⟩, -⟩, e1⟩, e2⟩
        refine ⟨hp.2.2.1, by rw [← e1, ← e2]; exact hp.2.2.2.1, fun y hy => ?_⟩
        rw [← hU] at hy
        have : p.2.2 y - y = 0 := hy
        exact sub_eq_zero.1 this
      · rintro p ⟨⟨-, e1⟩, e2⟩ q ⟨⟨-, f1⟩, f2⟩ e
        exact Prod.ext (e1.trans f1.symm) (Prod.ext (e2.trans f2.symm) e)
  · have hempty : {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun p hp => hcase ?_
      obtain ⟨-, a, -, c⟩ := key p hp
      have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
      have h1 : (2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) ≤ 1 :=
        pow_le_one₀ (by positivity) ((div_le_one (by linarith)).2 hg')
      have h2 : A ≤ (D₀ : ℝ) * x * x' := by
        calc A ≤ 1 * D₀ * x * x' := by rw [hA]; gcongr
          _ = _ := by ring
      have a' : (1 : ℝ) ≤ (GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) : ℝ) ^ 2 :=
        one_le_pow₀ (by exact_mod_cast a)
      have h3 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    rw [hempty]
    simp

end GlobalTheory.DegCnt.FixedSpaceCount
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_isometry_pairs_with_given_fixed_space : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' s n : ℕ) (U : Submodule K V), 1 ≤ x → 1 ≤ x' → 1 ≤ n → Module.finrank K U + s = (Module.finrank K V) → GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L₀) = n → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U}).encard : ℕ∞) : ℝ≥0∞) ≤ if (n : ℝ) ≤ (D₀ : ℝ) * x * x' then ENNReal.ofReal (((2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' / n) ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * cf K + 1) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (3 * (2 * j + 1)) * ((4 * s * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * s * (Formalism.HermitianLatticesTheory.fDeg K))) else 0 := by
  atlas_forward_decl GlobalTheory.DegCnt.FixedSpaceCount.main
end

section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PairMean

section Cyclic

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

def GoodAt (A B : Submodule R W) (P : Ideal R) (v : W) : Prop :=
  ∀ b ∈ B, ∃ s, s ∉ P ∧ ∃ r : R, s • b - r • v ∈ A

theorem goodAt_comb {A B : Submodule R W} {P : Ideal R} (hP : P.IsPrime) {v w : W} {e e' : R}
    (hw : GoodAt A B P w) (hv : v ∈ B) (he : e ∈ P) (he' : e' ∉ P) : GoodAt A B P (e • v + e' • w) := by
  intro b hb
  obtain ⟨s, hs, r, h⟩ := hw v hv
  obtain ⟨s', hs', r', h'⟩ := hw b hb
  refine ⟨(e * r + s * e') * s', fun hm => ?_, r' * s, ?_⟩
  · rcases hP.mem_or_mem hm with h1 | h1
    · have : s * e' ∈ P := by simpa using P.sub_mem h1 (P.mul_mem_right r he)
      exact (hP.mem_or_mem this).elim hs he'
    · exact hs' h1
  · have := A.sub_mem (A.smul_mem (e * r + s * e') h') (A.smul_mem (r' * e) h)
    convert this using 1
    module

theorem exists_goodAt {A B : Submodule R W} (S : Finset (Ideal R)) (hS : ∀ P ∈ S, P.IsMaximal)
    (h : ∀ P ∈ S, ∃ v ∈ B, GoodAt A B P v) : ∃ v ∈ B, ∀ P ∈ S, GoodAt A B P v := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, B.zero_mem, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨v, hv, hg⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
      (fun Q hQ => h Q (Finset.mem_insert_of_mem hQ))
    obtain ⟨w, hw, hgw⟩ := h P (Finset.mem_insert_self _ _)
    have hP := hS P (Finset.mem_insert_self _ _)
    have hn : ¬ S.inf id ≤ P := by
      rw [hP.isPrime.inf_le']
      rintro ⟨Q, hQ, hle⟩
      have := (hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hle
      exact hPS (this ▸ hQ)
    obtain ⟨y, hy, hyP⟩ := SetLike.not_le_iff_exists.1 hn
    obtain ⟨a, e, he, hae⟩ := hP.exists_inv hyP
    refine ⟨e • v + (a * y) • w, B.add_mem (B.smul_mem _ hv) (B.smul_mem _ hw), fun Q hQ => ?_⟩
    rcases Finset.mem_insert.1 hQ with rfl | hQ'
    · refine goodAt_comb hP.isPrime hgw hv he fun hm => hP.ne_top ?_
      rw [Ideal.eq_top_iff_one, ← hae]
      exact Q.add_mem hm he
    · have hyQ : a * y ∈ Q := Q.mul_mem_left a (Finset.inf_le (f := id) hQ' hy)
      rw [add_comm]
      refine goodAt_comb (hS Q hQ).isPrime (hg Q hQ') hw hyQ fun hm => (hS Q hQ).ne_top ?_
      rw [Ideal.eq_top_iff_one, ← hae]
      exact Q.add_mem hyQ hm

theorem cyclic_of_local [IsDedekindDomain R] {A B : Submodule R W} (hAB : A ≤ B) (c : R) (hc : c ≠ 0)
    (hcB : ∀ b ∈ B, c • b ∈ A) (h : ∀ P : Ideal R, P.IsMaximal → ∃ v ∈ B, GoodAt A B P v) :
    ∃ v, B = A ⊔ Submodule.span R {v} := by
  have h0 : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨v, hv, hg⟩ := exists_goodAt (A := A) (B := B)
    ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {c})).toFinset.filter fun P => P.IsMaximal)
    (fun P hP => (Finset.mem_filter.1 hP).2) (fun P hP => h P (Finset.mem_filter.1 hP).2)
  refine ⟨v, le_antisymm (fun b hb => ?_) (sup_le hAB ((Submodule.span_singleton_le_iff_mem _ _).2 hv))⟩
  let I : Ideal R := (A ⊔ Submodule.span R {v}).comap (LinearMap.toSpanSingleton R W b)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hne
    have hcP : c ∈ P := hle (Submodule.mem_sup_left (hcB b hb))
    obtain ⟨s, hs, r, hr⟩ := hg P (Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2
      ((Ideal.mem_normalizedFactors_iff h0).2 ⟨hP.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hcP⟩), hP⟩) b hb
    refine hs (hle ?_)
    change s • b ∈ A ⊔ Submodule.span R {v}
    rw [← sub_add_cancel (s • b) (r • v)]
    exact Submodule.add_mem_sup hr (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  have : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using this

end Cyclic

section Lat

open Formalism.HermitianLatticesTheory GlobalTheory.Mass

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem genBy_of_genus (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) {M N : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) (hN : N ∈ genus h M) (hNd : N ≤ Formalism.HermitianLatticesTheory.dual h N) (h0 : discN h N ≠ 0)
    (t : V) (ht : t ∈ Formalism.HermitianLatticesTheory.dual h M) (htM : ∀ y ∈ Formalism.HermitianLatticesTheory.dual h M, ∃ r : 𝓞 K, y - r • t ∈ M) :
    GenBy (Formalism.HermitianLatticesTheory.dual h N) N 1 := by
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨v, hv⟩ := cyclic_of_local hNd (discN h N : 𝓞 K) (by exact_mod_cast h0) (fun x hx => by
      rw [Nat.cast_smul_eq_nsmul]
      exact AddSubgroup.nsmul_index_mem
        (H := N.toAddSubgroup.addSubgroupOf (Formalism.HermitianLatticesTheory.dual h N).toAddSubgroup) ⟨x, hx⟩) (fun P hP => by
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    have hle := locBasic_hcompl_le (K := K) P
    have key : ∀ A B : Submodule (𝓞 K) V, gmap g (loc (K := K) P A) = loc (K := K) P B →
        gmap g (locS P.primeCompl A) = locS P.primeCompl B := by
      intro A B e
      rw [← genusCovol_locS_locS hle A, gmap_locS_comm]
      change locS P.primeCompl (gmap g (loc (K := K) P A)) = _
      rw [e]
      exact genusCovol_locS_locS hle B
    obtain ⟨a1, a2, -, -, a5⟩ := isomAct (𝓞 K) K V h g hg M
    have b1 := (ld (gmap g M) (a5.2 hM).fg).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    have k1 := key _ _ hgL
    have k2 := key (Formalism.HermitianLatticesTheory.dual h M) (Formalism.HermitianLatticesTheory.dual h N) (by
      rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (Formalism.HermitianLatticesTheory.dual h M)).2.1 P])
    have up : ∀ (A : Submodule (𝓞 K) V) x, x ∈ A → x ∈ locS P.primeCompl A :=
      fun A x hx => ⟨1, one_mem _, by rwa [one_smul]⟩
    obtain ⟨s₀, hs₀, hv⟩ : g t ∈ locS P.primeCompl (Formalism.HermitianLatticesTheory.dual h N) := k2 ▸ ⟨t, up _ _ ht, rfl⟩
    refine ⟨_, hv, fun b hb => ?_⟩
    obtain ⟨y, ⟨s, hs, hy⟩, hyb⟩ : b ∈ gmap g (locS P.primeCompl (Formalism.HermitianLatticesTheory.dual h M)) := k2 ▸ up _ _ hb
    obtain ⟨r, hr⟩ := htM _ hy
    obtain ⟨s', hs', ha⟩ : ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) (s • y - r • t) ∈ locS P.primeCompl N :=
      k1 ▸ ⟨_, up _ _ hr, rfl⟩
    refine ⟨s₀ * s' * s, mul_mem (mul_mem hs₀ hs') hs, s' * r, ?_⟩
    rw [map_sub, map_smul, map_smul, hyb] at ha
    have := N.smul_mem s₀ ha
    convert this using 1
    change _ = s₀ • s' • (s • b - r • g t)
    module)
  exact ⟨{v}, by simp, by simpa using hv⟩

omit [NumberField K] in
theorem discN_top (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    discN (hRes h ⊤) (latIn ⊤ L) = discN h L := by
  have e : Formalism.HermitianLatticesTheory.dual (hRes h ⊤) (latIn ⊤ L) = latIn ⊤ (Formalism.HermitianLatticesTheory.dual h L) := by
    ext x
    change _ ↔ (x : V) ∈ Formalism.HermitianLatticesTheory.dual h L
    rw [isomAct_mem_dual, isomAct_mem_dual]
    exact ⟨fun a y hy => a ⟨y, trivial⟩ hy, fun a y hy => a y hy⟩
  unfold discN
  rw [e]
  let f : (⊤ : Submodule K V) →+ V := ((⊤ : Submodule K V).subtype : (⊤ : Submodule K V) →+ V)
  change (L.toAddSubgroup.comap f).relIndex ((Formalism.HermitianLatticesTheory.dual h L).toAddSubgroup.comap f) = _
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective (fun y => ⟨⟨y, trivial⟩, rfl⟩)]
  rfl

theorem isIntLat_latIn (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : IsIntLat h L)
    (U : Submodule K V) : IsIntLat (hRes h U) (latIn U L) := by
  refine ⟨⟨?_, ?_⟩, fun x hx y hy => hL.2 x hx y hy⟩
  · apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype
    exact hL.1.fg.of_le (Submodule.map_comap_le _ _)
  · refine eq_top_iff.mpr fun x _ => ?_
    have hx : (x : V) ∈ Submodule.span K (L : Set V) := by rw [hL.1.span_eq_top]; trivial
    obtain ⟨a, hax⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx
    rw [Submodule.span_eq] at hax
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using nonZeroDivisors.coe_ne_zero a
    rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
    exact Submodule.subset_span hax

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem pd_nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  constructor <;>
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

theorem discN_res_ne_zero [FiniteDimensional K V] (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (hp : PD h) {L : Submodule (𝓞 K) V} (hL : IsIntLat h L) (U : Submodule K V) :
    discN (hRes h U) (latIn U L) ≠ 0 :=
  (GlobalTheory.Mass.DiscOrder.main K U (hRes h U) hK ⟨fun x y => hs.eq (x : V) (y : V)⟩
    (pd_nondeg _ fun τ x hx => hp τ (x : V) (fun e => hx (Subtype.ext e))) _ (isIntLat_latIn h hL U)).1

theorem of_equiv (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (T : ℕ)
    (e : (↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) :
    discN h L = T ^ Module.finrank ℚ K ∧
      ∃ t ∈ Formalism.HermitianLatticesTheory.dual h L, ∀ y ∈ Formalism.HermitianLatticesTheory.dual h L, ∃ r : 𝓞 K, y - r • t ∈ L := by
  constructor
  · unfold discN
    rw [GlobalTheory.Mass.DiscOrder.idxN_eq_card, Nat.card_congr e.toEquiv, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  · obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    refine ⟨t, t.2, fun y hy => ?_⟩
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨y, hy⟩))
    refine ⟨r, ?_⟩
    have : (Submodule.Quotient.mk ⟨y, hy⟩ : ↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) =
        Submodule.Quotient.mk (r • t) := by
      rw [Submodule.Quotient.mk_smul, ht, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, hr,
        LinearEquiv.symm_apply_apply]
    have h2 := (Submodule.Quotient.eq _).1 this
    exact h2

end Lat

section Count

theorem encard_fibres_le {α β : Type} (S : Set α) (φ : α → β) (P : Set β) (B : ℝ≥0∞)
    (h : ∀ U ∈ P, ((({p ∈ S | φ p = U}).encard : ℕ∞) : ℝ≥0∞) ≤ B) :
    ((({p ∈ S | φ p ∈ P}).encard : ℕ∞) : ℝ≥0∞) ≤ ((P.encard : ℕ∞) : ℝ≥0∞) * B := by
  have e : {p ∈ S | φ p ∈ P} = ⋃ U ∈ P, {p ∈ S | φ p = U} := by
    ext p
    simp [and_comm]
  rw [e, ← ENNReal.tsum_set_one, ← ENNReal.tsum_set_const]
  refine (ENNReal.tsum_biUnion_le_tsum (fun _ => 1) _ _).trans (ENNReal.tsum_le_tsum fun U => ?_)
  rw [ENNReal.tsum_set_one]
  exact h U U.2

theorem encard_cover_le {α ι : Type} (S A₁ A₂ : Set α) (I : Finset ι) (F : ι → Set α)
    (h : S ⊆ A₁ ∪ A₂ ∪ ⋃ i ∈ I, F i) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ (A₁.encard : ℕ∞) + (A₂.encard : ℕ∞) + ∑ i ∈ I, (((F i).encard : ℕ∞) : ℝ≥0∞) := by
  have h1 : S.encard ≤ A₁.encard + A₂.encard + (⋃ i ∈ I, F i).encard :=
    (Set.encard_le_encard h).trans ((Set.encard_union_le _ _).trans (by
      gcongr; exact Set.encard_union_le _ _))
  have h2 : (((⋃ i ∈ I, F i).encard : ℕ∞) : ℝ≥0∞) ≤ ∑ i ∈ I, (((F i).encard : ℕ∞) : ℝ≥0∞) := by
    simp only [← ENNReal.tsum_set_one]
    exact ENNReal.tsum_biUnion_le (fun _ => 1) I F
  calc ((S.encard : ℕ∞) : ℝ≥0∞) ≤ (A₁.encard : ℕ∞) + (A₂.encard : ℕ∞) + ((⋃ i ∈ I, F i).encard : ℕ∞) := by
        exact_mod_cast h1
    _ ≤ _ := by gcongr

theorem orbSum_le_lin {G α ι : Type} [Group G] [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) (c : ℝ≥0∞)
    (I : Finset ι) (M : ι → α → ℝ≥0∞) (B : ι → ℝ≥0∞) (h : ∀ a ∈ X, N a ≤ c + ∑ i ∈ I, M i a * B i) :
    GlobalTheory.Mass.orbSum G X N ≤ GlobalTheory.Mass.orbMass G X * c + ∑ i ∈ I, GlobalTheory.Mass.orbSum G X (M i) * B i := by
  unfold GlobalTheory.Mass.orbMass GlobalTheory.Mass.orbSum
  simp only [← ENNReal.tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  refine (mul_le_mul_right (h _ q.2) _).trans (le_of_eq ?_)
  simp only [mul_add, Finset.mul_sum, mul_one, mul_assoc]

end Count

theorem mid_bound (m A c D X Y : ℝ) (g n s k f j x x' : ℕ) (hm : 0 ≤ m) (hA : 0 ≤ A) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hX : X = (x : ℝ) * x') (hX1 : 1 ≤ X) (hY : Y = X * D ^ 2) (hg : 2 ≤ g) (hn : 1 ≤ n) (hnD : (n : ℝ) ≤ D * X)
    (hs : s ≤ k) :
    m * (A * 16 ^ (s * k * f)) * ((n : ℝ) / D) ^ ((k : ℝ) / 2) * ((n : ℝ) * D) ^ (5 * (s : ℝ) + 5 + 2 * c) *
      (((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) ^ ((k : ℝ) / 2) * X ^ (2 * (s : ℝ) + 2 * c + 1) *
        Y ^ (3 * (2 * j + 1)) * ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f)) ≤
    m * X ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A *
      ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s := by
  have n0 : (0 : ℝ) < n := by exact_mod_cast hn
  have g0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have D0 : 0 < D := by linarith
  have X0 : 0 < X := by linarith
  have hXY : X ≤ Y := by rw [hY]; exact le_mul_of_one_le_right X0.le (one_le_pow₀ hD)
  have Y0 : 0 < Y := by linarith
  have e1 : ((n : ℝ) / D) ^ ((k : ℝ) / 2) * ((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) ^ ((k : ℝ) / 2) =
      (2 / (g : ℝ)) ^ (s * k * f) * X ^ ((k : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : (n : ℝ) / D * ((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) = (2 / (g : ℝ)) ^ (2 * s * f) * X := by
      rw [hX]; field_simp
    rw [this, Real.mul_rpow (by positivity) X0.le, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast]
    congr 2
    push_cast
    ring
  have b1 : ((n : ℝ) * D) ^ (5 * (s : ℝ) + 5 + 2 * c) ≤ Y ^ (5 * (s : ℝ) + 5 + 2 * c) :=
    Real.rpow_le_rpow (by positivity) (by rw [hY]; nlinarith) (by positivity)
  have b2 : X ^ (2 * (s : ℝ) + 2 * c + 1) ≤ Y ^ (2 * (s : ℝ) + 2 * c + 1) :=
    Real.rpow_le_rpow X0.le hXY (by positivity)
  have b3 : ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) := by gcongr
  have e2 : Y ^ (5 * (s : ℝ) + 5 + 2 * c) * Y ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1)) =
      Y ^ (6 * (j : ℝ) + 9 + 4 * c) * (Y ^ 7) ^ s := by
    rw [← pow_mul, ← Real.rpow_natCast Y (3 * _), ← Real.rpow_natCast Y (7 * _), ← Real.rpow_add Y0,
      ← Real.rpow_add Y0, ← Real.rpow_add Y0]
    congr 1
    push_cast
    ring
  have e3 : (16 : ℝ) ^ (s * k * f) * (2 / (g : ℝ)) ^ (s * k * f) = ((32 / (g : ℝ)) ^ (k * f)) ^ s := by
    rw [← mul_pow, ← pow_mul]
    congr 1 <;> ring
  have e4 : ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) = (((4 * k * f : ℕ) : ℝ) ^ (4 * f)) ^ s := by
    rw [← pow_mul]; congr 1; ring
  calc _ = m * A * 16 ^ (s * k * f) * (((n : ℝ) / D) ^ ((k : ℝ) / 2) *
        ((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) ^ ((k : ℝ) / 2)) *
        (((n : ℝ) * D) ^ (5 * (s : ℝ) + 5 + 2 * c) * X ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1))) *
        ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f) := by ring
    _ ≤ m * A * 16 ^ (s * k * f) * ((2 / (g : ℝ)) ^ (s * k * f) * X ^ ((k : ℝ) / 2)) *
        (Y ^ (5 * (s : ℝ) + 5 + 2 * c) * Y ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1))) *
        ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) := by rw [e1]; gcongr
    _ = m * X ^ ((k : ℝ) / 2) * A * ((16 : ℝ) ^ (s * k * f) * (2 / (g : ℝ)) ^ (s * k * f)) *
        (Y ^ (5 * (s : ℝ) + 5 + 2 * c) * Y ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1))) *
        ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) := by ring
    _ = _ := by rw [e2, e3, e4, mul_pow, mul_pow]; ring

theorem top_bound (c D X Y : ℝ) (g k f j x x' : ℕ) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hX : X = (x : ℝ) * x') (hX1 : 1 ≤ X) (hY : Y = X * D ^ 2) :
    ((2 / (g : ℝ)) ^ (2 * 0 * f) * D * x * x' / D) ^ ((k : ℝ) / 2) * X ^ (2 * ((0 : ℕ) : ℝ) + 2 * c + 1) *
        Y ^ (3 * (2 * j + 1)) * ((4 * 0 * f : ℕ) : ℝ) ^ (4 * 0 * f) ≤
      X ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * c) := by
  have D0 : 0 < D := by linarith
  have X0 : 0 < X := by linarith
  have hXY : X ≤ Y := by rw [hY]; exact le_mul_of_one_le_right X0.le (one_le_pow₀ hD)
  have Y0 : 0 < Y := by linarith
  have e : (2 / (g : ℝ)) ^ (2 * 0 * f) * D * x * x' / D = X := by rw [hX]; simp; field_simp
  rw [e]
  simp only [mul_zero, zero_mul, pow_zero, mul_one, Nat.cast_zero, zero_add, mul_assoc]
  gcongr
  calc _ ≤ Y ^ (2 * c + 1) * Y ^ (3 * (2 * j + 1)) := by gcongr
    _ = Y ^ (2 * c + 1 + (3 * (2 * j + 1) : ℕ)) := by rw [Real.rpow_add Y0 (2 * c + 1), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)

set_option maxHeartbeats 800000 in

theorem main : MinkowskiBound → GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → GlobalTheory.Mass.PD H.B.flip → 3 ≤ (Module.finrank K V) → ∀ (T : ℕ) (L₀ : Submodule (𝓞 K) V) (Mb : ℝ), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → GlobalTheory.Mass.IsIntLat H.B.flip L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual H.B.flip L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual H.B.flip L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → Mb = (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) → ∀ D₀ : ℝ, D₀ = (T : ℝ) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K)) → ∀ (g j x x' : ℕ) (Y : ℝ), 2 ≤ g → 1 ≤ x → 1 ≤ x' → Y = (x : ℝ) * x' * D₀ ^ 2 → GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) (fun L => (((Trip H g L j x x').encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L₀ * ((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * cf K) * (1 + Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * (∑ s ∈ Finset.Ico 1 (Module.finrank K V), ((32 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * Y ^ 7) ^ s) + ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V))) := by
  intro hMk hMax hSi K V _ _ _ _ _ _ _ _ H hK hO hv hpd hk T L₀ Mb hT hTP hL₀ he hMb D₀ hD₀ g j x x' Y hg hx hx' hY
  have hSC := GlobalTheory.T.mean_primitiveSublattices_genus_definiteLattice hMax hSi K V H hK hO hv hpd hk T L₀ Mb hT hTP hL₀ he hMb D₀ hD₀
  obtain ⟨e⟩ := he
  have hs := flip_isSymm H
  have hnd := pd_nondeg _ hpd
  obtain ⟨hd, t, ht, htM⟩ := of_equiv _ L₀ T e
  rw [(GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex K hK.1).1] at hd
  obtain ⟨hmass, hm0, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V H.B.flip hK hs hpd L₀ hL₀.1
  have hgen := (GlobalTheory.Mass.DiscOrder.main K V H.B.flip hK hs hnd L₀ hL₀).2.2.2.1
  set k := Module.finrank K V with hkdef
  set f := Formalism.HermitianLatticesTheory.fDeg K with hf
  set m := Formalism.HermitianLatticesTheory.mass H.B.flip L₀ with hm
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = T ^ (2 * f) := ⟨_, rfl⟩
  rw [← hD] at hd
  have hDD : D₀ = D := by rw [hD₀, hD]; push_cast; rfl
  have hD1 : 1 ≤ D := by rw [hD]; exact Nat.one_le_pow _ _ hT.pos
  subst hDD
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hc : 0 ≤ cf K := add_nonneg zero_le_one (Real.logb_nonneg one_lt_two (by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)))
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  have hA : 0 ≤ Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f := by positivity
  have hX1 : (1 : ℝ) ≤ (x : ℝ) * x' := by exact_mod_cast Nat.mul_pos hx hx'
  have hY1 : (D : ℝ) * ((x : ℝ) * x') ≤ Y := by rw [hY]; nlinarith [mul_nonneg (sub_nonneg.2 hX1) (sub_nonneg.2 hD1')]
  have hY2 : 1 ≤ Y := le_trans (one_le_mul_of_one_le_of_one_le hD1' hX1) hY1
  have Y0 : 0 < Y := by linarith
  set c := cf K with hcdef
  set Z := ((x : ℝ) * x') ^ ((k : ℝ) / 2) with hZ
  have Z0 : 0 ≤ Z := by positivity
  set Pk := ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D * x * x') ^ k with hPk
  have Pk0 : 0 ≤ Pk := by positivity
  let I : Finset (ℕ × ℕ) := Finset.Ico 1 k ×ˢ Finset.Icc 1 (D * x * x')
  let B : ℕ × ℕ → ℝ := fun i => ((2 / (g : ℝ)) ^ (2 * i.1 * f) * D * x * x' / i.2) ^ ((k : ℝ) / 2) *
    ((x : ℝ) * x') ^ (2 * (i.1 : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1)) * ((4 * i.1 * f : ℕ) : ℝ) ^ (4 * i.1 * f)
  have h1 := orbSum_le_lin (G := Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀)
    (fun L => (((Trip H g L j x x').encard : ℕ∞) : ℝ≥0∞))
    (ENNReal.ofReal (Z * Y ^ (6 * (j : ℝ) + 10 + 4 * c) * (1 + Pk))) I
    (fun i L => (((GlobalTheory.Mass.primSp H.B.flip L (k - i.1) i.2).encard : ℕ∞) : ℝ≥0∞))
    (fun i => ENNReal.ofReal (B i)) (by
      intro L hL
      obtain ⟨hLi, hLd⟩ := hgen L hL
      rw [hd] at hLd
      have hG : GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L) L 1 := genBy_of_genus _ hs hL₀.1 hL
        (fun x hx => (Formalism.HermitianLatticesTheory.isomAct_mem_dual _ L x).2 fun y hy => hLi.2 y hy x hx)
        (by rw [hLd]; omega) t ht htM
      have ps := fun s n U => GlobalTheory.T.count_isometry_pairs_with_given_fixed_space hMk K V H hK hpd L g j D hLi hLd hG hg x x' s n U hx hx'
      have pk := GlobalTheory.T.pairs_isometry_no_fixed_vector_count_bound hMk K V H hK hpd L g j D hLi hLd hG hg x x' hx hx'
      rw [← hY] at ps pk
      refine (encard_cover_le _ {p ∈ Trip H g L j x x' | fixSp p.2.2 = ⊤}
        {p ∈ Trip H g L j x x' | fixSp p.2.2 = ⊥} I
        (fun i => {p ∈ Trip H g L j x x' | fixSp p.2.2 ∈ GlobalTheory.Mass.primSp H.B.flip L (k - i.1) i.2}) ?_).trans ?_
      · intro p hp
        by_cases h1 : fixSp p.2.2 = ⊤
        · exact Or.inl (Or.inl ⟨hp, h1⟩)
        by_cases h2 : fixSp p.2.2 = ⊥
        · exact Or.inl (Or.inr ⟨hp, h2⟩)
        have l1 : Module.finrank K (fixSp p.2.2) < k := Submodule.finrank_lt h1
        have l2 : Module.finrank K (fixSp p.2.2) ≠ 0 := fun e => h2 (Submodule.finrank_eq_zero.1 e)
        have l3 := Nat.one_le_iff_ne_zero.2 (discN_res_ne_zero hK _ hs hpd hLi (fixSp p.2.2))
        have l4 := ps (k - Module.finrank K (fixSp p.2.2)) _ (fixSp p.2.2) l3 (by omega) rfl
        refine Or.inr (Set.mem_biUnion (x := (k - Module.finrank K (fixSp p.2.2),
          GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (fixSp p.2.2)) (GlobalTheory.Mass.latIn (fixSp p.2.2) L))) ?_
          ⟨hp, by simp only; omega, rfl⟩)
        simp only [I, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico, Finset.mem_Icc]
        refine ⟨by omega, l3, ?_⟩
        by_contra hn
        rw [if_neg (fun a => hn (by exact_mod_cast a))] at l4
        have : ({q ∈ Trip H g L j x x' | fixSp q.2.2 = fixSp p.2.2}).encard = 0 := by simpa using l4
        exact (Set.eq_empty_iff_forall_notMem.1 (Set.encard_eq_zero.1 this)) p ⟨hp, rfl⟩
      · refine add_le_add ?_ (Finset.sum_le_sum fun i hi => encard_fibres_le _ _ _ _ fun U hU => ?_)
        · have p0 := ps 0 D ⊤ hD1 (by simp) ((discN_top _ _).trans hLd)
          rw [if_pos (by nlinarith)] at p0
          rw [mul_add, mul_one, ENNReal.ofReal_add (by positivity) (by positivity)]
          refine add_le_add (p0.trans (ENNReal.ofReal_le_ofReal
            (top_bound c D _ Y g k f j x x' hc hD1' rfl hX1 hY))) (pk.trans (ENNReal.ofReal_le_ofReal ?_))
          have : Y ^ (c + 3 * (2 * (j : ℝ) + 1)) ≤ Y ^ (6 * (j : ℝ) + 10 + 4 * c) :=
            Real.rpow_le_rpow_of_exponent_le hY2 (by linarith)
          change Z * _ * Pk ≤ _
          gcongr
        · simp only [I, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc] at hi
          have p1 := ps i.1 i.2 U hi.2.1 (by rw [hU.1]; omega) hU.2
          rw [if_pos (by exact_mod_cast hi.2.2)] at p1
          exact p1)
  refine h1.trans ?_
  rw [← hmass, ← ENNReal.ofReal_mul hm0.le]
  set C : ℕ → ℝ := fun s => ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s with hC
  have C0 : ∀ s, 0 ≤ C s := fun s => pow_nonneg (by positivity) _
  set A := Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f with hAdef
  have h2 : ∑ i ∈ I, GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀)
      (fun L => (((GlobalTheory.Mass.primSp H.B.flip L (k - i.1) i.2).encard : ℕ∞) : ℝ≥0∞)) * ENNReal.ofReal (B i) ≤
      ∑ i ∈ I, ENNReal.ofReal (m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * C i.1) := by
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [I, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc] at hi
    refine (mul_le_mul_left (hSC i.1 i.2 hi.1.1 hi.1.2 hi.2.1) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (mid_bound m A c D _ Y g i.2 i.1 k f j x x' hm0.le hA hc hD1' rfl hX1 hY hg
      hi.2.1 (by rw [← mul_assoc]; exact_mod_cast hi.2.2) hi.1.2.le)
  refine (add_le_add_right h2 _).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := C0 i.1; positivity),
    ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ => by have := C0 i.1; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : ∑ i ∈ I, m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * C i.1 =
      (D * ((x : ℝ) * x')) * (m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * ∑ s ∈ Finset.Ico 1 k, C s) := by
    rw [Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [mul_assoc]
  have e2 : Y ^ (6 * (j : ℝ) + 10 + 4 * c) = Y * Y ^ (6 * (j : ℝ) + 9 + 4 * c) := by
    rw [← Real.rpow_one_add' Y0.le (by positivity)]
    congr 1
    ring
  have S0 : 0 ≤ ∑ s ∈ Finset.Ico 1 k, C s := Finset.sum_nonneg fun s _ => C0 s
  have b := mul_le_mul_of_nonneg_right hY1
    (show 0 ≤ m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * ∑ s ∈ Finset.Ico 1 k, C s by positivity)
  rw [e1, e2]
  refine (add_le_add_right b _).trans (le_of_eq ?_)
  ring

end GlobalTheory.DegCnt.PairMean
end

section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairsRow

theorem main : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → HostC → LatticeNormalizationCondition →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    Module.finrank D.host.E W = D.R.k → GlobalTheory.Mass.PD HW.B.flip → ∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) *
          GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') := by
  intro hMax hSi hHost hLat D large₂ X Y u hStd W HW hEmb hk hpd Λ hΛ x x' hx hx'
  obtain ⟨hK, -, -, hv1, -, -, -, -, -, -, -, hg, hT⟩ := hHost D large₂ hStd
  have hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E := by
    rw [(hHost D large₂ hStd).2.2.1]; exact hv1
  obtain ⟨hTp, hTP⟩ := hT u
  obtain ⟨hI, he⟩ := hLat D large₂ X Y u hStd W HW hEmb Λ hΛ
  have hk3 : 3 ≤ Module.finrank D.host.E W := by
    rw [hk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have : FiniteDimensional D.host.E W := Module.finite_of_finrank_pos (by omega)
  have h := GlobalTheory.DegCnt.PairMean.main Formalism.MainNotions.KappaEndpoints.mk_core hMax hSi D.host.E W HW hK
    (GlobalTheory.OrthoLattice.hasOrtho D.host.E hK) hv hpd hk3 (Tu D u) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) _ hTp hTP hI he rfl
    _ rfl (gS D) D.R.rS x x' _ hg hx hx' rfl
  rw [hk] at h
  refine h.trans (le_of_eq ?_)
  unfold GlobalTheory.DegAsm.pairBd
  simp only [mul_assoc]

end GlobalTheory.PairsRow
end

section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusMean_embeddedPairs_le_mass_mul_pairBound : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → HostC → LatticeNormalizationCondition →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    Module.finrank D.host.E W = D.R.k → GlobalTheory.Mass.PD HW.B.flip → ∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) *
          GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') := by
  first | exact @GlobalTheory.PairsRow.main | exact GlobalTheory.PairsRow.main | (intros; apply GlobalTheory.PairsRow.main <;> assumption)
end
