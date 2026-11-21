import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman

section
open Filter Topology ValuativeRel

private theorem small_powers {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (V : Set k) (hV : V ∈ nhds (0 : k)) :
    ∀ᶠ c : ℕ in atTop, ∀ x ∈ IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c,
      (x : k) ∈ V := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hV
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(valuation k).integer
  have hlt : valuation k (π : k) < 1 := by
    refine lt_of_le_of_ne π.2 fun h => hπ.not_isUnit ?_
    exact (Valuation.integer.integers (valuation k)).isUnit_of_one' h
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop N] with c hc x hx
  have hx' := Ideal.pow_le_pow_right hc hx
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx'
  obtain ⟨a, rfl⟩ := hx'
  apply hs
  have ha : valuation k (a : k) ≤ 1 := a.2
  change valuation k ((a : k) * (π : k) ^ N) < γ
  rw [map_mul, map_pow]
  calc _ ≤ 1 * valuation k (π : k) ^ N := by gcongr
    _ < γ := by simpa using hN

private theorem entry_mem {k : Type} [Field k] [ValuativeRel k] {n : ℕ}
    (I : Ideal ↥(valuation k).integer) (g : GL (Fin n) k)
    (hg : g ∈ Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker) (i j : Fin n) :
    ∃ x ∈ I, (x : k) = (g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 : Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I) h = 1 := hh
  have h2 : Ideal.Quotient.mk I ((h : Matrix (Fin n) (Fin n) _) i j)
      = (1 : Matrix (Fin n) (Fin n) (_ ⧸ I)) i j :=
    by
      have h4 := Units.ext_iff.mp h1
      exact congrFun (congrFun h4 i) j
  refine ⟨(h : Matrix (Fin n) (Fin n) _) i j - (1 : Matrix (Fin n) (Fin n) _) i j, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, h2]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · have h3 : ((Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k) h :
        GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
        = (((h : Matrix (Fin n) (Fin n) ↥(valuation k).integer) i j : _) : k) := rfl
    rw [h3]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem tendsto_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {α : Type} (L : Filter α) (c : α → ℕ)
    (hc : Tendsto c L atTop) (g : α → GL (Fin n) k)
    (hg : ∀ᶠ a in L, g a ∈ Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c a))).ker) :
    Tendsto (fun a => (g a : Matrix (Fin n) (Fin n) k)) L (nhds 1) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  rw [← tendsto_sub_nhds_zero_iff]
  refine tendsto_def.mpr fun V hV => ?_
  filter_upwards [hg, hc.eventually (small_powers V hV)] with a ha hs
  obtain ⟨x, hx, e⟩ := entry_mem _ _ ha i j
  have := hs x hx
  rwa [e] at this

theorem UpperTheory.congruence_subgroup_eventually :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) →
        ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∀ g : GL (Fin n) k, g ∈ Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
          (Matrix.GeneralLinearGroup.map (n := Fin n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer ^ c))).ker → g ∈ U := by
  intro k _ _ _ _ n U hU
  let K : ℕ → Subgroup (GL (Fin n) k) := fun c => Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c))).ker
  let L : Filter (ℕ × GL (Fin n) k) := comap Prod.fst atTop ⊓ 𝓟 {p | p.2 ∈ K p.1}
  have hc : Tendsto Prod.fst L atTop := tendsto_comap.mono_left inf_le_left
  have hK : ∀ᶠ p in L, p.2 ∈ K p.1 := mem_inf_of_right (mem_principal_self _)
  have h1 := tendsto_val L Prod.fst hc Prod.snd hK
  have h2 := tendsto_val L Prod.fst hc (fun p => p.2⁻¹) (hK.mono fun p hp => (K p.1).inv_mem hp)
  have h : Tendsto Prod.snd L (nhds (1 : GL (Fin n) k)) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds h1 ?_
    exact (MulOpposite.continuous_op.tendsto _).comp h2
  have h3 : ∀ᶠ p in L, p.2 ∈ U := h hU
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at h3
  obtain ⟨c₀, h₀⟩ := h3
  exact ⟨c₀, fun c hc g hg => h₀ c hc (c, g) rfl hg⟩
end

section
private lemma liftUnitri {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (I : Ideal R) {n : ℕ}
    (h : GL (Fin n) K) (a : Fin n → Fin n → R)
    (ha : ∀ i j, f (a i j) = (h : Matrix (Fin n) (Fin n) K) i j)
    (hlow : ∀ i j, j < i → a i j = 0) (hd : ∀ i, a i i = 1)
    (hI : ∀ i j, i < j → a i j ∈ I) :
    h ∈ Subgroup.map (Matrix.GeneralLinearGroup.map f)
      (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker := by
  have hdet : (Matrix.of a).det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := Matrix.of a) (fun i j hij => hlow i j hij)]
    simp [hd]
  let H : GL (Fin n) R := Matrix.GeneralLinearGroup.mk'' (Matrix.of a) (by rw [hdet]; exact isUnit_one)
  refine ⟨H, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have : Ideal.Quotient.mk I (a i j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hI i j hij)
      simpa [H, Matrix.one_apply, hij.ne] using this
    · simp [H, hd]
    · simp [H, hlow i j hij, Matrix.one_apply, hij.ne']
  · ext i j
    simp [H, ha]

theorem UpperTheory.diagonal_conjugate_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (ϖ : kˣ), ValuativeRel.valuation k (ϖ : k) < 1 →
        ∀ (c : ℕ) (z g : GL (Fin n) k),
        (z : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (fun i : Fin n => ((ϖ ^ ((n : ℤ) - 1 - ((i : ℕ) : ℤ)) : kˣ) : k)) →
        g ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (↥(ValuativeRel.valuation k).integer) k)).range →
        (g : Matrix (Fin n) (Fin n) k).BlockTriangular id → (∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1) →
        z ^ c * g * (z ^ c)⁻¹ ∈ Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
          (Matrix.GeneralLinearGroup.map (n := Fin n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer ^ c))).ker := by
  intro k _ _ _ _ n ϖ hϖ c z g hz hg hb hd
  obtain ⟨g0, hg0⟩ := hg
  have hg0' : ∀ i j, algebraMap (↥(ValuativeRel.valuation k).integer) k ((g0 : Matrix (Fin n) (Fin n) _) i j)
      = (g : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    rw [← hg0]
    simp
  let p : ↥(ValuativeRel.valuation k).integer := ⟨(ϖ : k), hϖ.le⟩
  have hp : p ∈ IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    have h1 : ValuativeRel.valuation k ((p * q : ↥(ValuativeRel.valuation k).integer) : k) = 1 := by
      rw [hq]; simp
    have h2 : ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) ≤ 1 := q.2
    rw [Subring.coe_mul, map_mul] at h1
    have h3 : ValuativeRel.valuation k (ϖ : k) * ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hϖ
    exact absurd h1 h3.ne
  let t : Fin n → kˣ := fun i => ϖ ^ ((n : ℤ) - 1 - ((i : ℕ) : ℤ))
  have hz1 : ((z ^ c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => (((t i) ^ c : kˣ) : k)) := by
    rw [Units.val_pow_eq_pow_val, hz, Matrix.diagonal_pow]
    congr 1
  have hz2 : (((z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => ((((t i) ^ c)⁻¹ : kˣ) : k)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hz1, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    rw [← Units.val_mul]
    simp
  have hent : ∀ i j, ((z ^ c * g * (z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (((t i) ^ c : kˣ) : k) * (g : Matrix (Fin n) (Fin n) k) i j * ((((t j) ^ c)⁻¹ : kˣ) : k) := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hz2, hz1, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hpow : ∀ i j : Fin n, i < j →
      (((t i) ^ c : kˣ) : k) * ((((t j) ^ c)⁻¹ : kˣ) : k) = (ϖ : k) ^ (((j : ℕ) - (i : ℕ)) * c) := by
    intro i j hij
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val]
    congr 1
    have hle : (i : ℕ) ≤ (j : ℕ) := hij.le
    simp only [t]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    push_cast [Nat.cast_sub hle]
    ring
  refine liftUnitri _ _ _
    (fun i j => if i < j then p ^ (((j : ℕ) - (i : ℕ)) * c) * (g0 : Matrix (Fin n) (Fin n) _) i j
      else if i = j then 1 else 0) ?_ ?_ ?_ ?_
  · intro i j
    rw [hent]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_pos hij, map_mul, hg0', map_pow, mul_right_comm, hpow i j hij]
      rfl
    · rw [if_neg (lt_irrefl _), if_pos rfl, hd, map_one, mul_one, ← Units.val_mul]
      simp
    · rw [if_neg hij.not_gt, if_neg hij.ne', hb hij]
      simp
  · intro i j hij
    rw [if_neg hij.not_gt, if_neg hij.ne']
  · intro i
    simp
  · intro i j hij
    rw [if_pos hij]
    apply Ideal.mul_mem_right
    have hpos : (j : ℕ) - (i : ℕ) ≠ 0 := by
      have : (i : ℕ) < (j : ℕ) := hij
      omega
    rw [pow_mul]
    exact Ideal.pow_mem_pow (Ideal.pow_mem_of_mem _ hp _ (Nat.pos_of_ne_zero hpos)) c
end

section
private theorem unif_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    ValuativeRel.valuation k ((UpperTheory.V.Hi.unif k : kˣ) : k) < 1 := by
  have hex : ∃ x : kˣ, ValuativeRel.valuation k (x : k) = ValuativeRel.uniformizer k := by
    obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (ValuativeRel.uniformizer k)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact ValuativeRel.uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x hx0, hx⟩
  have h := Classical.epsilon_spec hex
  have h' : ValuativeRel.valuation k ((UpperTheory.V.Hi.unif k : kˣ) : k) = ValuativeRel.uniformizer k := h
  rw [h']
  exact ValuativeRel.uniformizer_lt_one

private theorem diagT_val (k : Type) [Field k] (n : ℕ) (t : Fin n → kˣ) :
    ((GlobalTheory.SmGL.diagT k (Fin n) t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => (t i : k)) := by
  generalize hD : Matrix.diagonal (fun i => (t i : k)) = D
  have h1 : ∀ i, D i i = t i := fun i => by rw [← hD, Matrix.diagonal_apply_eq]
  have h2 : ∀ i j, i ≠ j → D i j = 0 := fun i j h => by rw [← hD, Matrix.diagonal_apply_ne _ h]
  have key : ∀ (d : DecidableEq (Fin n)) (i j : Fin n),
      @Matrix.blockDiagonal' (Fin n) (fun _ => Unit) (fun _ => Unit) k d _
        (fun a : Fin n => ((Matrix.GeneralLinearGroup.scalar Unit (t a) : GL Unit k) : Matrix Unit Unit k)) ⟨i, ()⟩ ⟨j, ()⟩ = D i j := by
    intro d i j
    by_cases h : i = j
    · subst h
      rw [Matrix.blockDiagonal'_apply_eq, h1]
      simp
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, h2 i j h]
  ext i j
  exact key (fun a b => Classical.propDecidable _) i j

private theorem unipB_spec (k : Type) [Field k] (n : ℕ) (g : GL (Fin n) k)
    (hg : g ∈ GlobalTheory.SmGL.unipB k (Fin n)) :
    (g : Matrix (Fin n) (Fin n) k).BlockTriangular id ∧ ∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1 := by
  obtain ⟨p, hp, rfl⟩ := hg
  refine ⟨p.2, fun i => ?_⟩
  have h1 : GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.points (Fin n)) p = 1 := hp
  have h2 := congrArg (fun x => ((x i : GL Unit k) : Matrix Unit Unit k) () ()) h1
  have h3 : ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = (1 : Matrix Unit Unit k) () () := h2
  simpa using h3

theorem UpperTheory.Reformulated.B.BranchingSmooth.br_smooth :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k]
      [inst_3 : IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [inst_4 : AddCommGroup V] [inst_5 : _root_.Module ℂ V]
      (π : Representation ℂ (GL (Fin n) k) V), GlobalTheory.PRep.IsSmooth π → (UpperTheory.V.Hi.glIwa k n).Smooth π := by
  intro k _ _ _ _ n V _ _ π hπ v
  obtain ⟨c, hc⟩ := UpperTheory.congruence_subgroup_eventually (k := k) (n := n) {g | π g v = v} ((hπ v).mem_nhds (by simp))
  refine ⟨c, ?_, ?_, ?_⟩
  · show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := unipB_spec k n x hx.1
    exact hc c le_rfl _ (UpperTheory.diagonal_conjugate_mem (UpperTheory.V.Hi.unif k) (unif_lt k) c _ x (diagT_val k n _) hx.2 h1 h2)
  · show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _
    intro g hg
    exact hc (c + 1) (Nat.le_succ c) g hg.2
  · show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _
    intro g hg
    exact hc (c + 1) (Nat.le_succ c) g hg.2
end
