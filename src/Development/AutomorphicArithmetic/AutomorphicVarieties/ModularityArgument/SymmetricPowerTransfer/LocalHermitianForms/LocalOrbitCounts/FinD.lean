import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.MemRangeIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.MemCOfInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeProperties.LeftMulMatrixEmbeddingDetEqNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GConj

section
open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem fin_between {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}
    (L : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (x : Etau K τ) (hx : x.im ≠ 0) :
    {S : Set (Etau K τ) | IsLat O τ S ∧ 1 ∈ S ∧ x ∈ S ∧ ∀ w ∈ S, IsIntegral O w}.Finite := by
  haveI := L.frac
  classical
  obtain ⟨N, hN, hden⟩ := int_denom L hτ
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) ({-x.re / x.im, 1 / x.im} : Finset K)
  obtain ⟨p, hp⟩ := hr _ (Finset.mem_insert_self _ _)
  obtain ⟨q, hq⟩ := hr _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [Algebra.smul_def] at hp hq
  haveI := finite_quot_span L (mul_ne_zero hN (nonZeroDivisors.coe_ne_zero r))
  let M := integralClosure O (Etau K τ)
  haveI : Module.Finite O M := Module.Finite.iff_fg (N := Subalgebra.toSubmodule M).2 (intE_fg L hτ)
  let I : Submodule O M := Ideal.span {N * r} • ⊤
  haveI : Finite (M ⧸ I) := Submodule.finite_quotient_smul _ Module.Finite.fg_top
  let f : Set (M ⧸ I) → Set (Etau K τ) := fun A => Subtype.val '' (I.mkQ ⁻¹' A)
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨⟨⟨g, rfl⟩, -⟩, h1, h2, h3⟩
  set T := Submodule.span O (g : Set (Etau K τ))
  refine ⟨I.mkQ '' (Subtype.val ⁻¹' (T : Set (Etau K τ))), ?_⟩
  ext w
  constructor
  · rintro ⟨y, ⟨z, hz, e⟩, rfl⟩
    have h4 : y - z ∈ (Ideal.span {N * r} • ⊤ : Submodule O M) := (Submodule.Quotient.eq _).1 e.symm
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h4
    obtain ⟨m, -, hm⟩ := h4
    have hm' : (N * r) • (m : Etau K τ) = y - z := congrArg Subtype.val hm
    obtain ⟨a, b, ha, hb⟩ := hden _ m.2
    have e2 : (y : Etau K τ) = z + ((r * a + b * p) • (1 : Etau K τ) + (b * q) • x) := by
      rw [← sub_eq_iff_eq_add', ← hm', ← algebraMap_smul K (N * r), ← algebraMap_smul K (r * a + b * p), ← algebraMap_smul K (b * q)]
      simp only [map_mul, map_add, hp, hq, ← ha, ← hb]
      ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, - algebraMap_smul] <;> field_simp <;> ring
    rw [e2]
    exact T.add_mem hz (T.add_mem (T.smul_mem _ h1) (T.smul_mem _ h2))
  · intro hw
    exact ⟨⟨w, h3 w hw⟩, ⟨⟨w, h3 w hw⟩, hw, rfl⟩, rfl⟩

open UpperTheory.V.Z.Sym.Loc.GL in
theorem UpperTheory.V.Z.Sym.Loc.finG : UpperTheory.V.Z.Sym.Loc.FinG := by
  intro O K _ _ _ _ _ Δ τ L hτ j hj z hz
  haveI := L.frac
  classical
  obtain ⟨g, hg⟩ := (gConj O K Δ τ L hτ (j0 τ) j leftMulMatrixEmbedding_omega_trace hj).1
  have det : ∀ (y : GL (Fin 2) K) (s : Kˣ) (k : GL (Fin 2) K), k ∈ KG O K → y⁻¹ * jU j z * y = sc s * k →
      ∃ e : Oˣ, QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K e * (s : K) ^ 2 := fun y s k hk e => by
    obtain ⟨u, hu⟩ := kg_det hk
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K).det) e
    simp only [Units.val_mul] at this
    rw [Matrix.det_units_conj', Matrix.det_mul, hu, sc_val, Matrix.det_smul] at this
    exact ⟨u, by rw [← j_det j hj]; exact this.trans (by simp [mul_comm])⟩
  by_cases h0 : ∃ y₀ : GL (Fin 2) K, y₀⁻¹ * jU j z * y₀ ∈ ZK O K
  swap
  · exact ⟨∅, fun y hy => absurd ⟨y, hy⟩ h0⟩
  obtain ⟨y₀, hy₀⟩ := h0
  obtain ⟨s, k₀, hk₀, e₀⟩ := zk_iff.1 hy₀
  obtain ⟨ε, hε⟩ := det y₀ s k₀ hk₀ e₀
  let u : (Etau K τ)ˣ := su τ s⁻¹ * z
  have hun : QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε := by
    rw [Units.val_mul, su_mul, Algebra.smul_def, map_mul, QuadraticAlgebra.norm_algebraMap, hε, Units.val_inv_eq_inv_val]
    field_simp
  have hui : (u : Etau K τ).im ≠ 0 := by
    rw [Units.val_mul, su_mul]
    simpa using hz
  have fin := fin_between L hτ u hui
  choose! rep hrep using fun S (h : IsLat O τ S) => isLat_lat h
  refine ⟨fin.toFinset.image fun S => g⁻¹ * rep S, fun y hy => ?_⟩
  have h1 : (g * y)⁻¹ * (jU (j0 τ) u * (g * y)) ∈ ZK O K := by
    have : (g * y)⁻¹ * (jU (j0 τ) u * (g * y)) = sc s⁻¹ * (y⁻¹ * jU j z * y) := by
      rw [map_mul, jU_su, hg, mul_assoc (sc s⁻¹), ← mul_assoc, ← sc_comm]; group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) hy
  have h2 := ent_of_zk ε (by
    rw [← mul_assoc, Units.val_mul, Units.val_mul, Matrix.det_units_conj', ← hun]; exact leftMulMatrixEmbedding_det_eq_norm _) h1
  have h3 := lat_le (τ := τ).2 h2
  rw [lat_mul] at h3
  obtain ⟨t, ht⟩ := PS.gen_ex L hτ (lat_isLat (O := O) (g * y))
  have hl := PS.lat_ml (lat_isLat (O := O) (τ := τ) (g * y)) t⁻¹
  have hm : PS.ml t⁻¹ (LL O τ (g * y)) ∈ fin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨hl, PS.mem_ml.2 (by simpa using ht.1), PS.mem_ml.2 ?_, ?_⟩
    · rw [inv_inv, mul_comm]; exact h3 ⟨_, ht.1, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ht.2 w hw
  refine ⟨t, _, Finset.mem_image_of_mem _ hm, (jU j t * (g⁻¹ * rep (PS.ml t⁻¹ (LL O τ (g * y)))))⁻¹ * y, ?_, by group⟩
  have : cls τ (LL O τ (jU (j0 τ) t * rep (PS.ml t⁻¹ (LL O τ (g * y))))) = cls τ (LL O τ (g * y)) := by
    rw [lat_mul, ← hrep _ hl]
    change cls τ (PS.ml _ _) = _
    rw [← PS.ml_mul, mul_inv_cancel, PS.ml_one]
  rw [cls_lat] at this
  rw [hg]
  simpa [mul_assoc] using this
end

section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem map_two_add_smul_eq (O K : Type) [CommRing O] [Field K] [Algebra O K] (π : O)
    (X : Matrix (Fin 2) (Fin 2) O) :
    (1 + 1 + π • X).map (algebraMap O K) = 1 + 1 + algebraMap O K π • X.map (algebraMap O K) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply] <;> rw [Algebra.smul_def]

theorem UpperTheory.V.Z.Sym.Loc.stabG : UpperTheory.V.Z.Sym.Loc.StabG := by
  classical
  intro O K _ _ _ _ _ Δ τ L hτ j hj y
  haveI := L.frac
  set H := Subgroup.comap (jU j) (Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj y⁻¹)) (ZK O K)) with hH
  have memH : ∀ z, z ∈ H ↔ y⁻¹ * jU j z * y ∈ ZK O K := by
    intro z
    simp [hH]
  have Q : ∀ z : (Etau K τ)ˣ, trace (quo z) = trace (z : Etau K τ) ^ 2 * norm (↑z⁻¹ : Etau K τ) - 2 ∧
      norm (quo z) = 1 ∧ norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1 := by
    intro z
    have hzw : (z : Etau K τ) * ↑z⁻¹ = 1 := z.mul_inv
    have hn : norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1 := by rw [← map_mul, hzw, map_one]
    have h1 : quo z = algebraMap K (Etau K τ) (trace (↑z⁻¹ : Etau K τ)) * z - 1 := by
      rw [quo, star_eq (↑z⁻¹ : Etau K τ), mul_sub, hzw, mul_comm]
    have h2 : trace (z : Etau K τ) = norm (z : Etau K τ) * trace (↑z⁻¹ : Etau K τ) := by
      have e : algebraMap K (Etau K τ) (norm (z : Etau K τ)) * ↑z⁻¹ = star (z : Etau K τ) := by
        rw [algebraMap_norm_eq_mul_star, mul_comm (z : Etau K τ), mul_assoc, hzw, mul_one]
      have := congrArg trace e
      rw [← Algebra.smul_def, map_smul, smul_eq_mul, trace_star] at this
      exact this.symm
    refine ⟨?_, ?_, hn⟩
    · rw [h1, map_sub, ← Algebra.smul_def, map_smul, smul_eq_mul, trace_one]
      linear_combination (-(trace (z : Etau K τ)) * trace (↑z⁻¹ : Etau K τ)) * hn +
        (-(trace (z : Etau K τ)) * norm (↑z⁻¹ : Etau K τ)) * h2
    · rw [quo, map_mul, QuadraticAlgebra.norm_star, hn]
  have P1 : ∀ z ∈ H, IsIntegral O (quo z) := by
    intro z hz
    rw [memH] at hz
    obtain ⟨c, k, hck⟩ := mem_ZK.mp hz
    have hM := congrArg Units.val hck
    rw [Units.val_mul, Units.val_mul, Units.val_mul] at hM
    have e0 : ((jU j z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = j ↑z := rfl
    rw [e0] at hM
    have htr : trace (z : Etau K τ) = c * algebraMap O K (Matrix.trace (k : Matrix (Fin 2) (Fin 2) O)) := by
      rw [← j_trace j hj, ← Matrix.trace_units_conj' y (j z), hM]
      simp [Matrix.trace_fin_two, Matrix.GeneralLinearGroup.map_apply] <;> ring
    have hdet : norm (z : Etau K τ) = c ^ 2 * algebraMap O K (Matrix.det (k : Matrix (Fin 2) (Fin 2) O)) := by
      rw [← j_det j hj, ← Matrix.det_units_conj' y (j z), hM]
      simp [Matrix.det_fin_two, Matrix.GeneralLinearGroup.map_apply] <;> ring
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mp k.isUnit
    have hunit : algebraMap O K ↑u⁻¹ * algebraMap O K ↑u = 1 := by
      rw [← map_mul]
      simp
    have hn' := (Q z).2.2
    rw [hdet, ← hu] at hn'
    refine isIntegral_of_trace_norm (x := quo z) ((k : Matrix (Fin 2) (Fin 2) O).trace ^ 2 * ↑u⁻¹ - 2) 1 ?_ ?_
    · rw [(Q z).1, htr]
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      linear_combination (algebraMap O K (k : Matrix (Fin 2) (Fin 2) O).trace) ^ 2 *
        (-((c : K) ^ 2 * norm (↑z⁻¹ : Etau K τ)) * hunit + algebraMap O K ↑u⁻¹ * hn')
    · rw [(Q z).2.1, map_one]
  refine ⟨fun z hz => ⟨P1 z hz, P1 _ (H.inv_mem hz)⟩, ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨s, hs⟩ := intE_fg L hτ
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (s.biUnion fun g => Finset.univ.image fun p : Fin 2 × Fin 2 =>
      (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j g * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) p.1 p.2)
  have hint : ∀ x ∈ Submodule.span O (s : Set (Etau K τ)), ∀ a b,
      IsLocalization.IsInteger O ((d : O) • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) a b) := by
    intro x hx a b
    induction hx using Submodule.span_induction with
    | mem g hg =>
      exact hd _ (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩⟩)
    | zero => simpa using IsLocalization.isInteger_zero
    | add x x' _ _ h1 h2 =>
      rw [map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, smul_add]
      exact IsLocalization.isInteger_add h1 h2
    | smul o x _ h =>
      rw [← algebraMap_smul K o x, map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
        algebraMap_smul, smul_comm]
      exact IsLocalization.isInteger_smul h
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hd0 : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hm : π * (d : O) ≠ 0 := mul_ne_zero hπ0 hd0
  refine cint_relIndex_ne_zero L hτ hm H ?_
  intro z _ r hr hq
  have hrs : r ∈ Submodule.span O (s : Set (Etau K τ)) := by
    rw [hs, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
    exact hr
  let X : Matrix (Fin 2) (Fin 2) O := Matrix.of fun a b => (hint r hrs a b).choose
  have hX : ∀ a b, algebraMap O K (X a b) = (d : O) • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j r * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) a b :=
    fun a b => (hint r hrs a b).choose_spec
  have hzw : (z : Etau K τ) * ↑z⁻¹ = 1 := z.mul_inv
  have hn : norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1 := by rw [← map_mul, hzw, map_one]
  have hN0 : norm (z : Etau K τ) ≠ 0 := left_ne_zero_of_mul_eq_one hn
  have hsw : star (z : Etau K τ) * star (↑z⁻¹ : Etau K τ) = 1 := by
    rw [← star_mul, z.inv_mul, star_one]
  have hkey : algebraMap K (Etau K τ) (trace (z : Etau K τ)) * z =
      algebraMap K (Etau K τ) (norm (z : Etau K τ)) * (1 + quo z) := by
    rw [algebraMap_trace_eq_add_star, algebraMap_norm_eq_mul_star, quo]
    linear_combination (-((z : Etau K τ) * z)) * hsw
  have h2 : IsUnit (2 : O) := L.two
  have hm' : algebraMap O K (π * d) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hm
  have htr0 : trace (z : Etau K τ) ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hkey
    have hu : algebraMap K (Etau K τ) (norm (z : Etau K τ)) * algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ)) = 1 := by
      rw [← map_mul, hn, map_one]
    have h1q : (1 : Etau K τ) + quo z = 0 := by
      calc (1 : Etau K τ) + quo z = algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ)) *
            (algebraMap K (Etau K τ) (norm (z : Etau K τ)) * (1 + quo z)) := by
            rw [← mul_assoc, mul_comm (algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ))), hu, one_mul]
        _ = 0 := by rw [← hkey, mul_zero]
    rw [hq] at h1q
    have e : algebraMap O K (π * d) • r = algebraMap K (Etau K τ) (-2) := by
      rw [map_neg, map_ofNat]
      linear_combination h1q
    have hr' : r = algebraMap K (Etau K τ) (-2 / algebraMap O K (π * d)) := by
      calc r = (algebraMap O K (π * d))⁻¹ • (algebraMap O K (π * d) • r) := by
            rw [smul_smul, inv_mul_cancel₀ hm', one_smul]
        _ = _ := by rw [e, Algebra.smul_def, ← map_mul, div_eq_inv_mul]
    rw [hr'] at hr
    have hI : IsIntegral O (-2 / algebraMap O K (π * d)) :=
      (isIntegral_algebraMap_iff (algebraMap K (Etau K τ)).injective).mp hr
    obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI
    have h4 : (-2 : O) = π * d * o := by
      apply IsFractionRing.injective O K
      rw [map_mul (algebraMap O K) (π * d) o, ho, mul_div_assoc', mul_comm, mul_div_assoc, div_self hm',
        mul_one, map_neg, map_ofNat]
    exact hπ.not_isUnit (isUnit_of_mul_isUnit_left (x := π) (y := (d : O) * o)
      (by rw [← mul_assoc, ← h4]; exact h2.neg))
  have ha : norm (z : Etau K τ) / trace (z : Etau K τ) ≠ 0 := div_ne_zero hN0 htr0
  have hz_eq : (z : Etau K τ) = algebraMap K (Etau K τ) (norm (z : Etau K τ) / trace (z : Etau K τ)) *
      (1 + (1 + algebraMap O K (π * d) • r)) := by
    rw [← hq]
    calc (z : Etau K τ) = algebraMap K (Etau K τ) (trace (z : Etau K τ))⁻¹ *
          (algebraMap K (Etau K τ) (trace (z : Etau K τ)) * z) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ htr0, map_one, one_mul]
      _ = _ := by rw [hkey, ← mul_assoc, ← map_mul, div_eq_mul_inv, mul_comm (trace (z : Etau K τ))⁻¹]
  have hYY : ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have φmul : ∀ (b : K) (x : Etau K τ), ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (algebraMap K (Etau K τ) b * x) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = b • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    intro b x
    rw [map_mul, j.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have φadd : ∀ x x' : Etau K τ, ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (x + x') * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) + ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x' * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro x x'
    rw [map_add, Matrix.mul_add, Matrix.add_mul]
  have φone : ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j 1 * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [map_one, Matrix.mul_one, hYY]
  have φsmul : ∀ (b : K) (x : Etau K τ), ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (b • x) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = b • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    intro b x
    rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hXm : X.map (algebraMap O K) = algebraMap O K d • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j r * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    ext a b
    rw [Matrix.map_apply, hX, Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]
  let km : Matrix (Fin 2) (Fin 2) O := 1 + 1 + π • X
  have hkm : km.map (algebraMap O K) = 1 + 1 + algebraMap O K π • X.map (algebraMap O K) := by
    exact map_two_add_smul_eq O K π X
  have hdet : km.det = 4 + π * (2 * X 0 0 + 2 * X 1 1 + π * (X 0 0 * X 1 1 - X 0 1 * X 1 0)) := by
    simp [km, Matrix.det_fin_two, Matrix.one_apply]
    ring
  have hdu : IsUnit km.det := by
    by_contra hnu
    have hπm : π ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hπ.not_isUnit)
    have hdm : km.det ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have h4m : (4 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ hdm (Ideal.mul_mem_right (2 * X 0 0 + 2 * X 1 1 + π * (X 0 0 * X 1 1 - X 0 1 * X 1 0)) _ hπm)
      rwa [hdet, add_sub_cancel_right] at this
    apply mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h4m)
    rw [show (4 : O) = 2 * 2 by norm_num]
    exact h2.mul h2
  let kk : GL (Fin 2) O := ((Matrix.isUnit_iff_isUnit_det _).mpr hdu).unit
  have hA : ((Matrix.GeneralLinearGroup.map (algebraMap O K) kk : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      km.map (algebraMap O K) := by
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl
  rw [memH]
  apply mem_ZK.mpr
  refine ⟨Units.mk0 _ ha, kk, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  change ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [Matrix.GeneralLinearGroup.coe_scalar, hA, hkm, hXm, Units.val_mk0, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]
  conv_lhs => rw [hz_eq]
  rw [φmul, φadd, φone, φadd, φone, φsmul, map_mul, smul_smul, add_assoc]
end

section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.finD : UpperTheory.V.Z.Sym.Loc.FinD := by
  classical
  intro O K _ _ _ _ _ Δ τ L hτ γ j hγ hj
  obtain ⟨φ, h1, h2, -, h4⟩ := dIso O K Δ L
  obtain ⟨j', hj'γ, hj'tr, hj'⟩ := h4 τ γ j hγ hj
  have hZD : ∀ g : DX Δ, g ∈ ZD Δ ↔ ∃ z, IsScal z g := by
    intro g
    simp only [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.comp_apply, IsScal]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
      rw [← hz]
      first | rfl | simp [Matrix.GeneralLinearGroup.scalar]
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply Units.ext
      rw [show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Glob.mt g from rfl, hz]
      first | rfl | simp [Matrix.GeneralLinearGroup.scalar]
  have hmap : (ZD Δ ⊔ KD Δ O).map φ.toMonoidHom = ZK O K := by
    rw [Subgroup.map_sup]
    unfold ZK
    congr 1
    · ext x
      rw [Subgroup.mem_map_equiv, hZD, MonoidHom.mem_range]
      constructor
      · rintro ⟨z, hz⟩
        exact ⟨z, by rw [← (h2 z _).1 hz]; simp⟩
      · rintro ⟨z, rfl⟩
        exact ⟨z, (h2 z _).2 (by simp)⟩
    · ext x
      rw [Subgroup.mem_map_equiv, ← h1]
      simp
  have hmem : ∀ g, g ∈ ZD Δ ⊔ KD Δ O ↔ φ g ∈ ZK O K := by
    intro g
    rw [← hmap, Subgroup.mem_map_equiv]
    simp
  have hgen : ∀ z : (Etau K τ)ˣ, (z : Etau K τ).im ≠ 0 → ∃ S : Finset (DX Δ), ∀ y : DX Δ,
      y⁻¹ * j z * y ∈ ZD Δ ⊔ KD Δ O → ∃ t, ∃ s ∈ S, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * s * u := by
    intro z hz
    obtain ⟨s, hs⟩ := finG O K Δ τ L hτ j' hj'tr z hz
    refine ⟨s.image φ.symm, ?_⟩
    intro y hy
    rw [hmem] at hy
    simp only [map_mul, map_inv, hj'] at hy
    obtain ⟨t, x, hx, k, hk, hyk⟩ := hs (φ y) hy
    refine ⟨t, φ.symm x, Finset.mem_image_of_mem _ hx, φ.symm k, by rw [hmem]; simp [hk], ?_⟩
    apply φ.injective
    simp [map_mul, hj', hyk]
  obtain ⟨a, ha⟩ := exists_a (K := K) (τ := τ)
  have hγa : γ = j a := by
    apply φ.injective
    rw [hj']
    apply Units.ext
    rw [← hj'γ]
    simp [ha]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hgen a (by rw [ha]; simp)
    refine ⟨S, ?_⟩
    intro y hy
    apply hS y
    have hK : y⁻¹ * γ * y ∈ KD Δ O := by
      by_contra hn
      apply hy
      simp [one, hn]
    rw [← hγa]
    exact Subgroup.mem_sup_right hK
  · intro z hz χ
    obtain ⟨S, hS⟩ := hgen z (by rw [hz]; simp)
    refine ⟨S, ?_⟩
    intro y hy
    apply hS y
    unfold fZD at hy
    split_ifs at hy with hh
    · obtain ⟨z0, s0, hsc, hk⟩ := hh
      have hs0 : s0 ∈ ZD Δ := (hZD s0).2 ⟨z0, hsc⟩
      have := (ZD Δ ⊔ KD Δ O).mul_mem (Subgroup.mem_sup_left hs0) (Subgroup.mem_sup_right hk)
      simpa using this
    · exact absurd rfl hy
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hst : Subgroup.comap j (MulAction.stabilizer (DX Δ) (g : DX Δ ⧸ ZD Δ ⊔ KD Δ O)) =
        Subgroup.comap (jU j') (Subgroup.comap (MulAut.conj (φ g)⁻¹).toMonoidHom (ZK O K)) := by
      ext t
      simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk,
        smul_eq_mul, QuotientGroup.eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← Subgroup.inv_mem_iff, show ((j t * g)⁻¹ * g)⁻¹ = g⁻¹ * j t * g by group, hmem]
      simp [hj']
    rw [hst]
    exact stabG O K Δ τ L hτ j' hj'tr (φ g)
end
