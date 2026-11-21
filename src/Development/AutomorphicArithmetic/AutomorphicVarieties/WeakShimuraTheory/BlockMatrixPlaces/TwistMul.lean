import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CocT
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UMFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem unit_add_mem {R : Type} [CommRing R] [IsLocalRing R] {a b : R} (ha : IsUnit a)
    (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : a ∈ maximalIdeal R := by simpa using (maximalIdeal R).sub_mem h1 hb
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 ha

private theorem two_kill {R : Type} [CommRing R] [IsLocalRing R] {p q r s a b : R} (hp : IsUnit p) (hs : IsUnit s)
    (hq : q ∈ maximalIdeal R) (e1 : p * a + q * b = 0) (e2 : r * a + s * b = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨s', hs'⟩ := hs.exists_right_inv
  have hb : b = -(s' * r) * a := by linear_combination s' * e2 - b * hs'
  have hm : q * s' * r ∈ maximalIdeal R :=
    (maximalIdeal R).mul_mem_right _ ((maximalIdeal R).mul_mem_right _ hq)
  have hu : IsUnit (p + -(q * s' * r)) := unit_add_mem hp ((maximalIdeal R).neg_mem hm)
  have ha : a = 0 := (hu.mul_right_eq_zero).mp (by linear_combination e1 - q * hb)
  refine ⟨ha, ?_⟩
  rw [hb, ha]
  ring

private theorem cols {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X) (hs : Sep X)
    (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    ∃ y, u 0 1 = y * u 0 0 ∧ u 2 1 = y * u 2 0 := by
  have h01 : IsUnit (X 0 0 - X 1 1) := hs.unit 0 1 (by decide)
  have h21 : IsUnit (X 2 2 - X 1 1) := hs.unit 2 1 (by decide)
  have p0 : IsUnit (X 0 0 - U 1 1) := by
    have := unit_add_mem h01 (neg_mem (hc 1))
    convert this using 1; ring
  have p2 : IsUnit (X 2 2 - U 1 1) := by
    have := unit_add_mem h21 (neg_mem (hc 1))
    convert this using 1; ring
  have pU : IsUnit (U 0 0 - U 1 1) := by
    have := unit_add_mem p0 (hc 0)
    convert this using 1; ring
  obtain ⟨w, hw⟩ := pU.exists_left_inv
  have z01 := hb 0 1 (by decide)
  have z03 := hb 0 3 (by decide)
  have z21 := hb 2 1 (by decide)
  have z23 := hb 2 3 (by decide)
  have y10 := hU 1 0 (by decide)
  have y20 := hU 2 0 (by decide)
  have y30 := hU 3 0 (by decide)
  have y21 := hU 2 1 (by decide)
  have y31 := hU 3 1 (by decide)
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z21, z23, y10, y20, y30, y21, y31, zero_mul, mul_zero,
    add_zero] at e00 e01 e20 e21
  have := two_kill (a := u 0 1 - U 0 1 * w * u 0 0) (b := u 2 1 - U 0 1 * w * u 2 0) (r := X 2 0) p0 p2
    (hs.off 0 2 (by decide))
    (by linear_combination e01 - U 0 1 * w * e00 - U 0 1 * u 0 0 * hw)
    (by linear_combination e21 - U 0 1 * w * e20 - U 0 1 * u 2 0 * hw)
  exact ⟨U 0 1 * w, sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

private theorem entries_one_three_zero_eq_zero_of_intertwine_up {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X)
    (hs : Sep X) (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    u 1 0 = 0 ∧ u 3 0 = 0 := by
  have X10 : X 1 0 = 0 := hb 1 0 (by simp [lamW])
  have coord_mul_inv_coord_eq_one : X 1 2 = 0 := hb 1 2 (by simp [lamW])
  have X30 : X 3 0 = 0 := hb 3 0 (by simp [lamW])
  have X32 : X 3 2 = 0 := hb 3 2 (by simp [lamW])
  have U10 : U 1 0 = 0 := hU 1 0 (by decide)
  have U20 : U 2 0 = 0 := hU 2 0 (by decide)
  have U30 : U 3 0 = 0 := hU 3 0 (by decide)
  have r10 := congrFun (congrFun e 1) 0
  have r30 := congrFun (congrFun e 3) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_four, X10, coord_mul_inv_coord_eq_one, X30, X32, U10, U20, U30,
    zero_mul, mul_zero, add_zero, zero_add] at r10 r30
  have hc0 := hc 0
  have hp : IsUnit (X 1 1 - U 0 0) := by
    have e' : X 1 1 - U 0 0 = (X 1 1 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 1 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hs' : IsUnit (X 3 3 - U 0 0) := by
    have e' : X 3 3 - U 0 0 = (X 3 3 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 3 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hq : X 1 3 ∈ maximalIdeal R := hs.off 1 3 (by decide)
  exact two_kill (r := X 3 1) (a := u 1 0) (b := u 3 0) hp hs' hq
    (by linear_combination r10) (by linear_combination r30)

theorem UpperTheory.V.Ws.Bl.flagVec :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X u : M4 R), IsBlock X → Sep X → IsGSp 1 u → IsUp (adj u * X * u) → (∀ i, (adj u * X * u) i i - X i i ∈ maximalIdeal R) → uPlus u ≠ ⊥ := by
  intro R _ _ X u hb hs hg hup hc
  have hinv : adj u * u = 1 := by simpa [IsGSp] using hg
  have e : X * u = u * (adj u * X * u) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp hinv, Matrix.one_mul]
  obtain ⟨y, hy1, hy2⟩ := cols X u _ hb hs e hup hc
  obtain ⟨h10, h30⟩ := entries_one_three_zero_eq_zero_of_intertwine_up X u _ hb hs e hup hc
  have I10 := congrFun (congrFun hinv 1) 0
  have I11 := congrFun (congrFun hinv 1) 1
  have I00 := congrFun (congrFun hinv 0) 0
  have I31 := congrFun (congrFun hinv 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev] at I10 I11 I00 I31
  have iso : u 0 0 * u 3 1 = u 2 0 * u 1 1 := by
    linear_combination I31 - u 2 1 * h10 + u 0 1 * h30
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → R, w = ![0, u 1 1, 0, u 3 1] := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin 4 → R, φ = ![u 2 0, 0, -u 0 0, 0] := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : M4 R, Y = Matrix.vecMulVec w φ := ⟨_, rfl⟩
  have hYm : Y ∈ uM R := by
    show Y ∈ hAB R ⊓ sp4 R
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · show ∀ i j, ¬ lamW i < lamW j → Y i j = 0
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [lamW, Matrix.vecMulVec_apply]
    · show adj Y = -Y
      ext i j
      fin_cases i <;> fin_cases j <;>
        (try simp [hYd, hw, hφ, adj_apply, sgn, Fin.rev, Matrix.vecMulVec_apply]) <;>
        first
          | linear_combination iso
          | linear_combination (-1 : R) * iso
  have hv : w = Matrix.mulVec u ![-y, 1, 0, 0] := by
    funext i
    fin_cases i <;> simp [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      first
        | linear_combination (-1 : R) * hy1
        | linear_combination y * h10
        | linear_combination (-1 : R) * hy2
        | linear_combination y * h30
        | linear_combination hy1
        | linear_combination hy2
        | linear_combination (-y) * h10
        | linear_combination (-y) * h30
  have hA : Matrix.mulVec (adj u) w = ![-y, 1, 0, 0] := by
    rw [hv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hB0 : Matrix.vecMul φ u 0 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;> ring
  have hB1 : Matrix.vecMul φ u 1 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;>
      linear_combination u 2 0 * hy1 - u 0 0 * hy2
  have hN : adj u * Y * u = Matrix.vecMulVec ![-y, 1, 0, 0] (Matrix.vecMul φ u) := by
    rw [hYd, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hA]
  have hsup : IsSUp (adj u * Y * u) := by
    intro i j hji
    rw [hN, Matrix.vecMulVec_apply]
    fin_cases i <;> fin_cases j <;>
      first
        | (simp [hB0, hB1]; done)
        | (exfalso; simp at hji; done)
        | (exfalso; revert hji; decide)
  rw [Submodule.ne_bot_iff]
  refine ⟨⟨Y, hYm⟩, ?_, ?_⟩
  · exact hsup
  · intro hY0
    have hY : Y = 0 := congrArg Subtype.val hY0
    have f1 : u 1 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 1) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f2 : u 1 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 1) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f3 : u 3 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 3) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f4 : u 3 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 3) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have J : u 2 2 * u 1 1 - u 0 2 * u 3 1 = 1 := by
      linear_combination I11 - u 3 2 * hy1 + u 1 2 * hy2 - y * I10 + y * u 2 2 * h10 -
        y * u 0 2 * h30
    have z00 : u 0 0 = 0 := by linear_combination (-u 0 0) * J + u 2 2 * f2 - u 0 2 * f4
    have z20 : u 2 0 = 0 := by linear_combination (-u 2 0) * J + u 2 2 * f1 - u 0 2 * f3
    have h1 : (1 : R) = 0 := by
      linear_combination (-1 : R) * I00 + u 3 3 * z00 + u 2 3 * h10 - u 1 3 * z20 - u 0 3 * h30
    exact one_ne_zero h1
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem res_entry {R : Type} [CommRing R] [IsLocalRing R] {X X' : M4 R} (hX : Sep X) (h : X' * X = 1) (Y : M4 R)
    (i j : Fin 4) : residue R (X' j j) * residue R (X j j) = 1 ∧
      residue R ((X * Y * X' - Y) i j) = residue R ((X i i - X j j) * X' j j) * residue R (Y i j) := by
  have hoff : ∀ a b, a ≠ b → residue R (X a b) = 0 :=
    fun a b hab => (residue_eq_zero_iff _).2 (hX.off a b hab)
  have kr : ∀ (A B : M4 R), (∀ a b, a ≠ b → residue R (B a b) = 0) →
      ∀ a b, residue R ((A * B) a b) = residue R (A a b) * residue R (B b b) := by
    intro A B hB a b
    rw [Matrix.mul_apply, map_sum, Finset.sum_eq_single b]
    · rw [map_mul]
    · intro c _ hc
      rw [map_mul, hB c b hc, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  have kl : ∀ (A B : M4 R), (∀ a b, a ≠ b → residue R (A a b) = 0) →
      ∀ a b, residue R ((A * B) a b) = residue R (A a a) * residue R (B a b) := by
    intro A B hA a b
    rw [Matrix.mul_apply, map_sum, Finset.sum_eq_single a]
    · rw [map_mul]
    · intro c _ hc
      rw [map_mul, hA a c (Ne.symm hc), zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  have hdiag : ∀ j, residue R (X' j j) * residue R (X j j) = 1 := by
    intro j
    rw [← kr X' X hoff j j, h, Matrix.one_apply_eq, map_one]
  have hoff' : ∀ a b, a ≠ b → residue R (X' a b) = 0 := by
    intro a b hab
    have h0 : residue R (X' a b) * residue R (X b b) = 0 := by
      rw [← kr X' X hoff a b, h, Matrix.one_apply_ne hab, map_zero]
    linear_combination residue R (X' b b) * h0 - residue R (X' a b) * hdiag b
  refine ⟨hdiag j, ?_⟩
  rw [Matrix.sub_apply, map_sub, kr _ _ hoff' i j, kl _ _ hoff i j, map_mul, map_sub]
  linear_combination residue R (Y i j) * hdiag j

theorem UpperTheory.V.Ws.Bl.adBij :
    ∀ (R Γ : Type) [CommRing R] [IsLocalRing R] [Group Γ] (r : Γ →* M4 R) (h : BG r) (s : Γ), Sep (r s) → Function.Bijective fun Y => adU h s Y - Y := by
  intro R Γ _ _ _ r h s hs
  obtain ⟨hfin, -, hmem⟩ := uMFacts R
  haveI := hfin
  let φ : uM R →ₗ[R] uM R := adU h s - LinearMap.id
  have hinv : r s⁻¹ * r s = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hkey : ∀ Y : uM R, φ Y ∈ (maximalIdeal R • ⊤ : Submodule R (uM R)) →
      Y ∈ (maximalIdeal R • ⊤ : Submodule R (uM R)) := by
    intro Y hY
    rw [hmem] at hY ⊢
    intro i j
    by_cases hij : lamW i < lamW j
    · have h1 := hY i j
      have e := res_entry hs hinv (Y : M4 R) i j
      have hu : IsUnit (r s i i - r s j j) := hs.unit i j (ne_of_lt hij)
      have hc : (↑(φ Y) : M4 R) i j = (r s * ↑Y * r s⁻¹ - ↑Y) i j := rfl
      rw [hc, ← residue_eq_zero_iff, e.2, map_mul] at h1
      rw [← residue_eq_zero_iff]
      have hu' : residue R (r s i i - r s j j) ≠ 0 := (hu.map (residue R)).ne_zero
      have hv : residue R (r s⁻¹ j j) ≠ 0 := left_ne_zero_of_mul_eq_one e.1
      exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hu' hv)
    · have hY2 := (Submodule.mem_inf.1 Y.2).1
      rw [hY2 i j hij]
      exact zero_mem _
  have hS : (maximalIdeal R • ⊤ : Submodule R (uM R)) ≤
      (maximalIdeal R • ⊤ : Submodule R (uM R)).comap φ := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  let ψ := Submodule.mapQ _ _ φ hS
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨Y, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hkey Y hq
  letI : Module (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    inferInstanceAs (Module (R ⧸ maximalIdeal R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))))
  letI : IsScalarTower R (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))))
  haveI : Module.Finite (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hsurjA : Function.Surjective (algebraMap R (ResidueField R)) := Ideal.Quotient.mk_surjective
  let ψk := LinearMap.extendScalarsOfSurjective hsurjA ψ
  have hψsurj : Function.Surjective ψ := (LinearMap.injective_iff_surjective (f := ψk)).1 hψinj
  have hrange : LinearMap.range φ = ⊤ := by
    rw [← IsLocalRing.map_mkQ_eq_top, ← LinearMap.range_comp, eq_top_iff]
    intro q _
    obtain ⟨q', rfl⟩ := hψsurj q
    obtain ⟨Y, rfl⟩ := Submodule.mkQ_surjective _ q'
    exact ⟨Y, rfl⟩
  have hsurj : Function.Surjective φ := LinearMap.range_eq_top.1 hrange
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism φ hsurj, hsurj⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

namespace UpperTheory.V.Ws.Bl

end UpperTheory.V.Ws.Bl

private theorem mem_ideal_smul_module_of_entries_mem {A : Type} [CommRing A] (I : Ideal A) (Y : uM A)
    (hY : ∀ i j, (Y : M4 A) i j ∈ I) : Y ∈ I • (⊤ : Submodule A (uM A)) := by
  have h1 : (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,-1,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  have h2 : (!![0,0,0,0; 0,0,1,0; 0,0,0,0; 0,0,0,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  have h3 : (!![0,0,0,0; 0,0,0,0; 0,0,0,0; 1,0,0,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  obtain ⟨hz, ha⟩ := Y.2
  have h32 : (Y : M4 A) 3 2 = -(Y : M4 A) 1 0 := by
    have h := congrFun (congrFun ha 3) 2
    simp [adj, sgn] at h
    rw [h, neg_neg]
  have hd : Y = (Y : M4 A) 1 0 • (⟨_, h1⟩ : uM A) + (Y : M4 A) 1 2 • (⟨_, h2⟩ : uM A)
      + (Y : M4 A) 3 0 • (⟨_, h3⟩ : uM A) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h32] <;> exact hz _ _ (by decide)
  rw [hd]
  exact add_mem (add_mem (Submodule.smul_mem_smul (hY 1 0) trivial)
    (Submodule.smul_mem_smul (hY 1 2) trivial)) (Submodule.smul_mem_smul (hY 3 0) trivial)

private theorem isLocallyConstant_mkQ_adU_of_adicCont {A : Type} [CommRing A] [IsLocalRing A] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [ContinuousInv Γ] (r : Γ →* M4 A) (hb : BG r)
    (hc : ∀ i j, AdicCont (maximalIdeal A) fun g => r g i j) (n : ℕ) (x : uM A) :
    IsLocallyConstant fun g => (lev A (uM A) n).mkQ ((adU hb g) x) := by
  let φ := (Ideal.Quotient.mk (maximalIdeal A ^ n)).mapMatrix (m := Fin 4)
  have hq : ∀ (f : Γ → M4 A), (∀ i j, AdicCont (maximalIdeal A) fun g => f g i j) →
      IsLocallyConstant fun g => φ (f g) := by
    intro f hf
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro M
    have hM : (fun g => φ (f g)) ⁻¹' {M} =
        ⋂ i, ⋂ j, (fun g => Ideal.Quotient.mk (maximalIdeal A ^ n) (f g i j)) ⁻¹' {M i j} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      constructor
      · intro h i j
        rw [← h]
        rfl
      · intro h
        ext i j
        exact h i j
    rw [hM]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hf i j n).isOpen_fiber _
  have hP : IsLocallyConstant fun g => (φ (r g), φ (r g⁻¹)) :=
    (hq _ hc).prodMk (hq (fun g => r g⁻¹) fun i j N => (hc i j N).comp_continuous continuous_inv)
  have key : ∀ g' g : Γ, (φ (r g'), φ (r g'⁻¹)) = (φ (r g), φ (r g⁻¹)) →
      (lev A (uM A) n).mkQ ((adU hb g') x) = (lev A (uM A) n).mkQ ((adU hb g) x) := by
    intro g' g hgg
    obtain ⟨e1, e2⟩ := Prod.mk.inj hgg
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    apply mem_ideal_smul_module_of_entries_mem
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h0 : φ ((↑((adU hb g') x - (adU hb g) x) : M4 A)) = 0 := by
      rw [Submodule.coe_sub]
      change φ (r g' * (x : M4 A) * r g'⁻¹ - r g * (x : M4 A) * r g⁻¹) = 0
      simp only [map_sub, map_mul, e1, e2, sub_self]
    simpa [φ] using congrFun (congrFun h0 i) j
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  have hy : (fun g => (lev A (uM A) n).mkQ ((adU hb g) x)) ⁻¹' {y} =
      ⋃ g ∈ (fun g => (lev A (uM A) n).mkQ ((adU hb g) x)) ⁻¹' {y},
        (fun g => (φ (r g), φ (r g⁻¹))) ⁻¹' {(φ (r g), φ (r g⁻¹))} := by
    ext g'
    constructor
    · intro h
      exact Set.mem_biUnion h rfl
    · intro h
      obtain ⟨g, hg, hgg⟩ := Set.mem_iUnion₂.1 h
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg hgg ⊢
      rw [← hg]
      exact key g' g hgg
  rw [hy]
  exact isOpen_biUnion fun g _ => hP.isOpen_fiber _

private theorem isSUp_mul_mul_of_isUp_isSUp_isUp {A : Type} [CommRing A] (P N Q : M4 A) (hP : IsUp P) (hN : IsSUp N)
    (hQ : IsUp Q) : IsSUp (P * N * Q) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hli : l < i
  · rw [hP i l hli, zero_mul, zero_mul]
  by_cases hkl : k ≤ l
  · rw [hN l k hkl, mul_zero, zero_mul]
  rw [hQ k j (by omega), mul_zero]

theorem UpperTheory.V.Ws.Bl.latU :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (r : G ℚ Ω →* M4 A) (u : M4 A) (h : BlockDiagonalOrdinaryGSpRep S c s B r u),
          Lat (adU h.bg) (Dec (F := ℚ) B) (uPlus u) ∧ (∀ Y, adU h.bg c Y = -Y) ∧ r.ker ≤ (adU h.bg).ker := by
  intro Ω _ _ _ l _ S c s B hp A _ _ _ r u h
  have hinv : ∀ g, r g = 1 → r g⁻¹ = 1 := by
    intro g hg
    calc r g⁻¹ = r g⁻¹ * r g := by rw [hg, mul_one]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have huu : u * adj u = 1 := by
    have h1 : adj u * u = 1 := by
      have := h.sp
      simpa [IsGSp] using this
    exact mul_eq_one_comm.1 h1
  refine ⟨⟨fun n x => isLocallyConstant_mkQ_adU_of_adicCont r h.bg h.cont n x, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg Y hY
    have hg' : g⁻¹ ∈ Dec (F := ℚ) B := (Dec (F := ℚ) B).inv_mem hg
    change IsSUp (adj u * (r g * (Y : M4 A) * r g⁻¹) * u)
    have he : adj u * (r g * (Y : M4 A) * r g⁻¹) * u
        = (adj u * r g * u) * (adj u * (Y : M4 A) * u) * (adj u * r g⁻¹ * u) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc u (adj u), huu, Matrix.one_mul, ← Matrix.mul_assoc u (adj u), huu,
        Matrix.one_mul]
    rw [he]
    exact isSUp_mul_mul_of_isUp_isSUp_isUp _ _ _ (h.flag g hg) hY (h.flag _ hg')
  · intro a Y ha hY
    change IsSUp (adj u * ((a • Y : uM A) : M4 A) * u) at hY
    change IsSUp (adj u * (Y : M4 A) * u)
    intro i j hij
    have h0 := hY i j hij
    rw [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left ha
  · exact flagVec A (r s) u (h.bg.blk s) h.sep h.sp (h.flag s hp.dec) h.char
  · exact ⟨s, hp.dec, adBij A (G ℚ Ω) r h.bg s h.sep⟩
  · intro Y
    have hc2 : r c * r c = 1 := by
      rw [h.cc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [eAB]
    have hci : r c⁻¹ = r c := by
      calc r c⁻¹ = r c⁻¹ * (r c * r c) := by rw [hc2, Matrix.mul_one]
        _ = r (c⁻¹ * c) * r c := by rw [map_mul, Matrix.mul_assoc]
        _ = r c := by rw [inv_mul_cancel, map_one, Matrix.one_mul]
    obtain ⟨hz, _⟩ := Y.2
    apply Subtype.ext
    change r c * (Y : M4 A) * r c⁻¹ = -(Y : M4 A)
    rw [hci, h.cc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eAB, hz 0 0 (by decide), hz 0 1 (by decide), hz 0 2 (by decide), hz 0 3 (by decide),
        hz 1 1 (by decide), hz 1 3 (by decide), hz 2 0 (by decide), hz 2 1 (by decide),
        hz 2 2 (by decide), hz 2 3 (by decide), hz 3 1 (by decide), hz 3 3 (by decide)]
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearMap.ext
    intro Y
    apply Subtype.ext
    change r g * (Y : M4 A) * r g⁻¹ = (Y : M4 A)
    rw [hg, hinv g hg, Matrix.one_mul, Matrix.mul_one]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem ac_mul {S A : Type} [TopologicalSpace S] [CommRing A] {I : Ideal A}
    {M N : S → M4 A} (hM : ∀ a b, AdicCont I fun s => M s a b) (hN : ∀ a b, AdicCont I fun s => N s a b) :
    ∀ a b, AdicCont I fun s => (M s * N s) a b := by
  intro a b n
  simp only [Matrix.mul_apply, map_sum, map_mul, Fin.sum_univ_four, map_add]
  exact ((((hM a 0 n).mul (hN 0 b n)).add ((hM a 1 n).mul (hN 1 b n))).add ((hM a 2 n).mul (hN 2 b n))).add
    ((hM a 3 n).mul (hN 3 b n))

private theorem twist_mul {R Γ : Type} [CommRing R] [Group Γ] {r : Γ →* M4 R} (hb : ∀ g, IsBlock (r g)) {z : Γ → M4 R}
    (hz : ∀ g, z g ∈ hAB R) (coc : ∀ g h, z (g * h) = z g + r g * z h * r g⁻¹) (g h : Γ) :
    (1 + z (g * h)) * r (g * h) = (1 + z g) * r g * ((1 + z h) * r h) := by
  have e : r g⁻¹ * r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e0 : z g * (r g * z h * r h) = 0 := hAB_mul_hAB (hz g) (hAB_mul_mul (hb g) (hz h) (hb h))
  have e1 : r g * z h * r g⁻¹ * (r g * r h) = r g * z h * r h := by
    rw [mul_assoc, ← mul_assoc (r g⁻¹), e, one_mul]
  rw [coc, map_mul, ← add_assoc, add_mul, e1]
  calc _ = (1 + z g) * (r g * r h) + r g * z h * r h + z g * (r g * z h * r h) := by rw [e0, add_zero]
    _ = _ := by noncomm_ring

theorem UpperTheory.V.Ws.Bl.cocA :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (r : G ℚ Ω →* M4 A) (u : M4 A), IsAdicComplete (maximalIdeal A) A → (l : A) ∈ maximalIdeal A → BlockDiagonalOrdinaryGSpRep S c s B r u →
          ∃ (r' : G ℚ Ω →* M4 A) (z : G ℚ Ω → M4 A) (y : M4 A), (∀ g, r' g = (1 + z g) * r g) ∧ (∀ i j, AdicCont (maximalIdeal A) fun g => r' g i j) ∧ (∀ g, z g ∈ uM A) ∧ y ∈ uM A ∧
            (∀ g i j, z g i j ∈ maximalIdeal A) ∧ z c = 0 ∧ (∀ g ∈ neSet l r.ker, z g = 0) ∧ (∀ h ∈ Dec (F := ℚ) B, IsSUp (adj u * (z h - (r h * y * r h⁻¹ - y)) * u)) ∧ z ≠ 0 := by
  intro hP Ω _ _ _ l _ S c s B hpos A _ _ _ _ r u hc hl hb
  obtain ⟨hfin, hfree, hI⟩ := uMFacts A
  obtain ⟨hlat, hcc, hker⟩ := latU S c s B hpos A r u hb
  obtain ⟨z, y, hz, hne⟩ := cocT hP S c s B hpos A (uM A) (adU hb.bg) (uPlus u) r.ker hc hl hlat
    (adBij A _ r hb.bg s hb.sep) hcc hker hb.unr
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have htm : t ∈ maximalIdeal A := ht.not_isUnit
  have coc : ∀ g h, (t • z (g * h)).1 = (t • z g).1 + r g * (t • z h).1 * r g⁻¹ := fun g h => by
    rw [hz.coc, smul_add, ← map_smul, Submodule.coe_add, adU_val]
  have z1 : z 1 = 0 := by
    have := hz.coc 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    exact left_eq_add.mp this
  have zc : ∀ i j, AdicCont (maximalIdeal A) fun g => (1 + (t • z g).1) i j := fun i j n => by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hz.cont n) g] with g' e
    have e1 : z g' - z g ∈ lev A (uM A) n := (Submodule.Quotient.eq _).1 e
    have e2 := (hI _ _).1 (Submodule.smul_mem _ t e1) i j
    rw [Ideal.Quotient.eq]
    convert e2 using 1
    simp [smul_sub, mul_sub]
  refine ⟨MonoidHom.mk ⟨fun g => (1 + (t • z g).1) * r g, by simp [z1]⟩
      (twist_mul hb.bg.blk (fun g => (t • z g).2.1) coc), fun g => (t • z g).1, (t • y).1, fun _ => rfl,
    ac_mul zc hb.cont, fun g => (t • z g).2, (t • y).2, fun g i j => ?_, by simp [hz.cz], fun g hg => by simp [hz.kill g hg],
    fun h hh => ?_, fun e => hne (funext fun g => ?_)⟩
  · exact Ideal.mul_mem_right _ _ htm
  · have := (uPlus u).smul_mem t (hz.loc h hh)
    rw [smul_sub, smul_sub, ← map_smul] at this
    exact this
  · have e1 : t • (z g).1 = 0 := congrFun e g
    exact Subtype.ext ((smul_eq_zero.1 e1).resolve_left ht.ne_zero)
end
