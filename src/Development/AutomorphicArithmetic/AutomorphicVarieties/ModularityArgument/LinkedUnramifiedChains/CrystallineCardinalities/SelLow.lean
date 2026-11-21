import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LocHigh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CjFacts

section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J.AdjointKernelOpen

variable {l : ℕ} [Fact l.Prime] {κ : Type} [Field κ] {F : Frame l κ} {C : Type} [CommRing C]

private theorem r_ker_open (hdel : IsOpen (F.del.ker : Set F.Γ)) (B : Box F 3 C)
    (h : ∀ i j, IsLocallyConstant fun s => (B.r s).mat i j) : IsOpen (B.r.ker : Set F.Γ) := by
  have hset : (B.r.ker : Set F.Γ) = (F.del.ker : Set F.Γ) ∩
      ⋂ i, ⋂ j, (fun s => (B.r s).mat i j) ⁻¹' {(1 : Matrix (Fin 3) (Fin 3) C) i j} := by
    ext s
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [← B.nu s]
    constructor
    · intro hs
      refine ⟨by rw [hs]; rfl, fun i j => ?_⟩
      rw [hs]
      rfl
    · rintro ⟨h1, h2⟩
      apply SemidirectProduct.ext
      · apply Units.ext
        ext i j
        exact h2 i j
      · exact h1
  rw [hset]
  exact hdel.inter (isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => (h i j).isOpen_fiber _)

end UpperTheory.V.Z.J.AdjointKernelOpen

open UpperTheory.V.Z.J.AdjointKernelOpen in
theorem UpperTheory.V.Z.J.adOpen :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (B : Box F 3 O) (k : ℕ), B.Cont (maximalIdeal O) → IsOpen ((adK B k).ker : Set F.Γ) := by
  intro l _ O _ _ _ _ _ F C₀ hF hl B k hB
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨N, hN⟩ := (okFin l O hl).2.2.2.2.1 k
  have hK : IsOpen ((boxK B k).r.ker : Set F.Γ) := by
    refine r_ker_open hF.del_open (boxK B k) fun i j => ?_
    have hc := (hB i j N).comp (Ideal.Quotient.factor hN)
    convert hc using 1
    funext s
    simp [Ideal.Quotient.factor_mk, boxK, Box.map, GG.map, GG.mat]
  refine Subgroup.isOpen_mono (fun s hs => ?_) hK
  rw [MonoidHom.mem_ker] at hs ⊢
  ext x
  simp [adK, Box.ad, adRep, hs]
end

section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem arch_gen {R : Type} [CommRing R] [Finite R] (h2 : IsUnit (2 : R)) (y : GG 3 R)
    (hy : y * y = 1) (hr : y.right = -1) :
    {X : Matrix (Fin 3) (Fin 3) R | GG.ad 3 R y X = X}.ncard ≤ Nat.card R ^ 3 := by
  obtain ⟨a, s⟩ := y
  obtain rfl : s = -1 := hr
  have h : ((-1 : ℤˣ) = 1) = False := by decide
  have h1 : a * theta a = 1 := by
    have := congrArg SemidirectProduct.left hy
    simpa [SemidirectProduct.mul_left] using this
  have h3 : theta a = a⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h4 : (a : Matrix (Fin 3) (Fin 3) R) = Jmat R 3 * (a : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 := by
    rw [← theta_inv_val, h3, inv_inv]
  have hJ := Jmat_mul_Jmat (R := R) 3
  set A : Matrix (Fin 3) (Fin 3) R := a.val with hA
  set A' : Matrix (Fin 3) (Fin 3) R := (a⁻¹ : GL (Fin 3) R).val with hA'
  have hAA : A' * A = 1 := by rw [hA, hA', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAA' : A * A' = 1 := by rw [hA, hA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hB : (A * Jmat R 3)ᵀ = A * Jmat R 3 := by
    rw [Matrix.transpose_mul, Jmat_transpose]
    conv_rhs => rw [h4, Matrix.mul_assoc, hJ, Matrix.mul_one]
  have key : ∀ X : Matrix (Fin 3) (Fin 3) R, GG.ad 3 R ⟨a, -1⟩ X = X →
      (X * (A * Jmat R 3))ᵀ = -(X * (A * Jmat R 3)) := by
    intro X hX
    have hX' : A * (-(Jmat R 3 * Xᵀ * Jmat R 3)) * A' = X := by
      simpa only [GG.ad_apply, GG.adFun, GG.mat, h, if_false, thetaLie] using hX
    rw [Matrix.transpose_mul, hB]
    conv_rhs => rw [← hX']
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A' A, hAA, Matrix.one_mul, hJ, Matrix.mul_one]
  have anti : ∀ Y : Matrix (Fin 3) (Fin 3) R, Yᵀ = -Y → Y 0 1 = 0 → Y 0 2 = 0 → Y 1 2 = 0 → Y = 0 := by
    intro Y hY e1 e2 e3
    have hs : ∀ i j, Y j i = -Y i j := fun i j => congrFun (congrFun hY i) j
    have hd : ∀ i, Y i i = 0 := fun i => by
      apply h2.mul_left_cancel
      have := hs i i
      linear_combination this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, e1, e2, e3, hs 0 1, hs 0 2, hs 1 2]
  let f : Matrix (Fin 3) (Fin 3) R → R × R × R := fun X =>
    ((X * (A * Jmat R 3)) 0 1, (X * (A * Jmat R 3)) 0 2, (X * (A * Jmat R 3)) 1 2)
  have hinj : Set.InjOn f {X : Matrix (Fin 3) (Fin 3) R | GG.ad 3 R ⟨a, -1⟩ X = X} := by
    intro X hX X' hX' hf
    simp only [f, Prod.mk.injEq] at hf
    have h0 : X * (A * Jmat R 3) - X' * (A * Jmat R 3) = 0 := by
      apply anti
      · rw [Matrix.transpose_sub, key X hX, key X' hX']; abel
      · rw [Matrix.sub_apply, hf.1, sub_self]
      · rw [Matrix.sub_apply, hf.2.1, sub_self]
      · rw [Matrix.sub_apply, hf.2.2, sub_self]
    have h5 := congrArg (· * (Jmat R 3 * A')) (sub_eq_zero.1 h0)
    simp only [Matrix.mul_assoc] at h5
    rwa [← Matrix.mul_assoc (Jmat R 3), hJ, Matrix.one_mul, hAA', Matrix.mul_one, Matrix.mul_one] at h5
  calc _ ≤ (Set.univ : Set (R × R × R)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun _ _ => Set.mem_univ _) hinj (Set.toFinite _)
    _ = Nat.card R ^ 3 := by rw [Set.ncard_univ, Nat.card_prod, Nat.card_prod]; ring

theorem UpperTheory.V.Z.J.archUp :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → l ≠ 2 → ∀ (x : GG 3 O), x * x = 1 → x.right = -1 → ∀ k, 0 < k → {X : Matrix (Fin 3) (Fin 3) (Ok l O k) | GG.ad 3 (Ok l O k) (GG.map (Ideal.Quotient.mk _) x) X = X}.ncard ≤ Nat.card (Ok l O k) ^ 3 := by
  intro l hl O _ _ _ _ _ hl0 hl2 x hx hr k _
  have hfin : Finite (Ok l O k) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hne : Ideal.span {(l : O) ^ k} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero _ hl0
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
    haveI : Finite (O ⧸ maximalIdeal O) := (inferInstance : Finite (ResidueField O))
    have hf : Finite (O ⧸ maximalIdeal O ^ n) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hn] at hf
    exact hf
  have h2 : IsUnit (2 : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h
    have h' : ((2 : ℕ) : ResidueField O) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h'
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h')
  have h2' : IsUnit (2 : Ok l O k) := by
    simpa only [map_ofNat] using h2.map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}))
  exact arch_gen h2' _ (by rw [← map_mul, hx, map_one]) hr
end

section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem exists_nat_sub_mem_span_pow_and_toZModPow_eq_and_toZMod_eq (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (k : ℕ) (hk : 0 < k) (a : ℤ_[l]) :
    ∃ n : ℕ, algebraMap ℤ_[l] O a - n ∈ Ideal.span {(l : O) ^ k} ∧
      PadicInt.toZModPow k a = n ∧ PadicInt.toZMod a = n := by
  have h1 : PadicInt.toZModPow k a = ((PadicInt.toZModPow k a).val : ZMod (l ^ k)) :=
    (ZMod.natCast_zmod_val _).symm
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (PadicInt.toZModPow k a).val = n := ⟨_, rfl⟩
  rw [hn] at h1
  have h2 : a - (n : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ← h1, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp h2
  have ha : a = (n : ℤ_[l]) + (l : ℤ_[l]) ^ k * t := by
    rw [← ht]; ring
  refine ⟨n, ?_, h1, ?_⟩
  · rw [Ideal.mem_span_singleton]
    refine ⟨algebraMap ℤ_[l] O t, ?_⟩
    rw [ha, map_add, map_mul, map_pow, map_natCast, map_natCast]
    ring
  · rw [ha, map_add, map_mul, map_pow, map_natCast, map_natCast, ZMod.natCast_self,
      zero_pow hk.ne', zero_mul, add_zero]

theorem UpperTheory.V.Z.J.dualZero :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ k, 0 < k → HomMu l k F.eps (adK B k) = {0} := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B hL hB hC k hk
  haveI : CharP (ResidueField O) l := IsCoef.char
  have hlm : (l : O) ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have hI0m : Ideal.span {(l : O) ^ k} ≤ maximalIdeal O := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_mem_of_mem _ hlm _ hk
  set π : O →+* Ok l O k := Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) with hπ
  set φ : Ok l O k →+* ResidueField O :=
    Ideal.Quotient.lift (Ideal.span {(l : O) ^ k}) (IsLocalRing.residue O)
      (fun x hx => (IsLocalRing.residue_eq_zero_iff x).mpr (hI0m hx)) with hφ
  have hφπ : ∀ x, φ (π x) = IsLocalRing.residue O x := fun x => rfl
  have hπs : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hunit : ∀ x : Ok l O k, φ x ≠ 0 → IsUnit x := by
    intro x hx
    obtain ⟨y, rfl⟩ := hπs x
    rw [hφπ] at hx
    have hy : IsUnit y := by
      by_contra h
      exact hx ((IsLocalRing.residue_eq_zero_iff y).mpr ((IsLocalRing.mem_maximalIdeal y).mpr h))
    exact hy.map π
  set I : Ideal (Ok l O k) := (maximalIdeal O).map π with hIdef
  have hIφ : ∀ x ∈ I, φ x = 0 := by
    have hle : I ≤ RingHom.ker φ := by
      rw [hIdef, Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker, hφπ]
      exact (IsLocalRing.residue_eq_zero_iff y).mpr hy
    intro x hx
    exact hle hx
  have hφI : ∀ x, φ x = 0 → x ∈ I := by
    intro x hx
    obtain ⟨y, rfl⟩ := hπs x
    rw [hφπ, IsLocalRing.residue_eq_zero_iff] at hx
    exact Ideal.mem_map_of_mem π hx
  have hjac : I ≤ Ideal.jacobson ⊥ := by
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    apply hunit
    rw [map_add, map_mul, hIφ x hx, zero_mul, zero_add, map_one]
    exact one_ne_zero
  ext f
  rw [Set.mem_singleton_iff]
  constructor
  swap
  · rintro rfl
    intro s x
    simp
  intro hf
  have hf' : ∀ s x, f (adK B k s x) = PadicInt.toZModPow k (F.eps s : ℤ_[l]) * f x := hf
  have hlin : ∀ (s : F.Γ) (c : Ok l O k) (x : Matrix (Fin 3) (Fin 3) (Ok l O k)),
      adK B k s (c • x) = c • adK B k s x := by
    intro s c x
    show (boxK B k).ad s (c • x) = c • (boxK B k).ad s x
    exact map_smul _ _ _
  have hbr : ∀ (a : ℤ_[l]) (x : Matrix (Fin 3) (Fin 3) (Ok l O k)),
      f (π (algebraMap ℤ_[l] O a) • x) = PadicInt.toZModPow k a * f x := by
    intro a x
    obtain ⟨n, hn1, hn2, -⟩ := exists_nat_sub_mem_span_pow_and_toZModPow_eq_and_toZMod_eq l O k hk a
    have he : π (algebraMap ℤ_[l] O a) = (n : Ok l O k) := by
      rw [← sub_eq_zero, ← map_natCast π, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hn1
    rw [he, hn2, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
  let N : Submodule (Ok l O k) (Matrix (Fin 3) (Fin 3) (Ok l O k)) :=
    { carrier := {x | ∀ c : Ok l O k, f (c • x) = 0}
      add_mem' := by
        intro x y hx hy c
        rw [smul_add, map_add, hx c, hy c, add_zero]
      zero_mem' := by
        intro c
        rw [smul_zero, map_zero]
      smul_mem' := by
        intro d x hx c
        rw [smul_smul]
        exact hx _ }
  have hP : ∀ (s : F.Γ) x, adK B k s x - π (algebraMap ℤ_[l] O (F.eps s)) • x ∈ N := by
    intro s x c
    rw [smul_sub, ← hlin, smul_comm, map_sub, hf' s, hbr]
    ring
  suffices hN : (⊤ : Submodule (Ok l O k) (Matrix (Fin 3) (Fin 3) (Ok l O k))) ≤ N by
    ext x
    have := hN (Submodule.mem_top (x := x)) 1
    rw [one_smul] at this
    simpa using this
  have hIm : ∀ x : Matrix (Fin 3) (Fin 3) (Ok l O k), (∀ i j, x i j ∈ I) →
      x ∈ I • (⊤ : Submodule (Ok l O k) (Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
    intro x hx
    rw [Matrix.matrix_eq_sum_single x]
    refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
    rw [show Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : Ok l O k) by simp]
    exact Submodule.smul_mem_smul (hx i j) Submodule.mem_top
  have hkey : ∀ (a b : Fin 3) (s : F.Γ),
      φ (adK B k s (Matrix.single a b 1) a b) ≠ φ (π (algebraMap ℤ_[l] O (F.eps s))) →
      (∀ i j, ¬(a = i ∧ b = j) → φ (adK B k s (Matrix.single a b 1) i j) = 0) →
      Matrix.single a b (1 : Ok l O k) ∈ N ⊔ I • ⊤ := by
    intro a b s hu hz
    have hYN := hP s (Matrix.single a b 1)
    set Y := adK B k s (Matrix.single a b 1) - π (algebraMap ℤ_[l] O (F.eps s)) •
      Matrix.single a b (1 : Ok l O k) with hY
    have huu : IsUnit (Y a b) := by
      apply hunit
      rw [hY, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul, mul_one,
        map_sub]
      exact sub_ne_zero.mpr hu
    obtain ⟨v, hv⟩ := huu
    have hR : Y - Y a b • Matrix.single a b 1 ∈
        I • (⊤ : Submodule (Ok l O k) (Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
      apply hIm
      intro i j
      by_cases hij : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := hij
        rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul, mul_one,
          sub_self]
        exact I.zero_mem
      · apply hφI
        simp only [hY, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply_of_ne _ _ _ _ _ hij,
          smul_eq_mul, mul_zero, sub_zero]
        exact hz i j hij
    have hsplit : Matrix.single a b (1 : Ok l O k) =
        (↑v⁻¹ : Ok l O k) • Y - (↑v⁻¹ : Ok l O k) • (Y - Y a b • Matrix.single a b 1) := by
      rw [smul_sub (↑v⁻¹ : Ok l O k) Y, sub_sub_cancel, smul_smul, ← hv, Units.inv_mul, one_smul]
    rw [hsplit]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ hYN))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ hR))
  have hE : ∀ a b : Fin 3, Matrix.single a b (1 : Ok l O k) ∈ N ⊔ I • ⊤ := by
    have hres : ∀ x : O, res O O x = IsLocalRing.residue O x := by
      intro x
      simp [res, RingEquiv.symm_apply_eq]
    have had1 : ∀ s : F.Γ, (B.r s).right = 1 → ∀ X : Matrix (Fin 3) (Fin 3) (Ok l O k),
        adK B k s X = π.mapMatrix (B.r s).mat * X * π.mapMatrix ↑(B.r s).left⁻¹ := by
      intro s hs X
      show GG.adFun ((boxK B k).r s) X = _
      simp only [GG.adFun]
      rw [if_pos (show ((boxK B k).r s).right = 1 from hs)]
      rfl
    have hG0 : ∀ (h : F.G0) (a b i j : Fin 3), φ (adK B k ↑h (Matrix.single a b 1) i j) =
        if a = i ∧ b = j then ((F.Ψ ↑h ^ (w 3 a - w 3 b) : (ResidueField O)ˣ) : ResidueField O)
        else 0 := by
      intro h a b i j
      have hr : (B.r ↑h).right = 1 := by rw [B.nu]; exact h.2
      have hM : (B.r ↑h).mat = ρ.r h := hB.res h
      have hD : ∀ p q, IsLocalRing.residue O ((B.r ↑h).mat p q) =
          if p = q then ((F.Ψ ↑h ^ w 3 p : (ResidueField O)ˣ) : ResidueField O) else 0 := by
        intro p q
        rw [hM, ← hres]
        split_ifs with hpq
        · subst hpq; exact hL.2.1.1 h p
        · exact hL.2.2 h p q hpq
      have hinv : (B.r ↑h).mat * (↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O) = 1 :=
        Units.mul_inv _
      have hR : ∀ p q, IsLocalRing.residue O ((↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O) p q) =
          if p = q then (((F.Ψ ↑h ^ w 3 p)⁻¹ : (ResidueField O)ˣ) : ResidueField O) else 0 := by
        intro p q
        have e := congrArg (fun A => IsLocalRing.residue O (A p q)) hinv
        simp only [Matrix.mul_apply, map_sum, map_mul, hD, ite_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true, Matrix.one_apply, apply_ite (IsLocalRing.residue O), map_one,
          map_zero] at e
        have hu : ((F.Ψ ↑h ^ w 3 p : (ResidueField O)ˣ) : ResidueField O) ≠ 0 := Units.ne_zero _
        split_ifs with hpq
        · rw [if_pos hpq] at e
          calc _ = (((F.Ψ ↑h ^ w 3 p)⁻¹ : (ResidueField O)ˣ) : ResidueField O) *
                (((F.Ψ ↑h ^ w 3 p : (ResidueField O)ˣ) : ResidueField O) *
                  IsLocalRing.residue O ((↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O) p q)) := by
                rw [← mul_assoc, Units.inv_mul, one_mul]
            _ = _ := by rw [e, mul_one]
        · rw [if_neg hpq] at e
          exact (mul_eq_zero.mp e).resolve_left hu
      have hDm : (IsLocalRing.residue O).mapMatrix (B.r ↑h).mat =
          Matrix.diagonal (fun p => ((F.Ψ ↑h ^ w 3 p : (ResidueField O)ˣ) : ResidueField O)) := by
        ext p q
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, hD, Matrix.diagonal_apply]
      have hRm : (IsLocalRing.residue O).mapMatrix (↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O) =
          Matrix.diagonal (fun p => (((F.Ψ ↑h ^ w 3 p)⁻¹ : (ResidueField O)ˣ) : ResidueField O)) := by
        ext p q
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, hR, Matrix.diagonal_apply]
      have hφX : φ.mapMatrix (Matrix.single a b (1 : Ok l O k)) = Matrix.single a b 1 := by
        ext p q
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply, Matrix.single_apply]
        split_ifs <;> simp
      have e1 : φ (adK B k ↑h (Matrix.single a b 1) i j) =
          ((IsLocalRing.residue O).mapMatrix (B.r ↑h).mat * φ.mapMatrix (Matrix.single a b 1) *
            (IsLocalRing.residue O).mapMatrix (↑(B.r ↑h).left⁻¹ : Matrix (Fin 3) (Fin 3) O)) i j := by
        rw [had1 _ hr]
        show φ.mapMatrix (_ * _ * _) i j = _
        rw [map_mul, map_mul]
        rfl
      rw [e1, hDm, hRm, hφX, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
      split_ifs with hab
      · obtain ⟨rfl, rfl⟩ := hab
        rw [mul_one, ← Units.val_mul, ← _root_.zpow_neg, ← _root_.zpow_add, ← sub_eq_add_neg]
      · simp
    have hom : ∀ s : F.Γ, φ (π (algebraMap ℤ_[l] O (F.eps s : ℤ_[l]))) =
        ((F.om (ResidueField O) s : (ResidueField O)ˣ) : ResidueField O) := by
      intro s
      obtain ⟨n, hn1, -, hn3⟩ := exists_nat_sub_mem_span_pow_and_toZModPow_eq_and_toZMod_eq l O k hk (F.eps s : ℤ_[l])
      have he : π (algebraMap ℤ_[l] O (F.eps s : ℤ_[l])) = (n : Ok l O k) := by
        rw [← sub_eq_zero, ← map_natCast π, ← map_sub]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hn1
      rw [he, map_natCast]
      simp [Frame.om, hn3]
    have htheta : ∀ (Y : Matrix (Fin 3) (Fin 3) (Ok l O k)) (i j : Fin 3),
        thetaLie Y i j = -Y j.rev i.rev := by
      intro Y i j
      fin_cases i <;> fin_cases j <;> simp [thetaLie, Jmat, Matrix.mul_apply, Fin.sum_univ_three] <;> rfl
    have hc : ∀ Y : Matrix (Fin 3) (Fin 3) (Ok l O k), adK B k F.c Y = thetaLie Y := by
      intro Y
      have h1 : (B.r F.c).left = 1 := Units.ext hB.atc
      have h2 : (B.r F.c).right ≠ 1 := by rw [B.nu, hF.del_c]; decide
      show GG.adFun ((boxK B k).r F.c) Y = _
      simp only [GG.adFun]
      rw [if_neg (show ((boxK B k).r F.c).right ≠ 1 from h2)]
      have h3 : ((boxK B k).r F.c).mat = 1 := by
        show π.mapMatrix (B.r F.c).mat = 1
        rw [hB.atc, map_one]
      have h4 : (↑((boxK B k).r F.c).left⁻¹ : Matrix (Fin 3) (Fin 3) (Ok l O k)) = 1 := by
        show π.mapMatrix (↑(B.r F.c).left⁻¹ : Matrix (Fin 3) (Fin 3) O) = 1
        rw [h1, inv_one, Units.val_one, map_one]
      rw [h3, h4, one_mul, mul_one]
    have L1 : ∀ a b : Fin 3, (w 3 a - w 3 b = 0 ∨ w 3 a - w 3 b = 1 ∨ w 3 a - w 3 b = -1) →
        Matrix.single a b (1 : Ok l O k) ∈ N ⊔ I • ⊤ := by
      intro a b hw
      rcases hw with h0 | h1
      · obtain ⟨g, hg⟩ := hF.f2a
        apply hkey a b ↑g
        · rw [hG0, if_pos ⟨rfl, rfl⟩, hom, h0, zpow_zero, Units.val_one]
          intro heq
          exact hg (Units.val_eq_one.mp heq.symm)
        · intro i j hij
          rw [hG0, if_neg hij]
      · obtain ⟨g, hg⟩ := hF.f2b (w 3 b - w 3 a) (by omega)
        apply hkey a b ↑g
        · rw [hG0, if_pos ⟨rfl, rfl⟩, hom]
          intro heq
          apply hg
          apply Units.ext
          rw [Units.val_mul, ← heq, ← Units.val_mul, ← _root_.zpow_add, sub_add_sub_cancel, sub_self,
            zpow_zero]
        · intro i j hij
          rw [hG0, if_neg hij]
    have L2 : ∀ a b : Fin 3, b = a.rev → (w 3 a - w 3 b = 2 ∨ w 3 a - w 3 b = -2) →
        Matrix.single a b (1 : Ok l O k) ∈ N ⊔ I • ⊤ := by
      intro a b hb hw
      obtain ⟨g, hg⟩ := hF.f2c (w 3 b - w 3 a) (by omega)
      subst hb
      rcases Int.units_eq_one_or (F.del g) with hd | hd
      · have eG := fun i j => (hG0 ⟨g, hd⟩ a a.rev i j :
          φ (adK B k g (Matrix.single a a.rev 1) i j) = _)
        have hdk : ((F.delK (ResidueField O) g : (ResidueField O)ˣ) : ResidueField O) = 1 := by
          simp [Frame.delK, hd]
        apply hkey a a.rev g
        · rw [eG, if_pos ⟨rfl, rfl⟩, hom]
          intro heq
          apply hg
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, hdk, mul_one, ← heq, ← Units.val_mul, ← _root_.zpow_add,
            sub_add_sub_cancel, sub_self, zpow_zero]
        · intro i j hij
          rw [eG, if_neg hij]
      · have hmem : F.c⁻¹ * g ∈ F.del.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hF.del_c, hd]
          decide
        have hΨ : F.Ψ (F.c⁻¹ * g) = F.Ψ g := by
          rw [map_mul, map_inv, hF.Ψ_c, inv_one, one_mul]
        have hsplit : ∀ X, adK B k g X = thetaLie (adK B k (F.c⁻¹ * g) X) := by
          intro X
          rw [← hc]
          conv_lhs => rw [show g = F.c * (F.c⁻¹ * g) by group]
          rw [map_mul]
          rfl
        have eG := fun i j => (hG0 ⟨F.c⁻¹ * g, hmem⟩ a a.rev i j :
          φ (adK B k (F.c⁻¹ * g) (Matrix.single a a.rev 1) i j) = _)
        have hdk : ((F.delK (ResidueField O) g : (ResidueField O)ˣ) : ResidueField O) = -1 := by
          simp [Frame.delK, hd]
        apply hkey a a.rev g
        · rw [hsplit, htheta, Fin.rev_rev, map_neg, eG, if_pos ⟨rfl, rfl⟩, hom]
          dsimp only
          rw [hΨ]
          intro heq
          apply hg
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, hdk, ← heq, mul_neg_one, neg_mul, neg_neg,
            ← Units.val_mul, ← _root_.zpow_add, sub_add_sub_cancel, sub_self, zpow_zero]
        · intro i j hij
          rw [hsplit, htheta, map_neg, eG, if_neg, neg_zero]
          rintro ⟨h1, h2⟩
          apply hij
          refine ⟨Fin.rev_injective h2, ?_⟩
          rw [h1, Fin.rev_rev]
    intro a b
    fin_cases a <;> fin_cases b
    all_goals first
      | exact L1 _ _ (by decide)
      | exact L2 _ _ (by decide) (by decide)
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := I) Module.Finite.fg_top hjac
  intro x _
  rw [Matrix.matrix_eq_sum_single x]
  refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
  rw [show Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : Ok l O k) by simp]
  exact Submodule.smul_mem _ _ (hE i j)
end

section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private theorem jtj {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) i j = X j.rev i.rev := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.transpose_apply] <;> decide

private theorem count {A Q : Type} [AddCommGroup A] [AddCommGroup Q] [Finite Q] (S T : Set A) (H : AddSubgroup A)
    (hH : (H : Set A) = S) (hS : S.Finite) (hT : T ⊆ S) (f : A →+ Q) (hf : ∀ x ∈ S, f x = 0 → x ∈ T) :
    S.ncard ≤ T.ncard * Nat.card Q := by
  subst hH
  haveI : Finite H := hS.to_subtype
  have hTf : T.Finite := hS.subset hT
  haveI : Finite T := hTf.to_subtype
  let g : H →+ Q := f.comp H.subtype
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  have h2 : Nat.card (H ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv
  have h3 : Nat.card g.range ≤ Nat.card Q :=
    Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
  have h4 : Nat.card g.ker ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, hf x.1.1 x.1.2 (AddMonoidHom.mem_ker.mp x.2)⟩) ?_
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext (Subtype.ext hxy)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq T]
  change Nat.card H ≤ _
  rw [h1, h2, mul_comm]
  exact Nat.mul_le_mul h4 h3

private theorem core {R Γ : Type} [CommRing R] [Group Γ] (r : Γ →* GG 3 R) (c g : Γ)
    (hc : c * c = 1) (hc1 : (r c).mat = 1) (hc2 : (r c).right = -1) (hg : (r g).right = 1)
    (z : Γ → Matrix (Fin 3) (Fin 3) R) (hz : ∀ s t, z (s * t) = z s + (r s).adFun (z t))
    (e : z c 0 0 = 0 ∧ z c 0 1 = 0 ∧ z c 1 0 = 0 ∧ z c 0 2 = 0 ∧ z c 2 0 = 0 ∧ z c 1 1 = 0)
    (e1 : (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) 0 1 = 0)
    (e2 : (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) 1 0 = 0) :
    z c = 0 ∧ ∀ i j, i ≠ j → (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) i j = 0 := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hleft : (r c).left = 1 := Units.ext hc1
  have ad1 : ∀ (x : GG 3 R) X, x.right = 1 →
      x.adFun X = x.mat * X * ((x.left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro x X hx
    unfold GG.adFun
    rw [if_pos hx]
  have adc : ∀ X, (r c).adFun X = thetaLie X := by
    intro X
    unfold GG.adFun
    rw [if_neg (by rw [hc2]; exact hne), hc1, hleft, inv_one, Units.val_one, one_mul, mul_one]
  have ad0 : ∀ (x : GG 3 R), x.adFun 0 = 0 := by
    intro x
    unfold GG.adFun thetaLie
    simp
  have z1 : z 1 = 0 := by
    have h := hz 1 1
    rw [mul_one, map_one, ad1 _ _ (by simp)] at h
    simpa [GG.mat] using h
  have hsym : ∀ i j, z c i j = z c j.rev i.rev := by
    have h := hz c c
    rw [hc, z1, adc] at h
    intro i j
    have h2 : z c = Jmat R 3 * (z c)ᵀ * Jmat R 3 := by
      unfold thetaLie at h
      rw [eq_comm, add_neg_eq_zero] at h
      exact h
    have h3 := congrFun (congrFun h2 i) j
    rwa [jtj] at h3
  have r0 : (0 : Fin 3).rev = 2 := rfl
  have r1 : (1 : Fin 3).rev = 1 := rfl
  have r2 : (2 : Fin 3).rev = 0 := rfl
  have hzc : z c = 0 := by
    obtain ⟨e00, e01, e10, e02, e20, e11⟩ := e
    have s22 := hsym 2 2
    have s12 := hsym 1 2
    have s21 := hsym 2 1
    simp only [r1, r2] at s22 s12 s21
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.zero_apply] <;> first | exact e00 | exact e01 | exact e10 | exact e02 | exact e20 | exact e11 | exact s22.trans e00 | exact s12.trans e01 | exact s21.trans e10
  refine ⟨hzc, ?_⟩
  set A : GL (Fin 3) R := (r g).left with hA
  have hgi : (r g⁻¹).right = 1 := by rw [map_inv, SemidirectProduct.inv_right, hg, inv_one]
  have hgil : (r g⁻¹).left = A⁻¹ := by
    rw [map_inv, SemidirectProduct.inv_left, hg, inv_one, map_one, MulAut.one_apply]
  have zgi : z g⁻¹ = -(((A⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * z g * (A : Matrix (Fin 3) (Fin 3) R)) := by
    have h := hz g⁻¹ g
    rw [inv_mul_cancel, z1, ad1 _ _ hgi, GG.mat, hgil, inv_inv] at h
    rw [eq_comm, ← eq_neg_iff_add_eq_zero] at h
    exact h
  have zh : z (c * g⁻¹ * c) = -(Jmat R 3 * (z g⁻¹)ᵀ * Jmat R 3) := by
    rw [hz, hzc, ad0, add_zero, hz, hzc, zero_add, adc]
    rfl
  have Mh : (r (c * g⁻¹ * c)).mat = Jmat R 3 * (A : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 := by
    rw [GG.mat, map_mul, map_mul, SemidirectProduct.mul_left, hleft, map_one, mul_one,
      SemidirectProduct.mul_left, hleft, one_mul, hc2, hgil, map_inv, sgnAct_neg_one, theta_inv_val]
  have hD : z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat =
      z g * (A : Matrix (Fin 3) (Fin 3) R) - Jmat R 3 * (z g * (A : Matrix (Fin 3) (Fin 3) R))ᵀ * Jmat R 3 := by
    rw [zh, Mh, zgi]
    have hJ := Jmat_mul_Jmat (R := R) 3
    have hAA : ((A⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ * (A : Matrix (Fin 3) (Fin 3) R)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    simp only [Matrix.transpose_neg, Matrix.transpose_mul, neg_neg, Matrix.mul_neg, Matrix.neg_mul, GG.mat,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Jmat R 3) (Jmat R 3), hJ, Matrix.one_mul,
      ← Matrix.mul_assoc ((A⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ (A : Matrix (Fin 3) (Fin 3) R)ᵀ,
      hAA, Matrix.one_mul]
  have hDe : ∀ i j, (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) i j =
      (z g * (A : Matrix (Fin 3) (Fin 3) R)) i j - (z g * (A : Matrix (Fin 3) (Fin 3) R)) j.rev i.rev := by
    intro i j
    rw [hD, Matrix.sub_apply, jtj]
  intro i j hij
  rw [hDe] at e1 e2 ⊢
  rw [r0, r1] at e1 e2
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact sub_self _ | exact e1 | exact e2 | exact (show (z g * (A : Matrix (Fin 3) (Fin 3) R)) 1 2 - (z g * (A : Matrix (Fin 3) (Fin 3) R)) 0 1 = 0 by linear_combination -e1) | exact (show (z g * (A : Matrix (Fin 3) (Fin 3) R)) 2 1 - (z g * (A : Matrix (Fin 3) (Fin 3) R)) 1 0 = 0 by linear_combination -e2)

private def zlGrp {l : ℕ} [Fact l.Prime] {κ : Type} [Field κ] (F : Frame l κ) {N : Type} [AddCommGroup N]
    (ρ : Representation ℤ F.Γ N) (Z : ∀ v, AddSubgroup (F.Gv v → N)) : AddSubgroup (F.Γ → N) where
  carrier := ZL F ρ fun v => Z v
  add_mem' := by
    rintro x y ⟨⟨a1, a2⟩, a3⟩ ⟨⟨b1, b2⟩, b3⟩
    refine ⟨⟨a1.add b1, fun s t => ?_⟩, fun v => (Z v).add_mem (a3 v) (b3 v)⟩
    simp only [Pi.add_apply, a2, b2, map_add]; abel
  zero_mem' := ⟨⟨IsLocallyConstant.const 0, by simp⟩, fun v => (Z v).zero_mem⟩
  neg_mem' := by
    rintro x ⟨⟨a1, a2⟩, a3⟩
    refine ⟨⟨a1.neg, fun s t => ?_⟩, fun v => (Z v).neg_mem (a3 v)⟩
    simp only [Pi.neg_apply, a2, map_neg]; abel

private def ent {R Γ : Type} [CommRing R] (c g h : Γ) (P Q : Matrix (Fin 3) (Fin 3) R) :
    (Γ → Matrix (Fin 3) (Fin 3) R) →+ (Fin 8 → R) :=
  AddMonoidHom.mk' (fun z => ![z c 0 0, z c 0 1, z c 1 0, z c 0 2, z c 2 0, z c 1 1,
    (z g * P - z h * Q) 0 1, (z g * P - z h * Q) 1 0]) fun x y => by
      have e : (x + y) g * P - (x + y) h * Q = (x g * P - x h * Q) + (y g * P - y h * Q) := by
        simp only [Pi.add_apply, Matrix.add_mul]; abel
      rw [e]
      ext i
      fin_cases i <;> rfl

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.normCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ k, 0 < k → (∀ v, ∃ Z : AddSubgroup (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)), (Z : Set _) = Zv B k v) → (ZL F (adK B k) (Zv B k)).Finite → (ZL F (adK B k) (Zv B k)).ncard ≤ (ZN B k).ncard * Nat.card (Ok l O k) ^ 8 := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B _ hB _ k _ hZ hfin
  haveI : Finite (Ok l O k) := (okFin l O hl).1 k
  choose Z hZ using hZ
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  have hs : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c := by
    simp [Frame.star, Frame.conj, hc, mul_assoc]
  have h := count (ZL F (adK B k) (Zv B k)) (ZN B k) (zlGrp F (adK B k) Z)
    (congrArg (ZL F (adK B k)) (funext hZ)) hfin (fun z hz => hz.1)
    (ent F.c F.g0 (F.star F.g0) ((boxK B k).r F.g0).mat ((boxK B k).r (F.star F.g0)).mat) (fun z hz h0 => by
      refine ⟨hz, ?_⟩
      have e6 := congrFun h0 6
      have e7 := congrFun h0 7
      rw [hs] at e6 e7 ⊢
      exact core (boxK B k).r F.c F.g0 hF.c_sq (hB.map _).atc (((boxK B k).nu _).trans hF.del_c)
        (((boxK B k).nu _).trans F.g0.2) z hz.1.2
        ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2, congrFun h0 3, congrFun h0 4, congrFun h0 5⟩ e6 e7)
  rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at h
end

section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private theorem ac_const {D R : Type} [TopologicalSpace D] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I fun _ : D => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f g : D → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s + g s := fun N => by
  have h := (hf N).add (hg N)
  convert h using 1
  funext s
  simp

private theorem ac_mul {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f g : D → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := fun N => by
  have h := (hf N).mul (hg N)
  convert h using 1
  funext s
  simp

private theorem ac_comp {D E R : Type} [TopologicalSpace D] [TopologicalSpace E] [CommRing R] {I : Ideal R}
    {f : E → R} (hf : AdicCont I f) {φ : D → E} (hφ : Continuous φ) : AdicCont I fun s => f (φ s) :=
  fun N => (hf N).comp_continuous hφ

private theorem adic_continuous_sum_three {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f : Fin 3 → D → R}
    (hf : ∀ a, AdicCont I (f a)) : AdicCont I fun s => ∑ a, f a s := by
  simp only [Fin.sum_univ_three]
  exact ac_add (ac_add (hf 0) (hf 1)) (hf 2)

variable {l : ℕ} [Fact l.Prime]

private theorem triOf_val {C : Type} [CommRing C] {κ : Type} [Field κ] {F : Frame l κ} (B : Box F 3 C) (v : F.V)
    (s : F.Gv v) : (triOf B v s : Matrix (Fin 3) (Fin 3) C) =
      (B.g v : Matrix (Fin 3) (Fin 3) C) * (B.r (F.loc v s)).mat *
        (((B.g v)⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := rfl

private theorem pow_w_ne {κ : Type} [Field κ] (x : κˣ) (hx : x ^ 2 ≠ 1) (i j : Fin 3) (h : i ≠ j) :
    ((x ^ w 3 i : κˣ) : κ) ≠ ((x ^ w 3 j : κˣ) : κ) := by
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have h1 : x ≠ 1 := fun e => hx (by simp [e])
  have h2 : x ≠ x⁻¹ := fun e => hx (by
    rw [pow_two]
    nth_rewrite 2 [e]
    simp)
  have h3 : x⁻¹ ≠ 1 := fun e => h1 (by simpa using e)
  intro e
  have e' := Units.ext e
  fin_cases i <;> fin_cases j <;> simp_all

private theorem genI_of {D : Type} [Group D] [TopologicalSpace D] {I : Subgroup D} {d : ℕ}
    (h : ∃ u : Fin d → D, (∀ a, u a ∈ I) ∧ ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : D →* A,
      IsOpen (χ.ker : Set D) → (∀ a, χ (u a) = 1) → ∀ g ∈ I, χ g = 1) : GenI l I d := by
  obtain ⟨u, hu, hχ⟩ := h
  refine ⟨u, hu, ?_⟩
  intro k A _ _ hk a hloc hadd hz g hg
  have h1 : a 1 = 0 := by simpa using hadd 1 1
  let χ : D →* Multiplicative A :=
    { toFun := fun s => Multiplicative.ofAdd (a s)
      map_one' := by rw [h1]; rfl
      map_mul' := fun s t => by rw [hadd]; rfl }
  have hp : IsPGroup l (Multiplicative A) := fun x => ⟨k, by
    show Multiplicative.ofAdd (l ^ k • Multiplicative.toAdd x) = 1
    rw [hk]
    rfl⟩
  have ho : IsOpen (χ.ker : Set D) := by
    have : (χ.ker : Set D) = a ⁻¹' {0} := by
      ext s
      show χ s = 1 ↔ a s = 0
      exact Iff.rfl
    rw [this]
    exact hloc.isOpen_fiber 0
  exact hχ (Multiplicative A) hp χ ho (fun j => by
    show Multiplicative.ofAdd (a (u j)) = 1
    rw [hz]
    rfl) g hg

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.triOk :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ v, TriRep (triOf B v) ∧ GenI l (F.Iv v) (F.dv v) ∧ ∀ s j, (triOf B v s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O) := by
  intro l _ O _ _ _ _ _ F C₀ hF _ ρ B hL hB hC v
  have hd : ∀ s j, (triOf B v s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O) := by
    intro s j
    rw [triOf_val]
    have e : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := hB.res (F.loc0 v s)
    rw [e]
    exact hB.psi v j s
  have hloc : Continuous (F.loc v) := continuous_subtype_val.comp (hF.loc_cont v)
  refine ⟨⟨fun i j => ?_, fun s => ?_, ?_⟩, ?_, hd⟩
  · have e : (fun s => (triOf B v s : Matrix (Fin 3) (Fin 3) O) i j) = fun s =>
        ∑ b, (∑ a, (B.g v : Matrix (Fin 3) (Fin 3) O) i a * (B.r (F.loc v s)).mat a b) *
          (((B.g v)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) b j := by
      funext s
      rw [triOf_val, Matrix.mul_apply]
      simp only [Matrix.mul_apply]
    rw [e]
    exact adic_continuous_sum_three fun b => ac_mul (adic_continuous_sum_three fun a => ac_mul (ac_const _ _) (ac_comp (hC a b) hloc)) (ac_const _ _)
  · exact B.tri v s
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij => ?_⟩
    rw [hd, hd]
    by_contra hn
    have hm : (ρ.ψ v i s : O) - (ρ.ψ v j s : O) ∈ maximalIdeal O := hn
    have h0 := (res_eq_zero_iff O O _).2 hm
    rw [map_sub, sub_eq_zero] at h0
    have hi := hL.2.1.2 v i s
    have hj := hL.2.1.2 v j s
    simp only [NRep.map_ψ, RingHom.id_apply] at hi hj
    exact pow_w_ne _ hs i j hij (by rw [← hi, ← hj]; exact h0)
  · obtain ⟨u, a₀, hu, -, hχ⟩ := hF.gen v
    exact genI_of ⟨u, fun a => (hu a).1, hχ⟩
end

section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem lc_of_ker {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N]
    (τ : Representation ℤ D N) (h : IsOpen (τ.ker : Set D)) : IsLocallyConstant fun s => τ s := by
  rw [IsLocallyConstant.iff_exists_open]
  intro s
  refine ⟨(fun y => s⁻¹ * y) ⁻¹' (τ.ker : Set D), h.preimage (continuous_mul_left s⁻¹), ?_, ?_⟩
  · show s⁻¹ * s ∈ τ.ker
    rw [inv_mul_cancel]
    exact one_mem _
  · intro y hy
    have hy' : τ (s⁻¹ * y) = 1 := hy
    calc τ y = τ (s * (s⁻¹ * y)) := by rw [mul_inv_cancel_left]
      _ = τ s * τ (s⁻¹ * y) := map_mul τ _ _
      _ = τ s := by rw [hy', mul_one]

private theorem cnt {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N] [Finite N]
    (σ τ : Representation ℤ D N) (e : N ≃+ N) (he : ∀ s x, σ s (e x) = e (τ s x)) (h : IsOpen (τ.ker : Set D))
    (A : AddSubgroup (D → N)) [Finite A] (hA : (A : Set (D → N)) ⊆ Zc τ) (T : Set N)
    (hT : ∀ Y, (fun s => τ s Y - Y) ∈ A → Y ∈ T) :
    ∃ Z : AddSubgroup (D → N), (Z : Set (D → N)) = {z | ∃ z' ∈ A, ∃ Y, ∀ s, z s = e (z' s) + (σ s Y - Y)} ∧
      (Z : Set (D → N)) ⊆ Zc σ ∧ (∀ Y, (fun s => σ s Y - Y) ∈ Z) ∧
      Nat.card A * Nat.card N ≤ Nat.card Z * Nat.card T := by
  classical
  let ψ : ↥A × N →+ (D → N) :=
    { toFun := fun p => fun s => e ((p.1 : D → N) s) + (σ s p.2 - p.2)
      map_zero' := by
        funext s
        simp
      map_add' := by
        intro p q
        funext s
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, Pi.add_apply, map_add]
        abel }
  have hψ : ∀ p : ↥A × N, ∀ s, ψ p s = e ((p.1 : D → N) s) + (σ s p.2 - p.2) := fun p s => rfl
  have hlc : ∀ Y : N, IsLocallyConstant fun s => σ s Y := by
    intro Y
    have h1 : (fun s => σ s Y) = fun s => e (τ s (e.symm Y)) := by
      funext s
      rw [← he, AddEquiv.apply_symm_apply]
    rw [h1]
    exact (lc_of_ker τ h).comp fun f => e (f (e.symm Y))
  refine ⟨ψ.range, ?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨⟨a, Y⟩, rfl⟩
      exact ⟨a, a.2, Y, fun s => rfl⟩
    · rintro ⟨z', hz', Y, hz⟩
      exact ⟨(⟨z', hz'⟩, Y), funext fun s => (hz s).symm⟩
  · rintro z ⟨⟨a, Y⟩, rfl⟩
    have ha := hA a.2
    refine ⟨?_, ?_⟩
    · have h2 : IsLocallyConstant fun s => e ((a : D → N) s) := ha.1.comp e
      exact h2.add ((hlc Y).sub (IsLocallyConstant.const Y))
    · intro s t
      simp only [hψ]
      rw [ha.2 s t]
      simp only [map_add, map_sub, he, map_mul, Module.End.mul_apply]
      abel
  · intro Y
    exact ⟨(0, Y), funext fun s => by simp [hψ]⟩
  · have hcard : Nat.card (↥A × N) = Nat.card ψ.range * Nat.card ψ.ker := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
    have key : ∀ p : ψ.ker, (fun s => τ s (-e.symm p.1.2) - -e.symm p.1.2) = (p.1.1 : D → N) := by
      rintro ⟨⟨a, Y⟩, hp⟩
      have hp' : ∀ s, e ((a : D → N) s) + (σ s Y - Y) = 0 := fun s => congrFun hp s
      show (fun s => τ s (-e.symm Y) - -e.symm Y) = (a : D → N)
      funext s
      apply e.injective
      simp only [map_sub, map_neg, AddEquiv.apply_symm_apply, ← he]
      rw [eq_neg_of_add_eq_zero_left (hp' s)]
      abel
    let f : ψ.ker → T := fun p => ⟨-e.symm p.1.2, hT _ (by rw [key p]; exact p.1.1.2)⟩
    have hf : Function.Injective f := by
      intro p q hpq
      have h2 : p.1.2 = q.1.2 := by
        have h3 : -e.symm p.1.2 = -e.symm q.1.2 := congrArg Subtype.val hpq
        exact e.symm.injective (neg_injective h3)
      have h1 : (p.1.1 : D → N) = q.1.1 := by
        rw [← key p, ← key q, h2]
      exact Subtype.ext (Prod.ext (Subtype.ext h1) h2)
    have hker : Nat.card ψ.ker ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    calc Nat.card A * Nat.card N = Nat.card (↥A × N) := (Nat.card_prod _ _).symm
      _ = Nat.card ψ.range * Nat.card ψ.ker := hcard
      _ ≤ Nat.card ψ.range * Nat.card T := Nat.mul_le_mul_left _ hker

private theorem card_upT (R : Type) [Zero R] [Finite R] :
    Nat.card {Y : Matrix (Fin 3) (Fin 3) R | UpT Y} ≤ Nat.card R ^ 6 := by
  classical
  have hP : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2} = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hinj : Function.Injective
      (fun Y : {Y : Matrix (Fin 3) (Fin 3) R | UpT Y} =>
        fun p : {p : Fin 3 × Fin 3 // p.1 ≤ p.2} => (Y : Matrix (Fin 3) (Fin 3) R) p.1.1 p.1.2) := by
    rintro ⟨Y, hY⟩ ⟨Y', hY'⟩ e
    apply Subtype.ext
    ext i j
    show Y i j = Y' i j
    by_cases hij : i ≤ j
    · exact congrFun e ⟨(i, j), hij⟩
    · have hji : j < i := lt_of_not_ge hij
      have h1 : UpT Y := hY
      have h2 : UpT Y' := hY'
      rw [h1 i j hji, h2 i j hji]
  calc Nat.card {Y : Matrix (Fin 3) (Fin 3) R | UpT Y}
      ≤ Nat.card ({p : Fin 3 × Fin 3 // p.1 ≤ p.2} → R) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card R ^ 6 := by rw [Nat.card_fun, hP]

private def cjE {R : Type} [CommRing R] (g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R ≃+ Matrix (Fin 3) (Fin 3) R where
  toFun X := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * (g : Matrix (Fin 3) (Fin 3) R)
  invFun X := (g : Matrix (Fin 3) (Fin 3) R) * X * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
  left_inv X := by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left]
  right_inv X := by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]

private theorem ad_cj {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {F : Frame l (ResidueField O)} (B : Box F 3 O) (k : ℕ) (v : F.V) (s : F.Gv v)
    (X : Matrix (Fin 3) (Fin 3) (Ok l O k)) :
    adK B k (F.loc v s) (cjE ((boxK B k).g v) X) = cjE ((boxK B k).g v) (cj k (triOf B v) s X) := by
  have hr : (B.r (F.loc v s)).right = 1 := by
    rw [B.nu]
    exact (F.loc0 v s).2
  have e1 : ∀ A : GL (Fin 3) O, (↑A : Matrix (Fin 3) (Fin 3) O).map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k})) =
      ↑(GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k})) A) := fun A => rfl
  simp only [adK, Box.ad, adRep, GG.ad, boxK, Box.map, GG.map, cjE, cj, triOf, MonoidHom.comp_apply,
    MonoidHom.coe_mk, OneHom.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk, e1]
  show GG.adFun (m := 3) (R := Ok l O k) _ _ = _
  simp only [GG.adFun, GG.mat, SemidirectProduct.map_left, SemidirectProduct.map_right, MonoidHom.id_apply, hr,
    if_true, map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc,
    Units.inv_mul_cancel_left, Units.mul_inv_cancel_left, Units.inv_mul, Units.mul_inv, Matrix.mul_one]

theorem UpperTheory.V.Z.J.zvCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ k, 0 < k → ∀ v, (ZF (l := l) (F.Iv v) k (triOf B v)).Finite → ∃ Z : AddSubgroup (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)), (Z : Set _) = Zv B k v ∧ (Z : Set _) ⊆ Zc ((adK B k).comp (F.loc v)) ∧ (∀ Y, (fun s => adK B k (F.loc v s) Y - Y) ∈ Z) ∧ (ZF (l := l) (F.Iv v) k (triOf B v)).ncard * Nat.card (Ok l O k) ^ 9 ≤ Nat.card Z * Nat.card (Ok l O k) ^ 6 := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B hlift hOf hCont k hk v hfin
  classical
  obtain ⟨hfinOk, -⟩ := okFin l O hl
  haveI : Finite (Ok l O k) := hfinOk k
  have htri := (triOk l O F C₀ hF hl ρ B hlift hOf hCont v).1
  obtain ⟨⟨ρc, hρc, hker⟩, -, -, -, hup⟩ := cjFacts l O (F.Gv v) (triOf B v) k hl htri
  let A : AddSubgroup (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)) :=
    { carrier := ZF (l := l) (F.Iv v) k (triOf B v)
      add_mem' := by
        rintro a b ⟨ha1, ha2, ha3, ha4⟩ ⟨hb1, hb2, hb3, hb4⟩
        refine ⟨ha1.add hb1, ?_, ?_, ?_⟩
        · intro s s'
          simp only [Pi.add_apply]
          rw [ha2, hb2, ← hρc, ← hρc, ← hρc, map_add]
          abel
        · intro s i j hij
          simp only [Pi.add_apply, Matrix.add_apply, ha3 s i j hij, hb3 s i j hij, add_zero]
        · intro s hs i
          simp only [Pi.add_apply, Matrix.add_apply, ha4 s hs i, hb4 s hs i, add_zero]
      zero_mem' := by
        refine ⟨IsLocallyConstant.const 0, ?_, ?_, ?_⟩
        · intro s s'
          simp only [Pi.zero_apply]
          rw [← hρc, map_zero, add_zero]
        · intro s i j hij
          rfl
        · intro s hs i
          rfl
      neg_mem' := by
        rintro a ⟨ha1, ha2, ha3, ha4⟩
        refine ⟨ha1.neg, ?_, ?_, ?_⟩
        · intro s s'
          simp only [Pi.neg_apply]
          rw [ha2, ← hρc, ← hρc, map_neg, neg_add]
        · intro s i j hij
          simp only [Pi.neg_apply, Matrix.neg_apply, ha3 s i j hij, neg_zero]
        · intro s hs i
          simp only [Pi.neg_apply, Matrix.neg_apply, ha4 s hs i, neg_zero] }
  have hA : (A : Set (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k))) ⊆ Zc ρc := by
    rintro z ⟨h1, h2, -, -⟩
    exact ⟨h1, fun s t => by rw [h2, hρc]⟩
  haveI : Finite A := hfin.to_subtype
  have hT : ∀ Y, (fun s => ρc s Y - Y) ∈ A → Y ∈ {Y : Matrix (Fin 3) (Fin 3) (Ok l O k) | UpT Y} := by
    rintro Y ⟨-, -, h3, -⟩
    exact hup Y fun s => by
      have := h3 s
      simpa only [hρc] using this
  have he : ∀ s x, ((adK B k).comp (F.loc v)) s (cjE ((boxK B k).g v) x) =
      cjE ((boxK B k).g v) (ρc s x) := by
    intro s x
    rw [hρc]
    exact ad_cj B k v s x
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := cnt _ ρc (cjE ((boxK B k).g v)) he hker A hA _ hT
  refine ⟨Z, ?_, hZ2, hZ3, ?_⟩
  · rw [hZ1]
    rfl
  · have hN : Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) = Nat.card (Ok l O k) ^ 9 := by
      show Nat.card (Fin 3 → Fin 3 → Ok l O k) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul]
    have hAc : Nat.card A = (ZF (l := l) (F.Iv v) k (triOf B v)).ncard :=
      Nat.card_coe_set_eq (ZF (l := l) (F.Iv v) k (triOf B v))
    have hTc := card_upT (Ok l O k)
    calc (ZF (l := l) (F.Iv v) k (triOf B v)).ncard * Nat.card (Ok l O k) ^ 9
        = Nat.card A * Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) := by rw [hAc, hN]
      _ ≤ Nat.card Z * Nat.card {Y : Matrix (Fin 3) (Fin 3) (Ok l O k) | UpT Y} := hZ4
      _ ≤ Nat.card Z * Nat.card (Ok l O k) ^ 6 := Nat.mul_le_mul_left _ hTc
end

section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem sel_arith {V : Type} [Fintype V] (q C L N : ℕ) (hq : 0 < q) (d z : V → ℕ) (v : V)
    (h1 : ∀ w, q ^ (9 + 3 * d w) ≤ z w) (h2 : q ^ (10 + 3 * d v) ≤ C * z v)
    (h3 : q ^ 9 * ∏ w, z w ≤ L * (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V) (h4 : L ≤ N * q ^ 8) :
    q ^ 2 ≤ C * N := by
  classical
  have hv : v ∈ Finset.univ := Finset.mem_univ v
  obtain ⟨E, hE⟩ : ∃ E, E = ∏ w, q ^ (9 + 3 * d w) := ⟨_, rfl⟩
  have hEeq : E = (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V := by
    rw [hE]
    simp only [pow_add, pow_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Finset.prod_pow_eq_pow_sum]
    ring
  have hEpos : 0 < E := by
    rw [hE]
    exact Finset.prod_pos fun w _ => pow_pos hq _
  have key : q * E ≤ C * ∏ w, z w := by
    rw [hE, ← Finset.mul_prod_erase _ _ hv, ← Finset.mul_prod_erase _ _ hv]
    calc _ = q ^ (10 + 3 * d v) * ∏ w ∈ Finset.univ.erase v, q ^ (9 + 3 * d w) := by ring
      _ ≤ (C * z v) * ∏ w ∈ Finset.univ.erase v, z w :=
          Nat.mul_le_mul h2 (Finset.prod_le_prod' fun w _ => h1 w)
      _ = _ := by ring
  have main : q ^ 2 * (q ^ 8 * E) ≤ (C * N) * (q ^ 8 * E) := by
    calc q ^ 2 * (q ^ 8 * E) = q ^ 9 * (q * E) := by ring
      _ ≤ q ^ 9 * (C * ∏ w, z w) := Nat.mul_le_mul_left _ key
      _ = C * (q ^ 9 * ∏ w, z w) := by ring
      _ ≤ C * (L * (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V) := Nat.mul_le_mul_left _ h3
      _ ≤ C * (N * q ^ 8 * (q ^ 3) ^ (∑ w, d w) * (q ^ 9) ^ Fintype.card V) := by gcongr
      _ = (C * N) * (q ^ 8 * E) := by rw [hEeq]; ring
  exact Nat.le_of_mul_le_mul_right main (Nat.mul_pos (pow_pos hq 8) hEpos)

private theorem sel_cut (q a e z n C : ℕ) (hq : 0 < q) (h : q ^ (a + e) ≤ C * n) (h' : n * q ^ 9 ≤ z * q ^ 6) :
    q ^ (a + 3 + e) ≤ C * z := by
  have b : q ^ 6 * q ^ (a + 3 + e) ≤ q ^ 6 * (C * z) :=
    calc q ^ 6 * q ^ (a + 3 + e) = q ^ (a + e) * q ^ 9 := by ring
      _ ≤ C * n * q ^ 9 := Nat.mul_le_mul_right _ h
      _ = C * (n * q ^ 9) := by ring
      _ ≤ C * (z * q ^ 6) := Nat.mul_le_mul_left _ h'
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left b (pow_pos hq _)

private theorem card_mat (A : Type) : Nat.card (Matrix (Fin 3) (Fin 3) A) = Nat.card A ^ 9 := by
  show Nat.card (Fin 3 → Fin 3 → A) = _
  rw [Nat.card_fun, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  ring

theorem UpperTheory.V.Z.J.selLow :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ cw : F.Inf → F.Γ, (∀ w, cw w * cw w = 1 ∧ F.del (cw w) = -1) → GWL { F with cw := cw } → LocE F → ∀ (v : F.V) (i : Fin 2), UnitStep (F.Iv v) (F.eps.comp (F.loc v)) (triOf B v) i → ∃ C : ℕ, ∀ k, 0 < k → (ZN B k).Finite ∧ Nat.card (Ok l O k) ^ 2 ≤ C * (ZN B k).ncard := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B hρ hB hc cw hcw hG hE v i hU
  have T := triOk l O F C₀ hF hl ρ B hρ hB hc
  obtain ⟨C, hC⟩ := locHigh l O (F.Gv v) (F.Iv v) _ (F.dv v) (triOf B v) hl (hE v) (T v).2.1 (T v).1 i hU
  refine ⟨C, fun k hk => ?_⟩
  have hlow := fun w => locLow l O (F.Gv w) (F.Iv w) _ (F.dv w) (triOf B w) hl (hE w) (T w).2.1 (T w).1 k hk
  choose Z hZ1 hZ2 hZ3 hZ4 using fun w => zvCnt l O F C₀ hF hl ρ B hρ hB hc k hk w (hlow w).1
  obtain ⟨hfin, -, hkill, -⟩ := okFin l O hl
  haveI : Finite (Ok l O k) := hfin k
  have hq : 0 < Nat.card (Ok l O k) := Nat.card_pos
  haveI : Finite (Matrix (Fin 3) (Fin 3) (Ok l O k)) := inferInstanceAs (Finite (Fin 3 → Fin 3 → Ok l O k))
  have hk2 : ∀ x : Matrix (Fin 3) (Fin 3) (Ok l O k), l ^ k • x = 0 := fun x => by
    ext a b
    exact hkill k (x a b)
  have hop : IsOpen ((adK B k).ker : Set F.Γ) := by
    first
      | exact adOpen l O F C₀ hF hl B k hc
      | exact (adOpen l O F C₀ hF hl ρ B hρ hB hc k).1
  have hmain : (ZL F (adK B k) fun w => Z w).Finite ∧
      Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) * ∏ w, Nat.card (Z w) ≤
        (ZL F (adK B k) fun w => Z w).ncard * (HomMu l k F.eps (adK B k)).ncard *
        (∏ w, {x | adK B k (cw w) x = x}.ncard) * Nat.card (Matrix (Fin 3) (Fin 3) (Ok l O k)) ^ Fintype.card F.V :=
    hG k hk (Matrix (Fin 3) (Fin 3) (Ok l O k)) (adK B k) hk2 hop Z hZ2 hZ3
  have hZe : (fun w => (Z w : Set (F.Gv w → Matrix (Fin 3) (Fin 3) (Ok l O k)))) = Zv B k := funext hZ1
  rw [hZe, dualZero l O F C₀ hF hl ρ B hρ hB hc k hk, Set.ncard_singleton, mul_one, card_mat] at hmain
  have harch : (∏ w, {x | adK B k (cw w) x = x}.ncard) ≤ (Nat.card (Ok l O k) ^ 3) ^ (∑ w, F.dv w) := by
    have e : ∑ w, F.dv w = Fintype.card F.Inf := hF.card_inf.symm
    rw [e, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod' fun w _ => ?_
    exact archUp l O hl hF.l_odd (B.r (cw w)) (by rw [← map_mul, (hcw w).1, map_one])
      ((B.nu _).trans (hcw w).2) k hk
  refine ⟨hmain.1.subset fun z hz => hz.1, ?_⟩
  refine sel_arith _ C _ _ hq F.dv (fun w => Nat.card (Z w)) v (fun w => ?_) ?_ ?_
    (normCnt l O F C₀ hF hl ρ B hρ hB hc k hk (fun w => ⟨Z w, hZ1 w⟩) hmain.1)
  · have := sel_cut _ 6 (3 * F.dv w) _ _ 1 hq ((hlow w).2.trans (one_mul _).ge) (hZ4 w)
    rwa [one_mul] at this
  · exact sel_cut _ 7 (3 * F.dv v) _ _ C hq (hC k hk) (hZ4 v)
  · exact hmain.2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ harch))
end
