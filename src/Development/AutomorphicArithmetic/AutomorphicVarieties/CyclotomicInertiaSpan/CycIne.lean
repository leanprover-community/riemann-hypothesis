import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.OnePrimeOfTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ClassIff

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.B1

private theorem exists_primitiveRoot_algClosure_numberField (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (M : ℕ) [NeZero M] : ∃ ζ : Ω, IsPrimitiveRoot ζ M := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω M

private theorem cycN_apply_primitiveRoot_eq_pow (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (N : ℕ) [NeZero N] (g : G F Ω) {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) :
    g ζ = ζ ^ ((cycN F Ω N g : (ZMod N)ˣ) : ZMod N).val := by
  have hu := (hζ.isUnit_unit NeZero.out).mem_rootsOfUnity
  have := modularCyclotomicCharacter.spec Ω (natCard_roots F Ω N)
    (MulSemiringAction.toRingAut (G F Ω) Ω g) hu
  simpa [cycN] using this

private theorem zmod_eq_intCast_of_primitiveRoot_pow_eq {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) (k : ℤ) (h : ζ ^ a.val = ζ ^ k) :
    a = (k : ZMod N) := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  have h1 : ζ ^ ((a.val : ℤ) - k) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, h, div_self (zpow_ne_zero _ h0)]
  have h2 := (hζ.zpow_eq_one_iff_dvd _).mp h1
  have h3 : (((a.val : ℤ) - k : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  push_cast at h3
  rw [ZMod.natCast_zmod_val] at h3
  exact sub_eq_zero.mp h3

theorem UpperTheory.V.B1.cycCompat :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N], IsOpen ((cycN F Ω N).ker : Set (G F Ω)) ∧
    (∀ (M : ℕ) [NeZero M] (h : M ∣ N) (g : G F Ω), ZMod.unitsMap h (cycN F Ω N g) = cycN F Ω M g) ∧
    ∀ c : G F Ω, IsConjOm c.toRingEquiv → cycN F Ω N c = -1 := by
  intro F Ω _ _ _ _ _ N _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_algClosure_numberField F Ω N
  refine ⟨?_, ?_, ?_⟩
  · haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin F {ζ}).fixingSubgroup) ?_
      (IntermediateField.fixingSubgroup_isOpen _)
    intro g hg
    have hgz : g ζ = ζ := by
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ
        (IntermediateField.mem_adjoin_simple_self F ζ)
      simpa [AlgEquiv.smul_def] using this
    rw [MonoidHom.mem_ker]
    apply Units.ext
    have := zmod_eq_intCast_of_primitiveRoot_pow_eq hζ _ 1 (by rw [← cycN_apply_primitiveRoot_eq_pow F Ω N g hζ, hgz, zpow_one])
    simpa using this
  · intro M _ h g
    obtain ⟨d, hd⟩ := id h
    have hη := hζ.pow (NeZero.pos N) (show N = d * M by rw [hd, mul_comm])
    have e1 : g (ζ ^ d) = (ζ ^ d) ^ ((cycN F Ω N g : (ZMod N)ˣ) : ZMod N).val := by
      rw [map_pow, cycN_apply_primitiveRoot_eq_pow F Ω N g hζ, ← pow_mul, ← pow_mul, mul_comm]
    have e2 := cycN_apply_primitiveRoot_eq_pow F Ω M g hη
    have key := zmod_eq_intCast_of_primitiveRoot_pow_eq hη _ (((cycN F Ω N g : (ZMod N)ˣ) : ZMod N).val : ℤ)
      (by rw [← e2, e1, zpow_natCast])
    apply Units.ext
    rw [key, Int.cast_natCast, ← ZMod.cast_eq_val, ZMod.unitsMap_def]
    rfl
  · intro c hc
    obtain ⟨j, hj⟩ := hc
    apply Units.ext
    have hN : ζ ^ N = 1 := hζ.pow_eq_one
    have hcz : c ζ = ζ⁻¹ := by
      apply j.injective
      have := hj ζ
      simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv] at this
      rw [this, map_inv₀]
      have hn : ‖j ζ‖ = 1 :=
        Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hN, map_one]) (NeZero.ne N)
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
      simp
    have := zmod_eq_intCast_of_primitiveRoot_pow_eq hζ _ (-1) (by rw [← cycN_apply_primitiveRoot_eq_pow F Ω N c hζ, hcz, zpow_neg_one])
    simpa using this
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.B1

private theorem cycIne_red_surj (l : ℕ) [Fact l.Prime] (n : ℕ) (b : (ZMod (l ^ n))ˣ) :
    ∃ u : ℤ_[l]ˣ, KStar.TotallyRealRoots.redPow l n u = b := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, Units.ext ?_⟩
    have : Subsingleton (ZMod (l ^ 0)) := by
      rw [pow_zero]
      infer_instance
    exact Subsingleton.elim _ _
  · haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
    set k := (b : ZMod (l ^ n)).val with hkdef
    have hcop : Nat.Coprime k (l ^ n) := ZMod.val_coe_unit_coprime b
    have hk : ¬ (l : ℤ) ∣ (k : ℤ) := by
      rw [Int.natCast_dvd_natCast]
      intro hd
      have hc : Nat.Coprime l k :=
        Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right (dvd_pow_self l hn.ne') hcop)
      have hg := Nat.dvd_gcd (dvd_refl l) hd
      rw [Nat.Coprime.gcd_eq_one hc] at hg
      exact hl.ne_one (Nat.eq_one_of_dvd_one hg)
    have hu : IsUnit ((k : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      exact le_antisymm (PadicInt.norm_le_one _)
        (not_lt.mp fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd _).mp h))
    refine ⟨hu.unit, Units.ext ?_⟩
    simp only [KStar.TotallyRealRoots.redPow, Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, map_intCast,
      Int.cast_natCast]
    rw [hkdef]
    exact (map_natCast (PadicInt.toZModPow n) _).trans (ZMod.natCast_zmod_val _)

theorem UpperTheory.V.B1.cycIne :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (B : ValuationSubring Ω), B.valuation (p : Ω) < 1 →
    (Ine (F := ℚ) B).map (cycN ℚ Ω N) = B3.pPart N p := by
  intro Ω _ _ _ N _ p _ B hB
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : p.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  set M := N / p ^ N.factorization p with hM
  haveI : NeZero M := ⟨(Nat.ordCompl_pos p hN0).ne'⟩
  have hMcop : M.Coprime p := (Nat.coprime_ordCompl hp hN0).symm
  have hone : ∀ ζ : Ω, ζ ^ M = 1 → ζ = ζ ^ (1 % M) := by
    intro ζ hζ
    rcases Nat.lt_or_ge 1 M with h | h
    · rw [Nat.mod_eq_of_lt h, pow_one]
    · have hM1 : M = 1 := le_antisymm h (Nat.pos_of_ne_zero (NeZero.ne M))
      rw [hM1, Nat.mod_self, pow_zero]
      rw [hM1, pow_one] at hζ
      exact hζ
  have hfixM : ∀ g ∈ Ine (F := ℚ) B, ∀ ζ : Ω, ζ ^ M = 1 → g ζ = ζ := fun g hg ζ hζ =>
    (UpperTheory.V.LDataCardLeFinrank.ineFixRoots ℚ Ω p B hB M hMcop ζ hζ).2 g hg
  have hcycM : ∀ g ∈ Ine (F := ℚ) B, cycN ℚ Ω M g = 1 := by
    intro g hg
    rw [cycN_eq_iff]
    intro ζ hζ
    rw [hfixM g hg ζ hζ, Units.val_one, ZMod.val_one_eq_one_mod]
    exact hone ζ hζ
  apply le_antisymm
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
    show cycN ℚ Ω N g ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker
    rw [MonoidHom.mem_ker, (cycCompat ℚ Ω N).2.1 M (Nat.ordCompl_dvd N p) g]
    exact hcycM g hg
  · intro h hh
    have hh' : ZMod.unitsMap (Nat.ordCompl_dvd N p) h = 1 := hh
    obtain ⟨u, hu⟩ := cycIne_red_surj p (N.factorization p) (ZMod.unitsMap (Nat.ordProj_dvd N p) h)
    obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω p B hB u
    refine Subgroup.mem_map.mpr ⟨σ, hσ, ?_⟩
    rw [cycN_eq_iff]
    refine (UpperTheory.V.LDataCardLeFinrank.classIff Ω p N (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) h).mpr ⟨?_, ?_⟩
    · intro ζ hζ
      rw [hh', Units.val_one, ZMod.val_one_eq_one_mod]
      show σ ζ = _
      rw [hfixM σ hσ ζ hζ]
      exact hone ζ hζ
    · rw [← hu, ← hσu]
      rfl
end
