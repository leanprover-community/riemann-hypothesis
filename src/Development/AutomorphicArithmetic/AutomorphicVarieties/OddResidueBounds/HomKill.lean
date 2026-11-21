import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Normkill
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LiftEx

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem jv_eq (M a : ℕ) [NeZero M] (ha : a.Coprime M) (b : ZMod M) :
    (M : ℤ) * jv M a b = (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
  unfold jv
  have hdiv : (M : ℤ) ∣ (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    unfold yCl
    rw [← mul_assoc, ZMod.coe_mul_inv_eq_one a ha, one_mul, sub_self]
  exact Int.mul_ediv_cancel' hdiv

theorem UpperTheory.V.Odd.clKill :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (a : ℕ), Odd a → a.Coprime M → ∀ c : Additive (ClassGroup (𝓞 K)), ∑ b : (ZMod M)ˣ, Eone M a b • Stick.clRep K (Stick.sg M K b)⁻¹ c = 0 := by
  intro M _ K _ _ _ a ha hcop c
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  have hterm : ∀ b : (ZMod M)ˣ, Eone M a b • Stick.clRep K (Stick.sg M K b)⁻¹ c =
      Additive.ofMul ((clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c)) ^ (Eone M a b)) := by
    intro b
    rfl
  rw [Finset.sum_congr rfl (fun b _ => hterm b), ← ofMul_prod]
  show Additive.ofMul _ = Additive.ofMul 1
  congr 1
  have hnorm : ∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) = 1 := by
    rw [← Stk.prod_galois_classGroup_map_eq_one K (Additive.toMul c)]
    exact Fintype.prod_equiv ((Stick.sg M K).toEquiv.trans (Equiv.inv _)) _ _ (fun b => rfl)
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime a hcop
  let β : (ZMod M)ˣ → ℤ := fun s => (if s = u⁻¹ then (a : ℤ) else 0) - (if s = 1 then 1 else 0)
  have hβ : ∀ t : (ZMod M)ˣ, (M : ℤ) * jv M a (t : ZMod M) =
      ∑ s, β s * (((s : ZMod M) * (t : ZMod M)).val : ℤ) := by
    intro t
    rw [jv_eq M a hcop t]
    have hy : yCl a (t : ZMod M) = ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * t := by
      unfold yCl
      rw [← ZMod.inv_coe_unit]
      rfl
    simp only [β, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, one_mul, Units.val_one]
    rw [hy]
  have hj := (Stick.coef M K (Additive.toMul c)).2 β (fun t => jv M a (t : ZMod M)) hβ
  calc ∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ Eone M a b
      = ∏ b : (ZMod M)ˣ, (clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ (((a : ℤ) - 1) / 2) *
          (clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ jv M a (b : ZMod M))⁻¹) := by
        refine Finset.prod_congr rfl (fun b _ => ?_)
        unfold Eone
        rw [zpow_sub]
    _ = (∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c)) ^ (((a : ℤ) - 1) / 2) *
          (∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ jv M a (b : ZMod M))⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_zpow]
    _ = 1 := by
        rw [hnorm, hj, one_zpow, inv_one, one_mul]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem cyc_hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] [CharZero Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have e : f.toRatAlgHom = g.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact h _ hζ.pow_eq_one
  exact RingHom.ext fun x => DFunLike.congr_fun e x

theorem UpperTheory.V.Odd.fixField :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∃ (K : IntermediateField E Ω) (_ : NumberField K) (_ : IsCyclotomicExtension {N} ℚ K), galOf E K Ω = fixMu E Ω N ∧ ∀ (b : (ZMod N)ˣ) (σ : Ω ≃+* Ω), CycLift N b σ → IsLift (Stick.sg N K b).toRingEquiv σ := by
  intro E Ω _ _ _ _ _ N _ ρ hρ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq fun q => by simp
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : IsGalois ℚ Ω := {}
  haveI : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {ζ}
  have hζL : ζ ∈ L := IntermediateField.mem_adjoin_simple_self ℚ ζ
  have hE : ∀ e : E, algebraMap E Ω e ∈ L := fun e => by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 : σ ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ ζ hζL
    have hc : CycLift N 1 σ.toRingEquiv := fun x hx => by
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hx
      have h2 : σ x = x := by rw [← hi, map_pow, h1]
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]
      exact h2
    have := hρ 1 _ hc e
    rw [map_one] at this
    exact this
  let K : IntermediateField E Ω := L.toSubfield.toIntermediateField hE
  haveI hL : IsCyclotomicExtension {N} ℚ L := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective
  let φ : L ≃+* K := RingEquiv.refl L
  have hK : @IsCyclotomicExtension {N} ℚ K _ _ DivisionRing.toRatAlgebra :=
    @IsCyclotomicExtension.equiv {N} ℚ L _ _ _ K _ DivisionRing.toRatAlgebra hL
      (@AlgEquiv.ofRingEquiv ℚ L K _ _ _ _ DivisionRing.toRatAlgebra φ fun q => by simp)
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI : NumberField K := IsCyclotomicExtension.numberField {N} ℚ K
  have hmu : ∀ x : Ω, x ^ N = 1 → x ∈ K := fun x hx => by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact (pow_mem hζL i : ζ ^ i ∈ L)
  have hpow : ∀ x : K, x ^ N = 1 → algebraMap K Ω x ^ N = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  refine ⟨K, inferInstance, hK, ?_, fun b σ hσ x => ?_⟩
  · ext g
    refine ⟨fun h x hx => h ⟨x, hmu x hx⟩, fun h x => ?_⟩
    exact DFunLike.congr_fun (cyc_hom_ext N (g.toRingEquiv.toRingHom.comp (algebraMap K Ω)) (algebraMap K Ω)
      fun y hy => h _ (hpow y hy)) x
  · refine DFunLike.congr_fun (cyc_hom_ext N (σ.toRingHom.comp (algebraMap K Ω))
      ((algebraMap K Ω).comp (Stick.sg N K b).toRingEquiv.toRingHom) fun y hy => ?_) x
    change σ (algebraMap K Ω y) = algebraMap K Ω (Stick.sg N K b y)
    rw [hσ _ (hpow y hy), Stick.sg_apply N K b hy, map_pow]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.homKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → 2 < N → ∀ a : ℕ, Odd a → a.Coprime N → ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (N' : ℕ), ∀ φ ∈ XDual N' (fixMu E Ω N) R X, ∀ σ : (ZMod N)ˣ → Ω ≃+* Ω, (∀ b, CycLift N b (σ b)) → ∀ (u : fixMu E Ω N) (w : (ZMod N)ˣ → fixMu E Ω N), (∀ b y, u.1 (σ b y) = σ b ((w b).1 y)) → ∑ b : (ZMod N)ˣ, Eone N a b • φ (w b) = 0 := by
  intro E Ω _ _ _ _ _ N _ ρ hρ hN2 a ha hcop R X _ _ _ N' φ hφ σ hσ u w huw
  obtain ⟨K, hKnf, hKcyc, hKgal, hKlift⟩ := fixField E Ω N ρ hρ
  have hU : fixMu E Ω N ≤ galOf E K Ω := le_of_eq hKgal.symm
  have hφ1 : φ ∈ XDual 1 (fixMu E Ω N) R X := by
    obtain ⟨h1, h2, h3, -⟩ := hφ
    refine ⟨h1, h2, h3, ?_⟩
    intro A hA
    simp at hA
  have hTC : IsTotallyComplex K := IsCyclotomicExtension.Rat.isTotallyComplex K hN2
  rw [← pullOnto E Ω K (fixMu E Ω N) hU 1 R X one_ne_zero (le_of_eq hKgal) (Or.inl hTC)] at hφ1
  obtain ⟨ψ, hψ, rfl⟩ := hφ1
  have hart : ∀ b, Additive.ofMul (artU K hU (w b)) =
      Stick.clRep K ((Stick.sg N K) b)⁻¹ (Additive.ofMul (artU K hU u)) := by
    intro b
    have hl := hKlift b (σ b) (hσ b)
    have hg : toGal K hU (w b) = conjGal hl (toGal K hU u) := by
      ext x
      rw [conjGal_apply]
      show (w b).1 x = (σ b).symm (u.1 (σ b x))
      rw [huw b x, RingEquiv.symm_apply_apply]
    have hc := artConj K Ω _ (σ b) hl (toGal K hU u)
    rw [← hg] at hc
    show _ = Stick.clRep K ((Stick.sg N K) b)⁻¹ (Additive.ofMul (artCl K Ω (toGal K hU u)))
    rw [hc]
    show _ = Stick.clRep K ((Stick.sg N K) b)⁻¹ (Stick.clRep K ((Stick.sg N K) b) (Additive.ofMul (artCl K Ω (toGal K hU (w b)))))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rfl
  let ψ' : Additive (ClassGroup (𝓞 K)) →+ X :=
    AddMonoidHom.mk' (fun c => ψ (Additive.toMul c)) (fun c d => hψ.1 _ _)
  have hsum := clKill N K a ha hcop (Additive.ofMul (artU K hU u))
  have key : ∀ b, (clPull K hU R X ψ) (w b) = ψ' (Stick.clRep K ((Stick.sg N K) b)⁻¹ (Additive.ofMul (artU K hU u))) := by
    intro b
    rw [← hart b]
    rfl
  calc _ = ∑ b : (ZMod N)ˣ, Eone N a ↑b • ψ' (Stick.clRep K ((Stick.sg N K) b)⁻¹ (Additive.ofMul (artU K hU u))) :=
        Finset.sum_congr rfl (fun b _ => by rw [key b])
    _ = 0 := by
      simp_rw [← map_zsmul ψ']
      rw [← map_sum, hsum, map_zero]
end
