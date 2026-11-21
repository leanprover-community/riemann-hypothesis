import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.OneCharU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigEnd3
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumberU3US
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyUnramifiedCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.PtHypU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.TypeIIOfBlochKatoLocalPoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.UsedOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleTypeIIBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdmissibleRankTwoSelf

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private cls_eq_one block_form conj_mat eigvec exists_two from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
theorem UpperTheory.GalN.V.adm2B_rhoK_of_typeII_of_modular_extensions :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ (ι : Qbar l ≃+* ℂ),
      TypeII D.η r → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) →
      _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e (N * (discr K).natAbs) (D.rhoK r h.mult) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII hmod
  obtain ⟨h11, -, W, hext, hcont, hirr, -, hdet⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hfin : ∀ g, ψQ g ^ Nat.card (ZMod N)ˣ = 1 := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
  have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
  have hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1 := fun g hg => by
    constructor
    · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1
      rw [cls_eq_one N g fun ζ hζ => hg ζ (by rw [pow_mul, hζ, one_pow]), map_one, map_one]
    · rw [← MonoidHom.mem_ker, D.η_ker]
      exact UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])
  have hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] := fun g hg =>
    block_form _ _ (hII.1 g hg) (h11 g hg) (hext.1 g hg)
  refine ⟨W, hirr, hmod W hext, ⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, ?_, 1, fun s => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : ¬ A.valuation (l : Ω) < 1 := fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')
    obtain ⟨M, hMM⟩ := pt_inertia_away D hM h A hAl
    have h1 := UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by
      have hc : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hAl hg.1
      have hc' : cycBar ℚ Ω l g = 1 := by
        rw [cycBar, MonoidHom.comp_apply, hc, map_one]
      rw [← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]
      congr 2
      funext i
      fin_cases i <;> simp [wt1]
    obtain ⟨χ, hχ, hd⟩ := UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1
    exact ⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : A.valuation (l : Ω) < 1 := ((places ℚ Ω l A).2.2.1 w hA).2 hw
    obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A hAl
    obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A hAl
    obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A hl.out hAl
    have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
      have := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
      rw [map_sub, map_pow, map_one, sub_ne_zero] at this
      exact this
    set v : Fin 3 → Qbar l := (M⁻¹ : GL (Fin 3) (Qbar l)).val *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have := congrArg (fun x => (M.val *ᵥ x) 0) (hv.symm.trans h0)
      simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      simp at this
    have hev : ∀ s ∈ Ine (F := ℚ) A,
        !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by
      have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
      rw [← hblk s (hIk hs)]
      refine eigvec M _ _ ?_ fun i j hij => ?_
      · rw [← conj_mat M r s hr, hdiag s hs 0]
        simp [GG.mat, tor_val, wt1]
      · rw [← conj_mat M r s hr]
        exact hup s (hID hs) (hIk hs) i j hij
    have hv1 : v 1 = 0 := by
      have := congrFun (hev s₀ hs₀) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      by_contra hne
      have h3 : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans this)).symm
      exact hs₀' (by rw [h3, one_pow])
    obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2]
      (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
      (fun h0 => hv0 (by
        funext i
        fin_cases i
        · exact congrFun h0 0
        · exact hv1
        · exact congrFun h0 1))
      (fun s hs => by
        have a0 := congrFun (hev s hs) 0
        have a2 := congrFun (hev s hs) 2
        funext i
        fin_cases i
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
      (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
      ⟨s₀, hs₀, hs₀'⟩
    have hκ' : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
        κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) * (![ψQ, ψQ⁻¹] i) s := fun i s hs => by
      fin_cases i
      · exact (hκ s hs).1.trans (hΨ s)
      · refine (hκ s hs).2.trans ?_
        rw [hΨ, mul_inv, ← _root_.zpow_neg]
        rfl
    refine ⟨A, hA, ![ψQ, ψQ⁻¹], κ, fun i s hs => ?_, hflag, hκ', Or.inl fun i j hij => ?_⟩
    · fin_cases i <;> simp [(hkill s hs).1]
    · obtain ⟨s, hs, hn⟩ := exists_two D.gd.l_odd A hAl
      have h1 := DFunLike.congr_fun hij ⟨s, hID hs⟩
      rw [MonoidHom.mul_apply, hκ' i _ hs, hκ' j _ hs] at h1
      have hf : ∀ i, ((![ψQ, ψQ⁻¹] i) s) ^ Nat.card (ZMod N)ˣ = 1 := fun i => by
        fin_cases i
        · exact hfin s
        · show (ψQ s)⁻¹ ^ _ = 1
          rw [inv_pow, hfin, inv_one]
      have h2 := congrArg (· ^ Nat.card (ZMod N)ˣ) h1
      simp only [mul_pow, hf, mul_one] at h2
      change (cycBar ℚ Ω l s ^ _) ^ _ = (cycBar ℚ Ω l s ^ _) ^ _ * cycBar ℚ Ω l s ^ _ at h2
      rw [← mul_pow, ← _root_.zpow_add_one, ← mul_inv_eq_one, ← inv_pow, ← mul_pow, ← _root_.zpow_sub, ← _root_.zpow_natCast,
        ← _root_.zpow_mul] at h2
      have h3 := (mul_eq_zero.1 (hn _ h2)).resolve_right (by exact_mod_cast Nat.card_pos.ne')
      fin_cases i <;> fin_cases j <;> simp at h3 <;> omega
  · refine ⟨N * (discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W,
      Nat.mul_pos (NeZero.pos N) hodd.pos, fun s hs => Units.ext ?_, by simp⟩
    have := hdet s
    rw [(hkill s hs).2] at this
    simpa using this
  · rw [one_mul, inv_one, mul_one, D.rhoK_apply]
    exact hblk _ (D.η_ker ▸ galEmb_mem ℚ K Ω s)
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.KillsComp
end GlobalTheory.KillsComp
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.Ord2.IrrTransfer
end GlobalTheory.Ord2.IrrTransfer
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.Ord2
open UpperTheory.V.Base UpperTheory.V.U3 in
theorem admissible_typeII_block_alt : U3.CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : U3.Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* U3.GG 3 (PadicAlgCl l)} (_ : D.IsPt U g₁ r) (ι : Qbar l ≃+* ℂ), U3.TypeII D.η r → ∀ W : R2 Ω l, D.IsExt r W → Continuous W → (∀ g, (mat W g).det = ((D.η g : ℤˣ) : ℤ)) → D.IsModularDense ι W → admitted ι e W := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII W hext hcont hdet hmod
  have hdt : ∀ g, (dt W g : Qbar l) = ((D.η g : ℤˣ) : ℤ) := fun g => hdet g
  obtain ⟨A, hA, -, hIA, -, -, -, -⟩ := dat_loc D
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  obtain ⟨hIk, -⟩ := hl1 A hA
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  let χ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω (HV.comp l ψ))
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hχ2 : ∀ g, χ g * χ g = 1 := fun g => by
    have h1 : Chr.dirG ℚ Ω (HV.comp l ψ) g * Chr.dirG ℚ Ω (HV.comp l ψ) g = 1 := by
      apply Units.ext
      show (HV.comp l ψ) (Chr.cls ℚ Ω N g) * (HV.comp l ψ) (Chr.cls ℚ Ω N g) = 1
      rw [← MulChar.mul_apply, ← sq, D.gd.ine, MulChar.one_apply (Units.isUnit _)]
    show Units.map _ _ * Units.map _ _ = 1
    rw [← map_mul, h1, map_one]
  have hψχ : ∀ s ∈ Ine (F := ℚ) A, ψQ s = χ s := fun s hs => by
    rw [← hIA] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    show Units.map _ _ = Units.map _ _
    rw [psi_ine D g hg]
  obtain ⟨κ, hflag, hκ⟩ := flag_block hC D hM h hII W hext hdet A hA
  refine ⟨hcont, ?_, fun s hs => Units.ext ?_, GlobalTheory.Ord2.irr_transfer D.η D.η_ker W hdet (typeII_irr_cyc hC D hM h hII W hext),
    levelAway_block hC D hM h hII W hext hdet, ?_, A, χ, κ, ?_, fun s hs => ?_, hflag, fun s hs => ?_, fun s hs => ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [MonoidHom.one_apply, Units.val_one, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hdt]
    rcases Int.units_eq_one_or (D.η g) with h1 | h1 <;> simp [h1]
  · rw [hdt, conj_eta D s hs]
    simp
  · obtain ⟨f, hf⟩ := _root_.UpperTheory.GalN.V.mod0'_alt hmod
    refine ⟨f, 1, 1, le_rfl, fun _ _ => rfl, ?_⟩
    rw [mul_one]
    exact hf
  · obtain ⟨h1, h2, h3, -⟩ := places ℚ Ω l A
    have hne : A ≠ ⊤ := fun ht => (h2 ht).2 hA
    obtain ⟨v, hv⟩ := h1 hne
    exact ⟨v, hv, (h3 v hv).1 hA⟩
  · show Units.map _ _ = 1
    rw [GlobalTheory.killsMu_comp_of_sq_eq_one ψ D.gd.l_odd D.gd.ine s hs, map_one]
  · rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [hdt, hIk hs]
    simp
  · rw [(hκ s hs).1, (hκ s hs).2, hΨ, hψχ s hs, mul_inv, ← zpow_neg]
    refine ⟨rfl, ?_⟩
    congr 1
    exact inv_eq_of_mul_eq_one_right (hχ2 s)
end GlobalTheory.Ord2
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.Ord2.TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
end GlobalTheory.Ord2.TwDet
namespace GlobalTheory.Ord2.TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
end GlobalTheory.Ord2.TwDet
namespace GlobalTheory.Ord2.TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
end GlobalTheory.Ord2.TwDet
namespace GlobalTheory.Ord2
open TwDet
end GlobalTheory.Ord2
end
end
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
private theorem cls_eq_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (g : G ℚ Ω)
    (hg : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) : Chr.cls ℚ Ω N g = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h1 := Chr.cls_spec N g ζ hζ.pow_eq_one
  rw [hg ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ (1 : ZMod N).val = ζ := by
    rw [ZMod.val_one_eq_one_mod, hζ.eq_orderOf, pow_mod_orderOf, pow_one]
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h1.symm.trans h2.symm)
theorem UpperTheory.V.Z.Kato.used_of_alt :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc}
      {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (_ : D.IsPt U g₁ r),
      TypeII D.η r → ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → Continuous W →
      (∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) = Wfun r g) →
      (∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).det = ((D.η g : ℤˣ) : ℤ)) →
      ∀ ι : Qbar l ≃+* ℂ, D.IsModularDense ι W →
      UpperTheory.V.Z.Kato.Used l Ω K e N ((Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η)
        ((Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)) W := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h hII W hext hcont hW hdet ι hmod
  obtain ⟨h11, -, -⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, hηc, hΨc, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  obtain ⟨A₀, hA₀, -, hIn, -, -, hcyc, hconj⟩ := dat_loc D
  set θ : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η with hθdef
  set ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ) with hψdef
  have hθ0 : ∀ g, (θ g : PadicAlgCl l) = ((D.η g : ℤˣ) : ℤ) := fun g => rfl
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hord := typeII_ord hC D hM h hII W hext hcont hdet
  have w0 : wt1 0 = 1 := by decide
  have w1 : wt1 1 = 0 := by decide
  have w2 : wt1 2 = -1 := by decide
  have h00 : ∀ g, (r0 D.η D.ΨQ g).mat 0 0 = (D.ΨQ g : PadicAlgCl l) := fun g => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq, w0, _root_.zpow_one]
  have h22 : ∀ g, (r0 D.η D.ΨQ g).mat 2 2 = (((D.ΨQ g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) := fun g => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq, w2, _root_.zpow_neg, _root_.zpow_one]
  have h11' : ∀ g, (r0 D.η D.ΨQ g).mat 1 1 = 1 := fun g => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq, w1, _root_.zpow_zero, Units.val_one]
  have htrW : ∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).trace = (θ g : PadicAlgCl l) * (r g).mat 0 0 + (r g).mat 2 2 := by
    intro g
    rw [hW, Wfun, hθ0, h.mult g]
    rcases Int.units_eq_one_or (D.η g) with hg | hg
    · rw [hg, if_pos rfl, Matrix.trace_fin_two]
      show (r g).mat 0 0 + (r g).mat 2 2 = _
      simp
    · rw [hg, if_neg (by decide), Matrix.trace_fin_two, Matrix.mul_diagonal, Matrix.mul_diagonal]
      show (r g).mat 0 0 * (-1) + (r g).mat 2 2 * 1 = _
      simp
  refine
    { l_odd := D.gd.l_odd, e_pos := D.gd.e_pos, gen := D.gd.gen, quad := D.gd.quad, imag := D.gd.imag, l_cop := D.gd.l_cop,
      N_pos := NeZero.pos N, N_even := D.gd.N_even, cop := D.gd.cop, θ_ker := ?_, θ_sq := fun g => ?_, ψ_mu := fun s hs => ?_,
      ψ_ord := ⟨orderOf ψ, D.gd.ord, fun g => ?_⟩, ψ_ine := fun A hA s hs => ?_, even := ⟨D.cc, D.conj, ?_⟩,
      level := hord.1, ord := ⟨A₀, N, hA₀, NeZero.pos N, hord.2 A₀ hA₀⟩, det := fun g => by rw [hdet, hθ0],
      tr_ine := fun A hA s hs => ?_, red := fun g => ?_, flag := ?_, irr := typeII_irr_cyc hC D hM h hII W hext }
  · rw [← D.η_ker]
    ext g
    simp only [MonoidHom.mem_ker, Units.ext_iff, hθ0, Units.val_one]
    rcases Int.units_eq_one_or (D.η g) with hg | hg <;> rw [hg] <;> norm_num
  · show Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom (D.η g) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N s)) = 1
    rw [cls_eq_one N s hs, map_one, map_one]
  · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow]
    have : ψ.toUnitHom (Chr.cls ℚ Ω N g) ^ orderOf ψ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe,
        Units.val_one]
    rw [this, map_one]
  · obtain ⟨x, -, hxI⟩ := hconj A hA
    have h1 := (hxI s).1 hs
    rw [← hIn] at h1
    obtain ⟨σ, hσI, hσ⟩ := h1
    have h2 := D.Ψ_I σ hσI
    have h3 : Loc.cycA l l c.O σ = chiO ℚ Ω l c.O (D.ι σ) := by
      show Units.map _ (Loc.cyc l l σ) = Units.map _ (cycZ ℚ Ω l (D.ι σ))
      rw [hcyc]
      rfl
    have h4 : Chr.dirG ℚ Ω ψ (D.ι σ) = Chr.dirG ℚ Ω (comp l ψ) (D.ι σ) := by
      rw [h3, Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, _root_.zpow_natCast] at h2
      exact mul_left_cancel h2
    have h5 : Chr.dirG ℚ Ω ψ s = Chr.dirG ℚ Ω ψ (D.ι σ) := by
      rw [hσ]
      simp only [map_mul, map_inv, inv_mul_cancel_comm]
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Chr.dirG ℚ Ω ψ s) ^ 2 = 1
    have h6 : Chr.dirG ℚ Ω (comp l ψ) (D.ι σ) ^ 2 = 1 := by
      apply Units.ext
      show (((comp l ψ).toUnitHom (Chr.cls ℚ Ω N (D.ι σ)) ^ 2 : c.Oˣ) : c.O) = _
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, D.gd.ine, MulChar.one_apply_coe,
        Units.val_one]
    rw [← map_pow, h5, h4, h6, map_one]
  · rw [← hΨ]
    show Units.map _ (D.Ψ D.cc) = 1
    rw [hΨc, map_one]
  · obtain ⟨hch, -⟩ := pt_inertia_above hC D hM h A hA
    have hk : s ∈ D.η.ker := (hl1 A hA).1 hs
    have htr : (r s).mat.trace = (r0 D.η D.ΨQ s).mat.trace := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hch s hs]
    rw [Matrix.trace_fin_three, Matrix.trace_fin_three, h00, h22, h11', h11 s hk] at htr
    rw [htrW, ← hΨ, hθ0, show D.η s = 1 from hk]
    simp only [Units.val_one, Int.cast_one, one_mul]
    linear_combination htr
  · rw [htrW, ← hΨ]
    have a0 := h.red g 0 0
    have a2 := h.red g 2 2
    rw [h00] at a0
    rw [h22] at a2
    have hn : ‖(θ g : PadicAlgCl l)‖ = 1 := by
      rw [hθ0]
      rcases Int.units_eq_one_or (D.η g) with hg | hg <;> simp [hg]
    have e1 : (θ g : PadicAlgCl l) * (r g).mat 0 0 + (r g).mat 2 2 -
        ((θ g : PadicAlgCl l) * (D.ΨQ g : PadicAlgCl l) + (((D.ΨQ g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) =
        (θ g : PadicAlgCl l) * ((r g).mat 0 0 - D.ΨQ g) + ((r g).mat 2 2 - (((D.ΨQ g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) := by
      ring
    rw [e1]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ a2)
    rw [norm_mul, hn, one_mul]
    exact a0
  · have hdt : GlobalTheory.Ord2.dt W = θ := MonoidHom.ext fun g => Units.ext ((hdet g).trans (hθ0 g).symm)
    rw [← hdt]
    exact (_root_.GlobalTheory.Ord2.admissible_typeII_block_alt hC D hM h ι hII W hext hcont hdet hmod).flag
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private bk_map IsBlockSL2Embedding pA sA pB sB pC decomp ad_sA pA_ad wOf wOf_eq pB_ad ad_sB pC_ad ad_pC pA_ad_one pA_ad_c repA pair_eq isBlock_reducible_three_dim pC_mem cont_pA cont_pB cont_pC from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ReducibleThreeDim
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
open UpperTheory.V.Th.ReducibleThreeDim in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.bloch_kato_selmer_vanishes_of_type_ii_modular_ext :
    U3.CohInp → _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW → _root_.UpperTheory.V.Th.RigiditySecondCase → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁) (f : S.R →ₐ[c.O] PadicAlgCl l), IsLocPt f → ∀ ι : Qbar l ≃+* ℂ, TypeII D.η (push f S.r.hom) → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt (push f S.r.hom) W → D.IsModularDense ι W) → Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
  intro hC hK hRig Ω _ _ _ K _ _ _ _ l _ c N _ e ψ D U g₁ hm S f₀ hf₀ ι hII hmod
  have h := isPt_push D hm S f₀ hf₀
  have hR := hRig D hm S f₀ hf₀ ι hII
  generalize push f₀ S.r.hom = r at h hR hII hmod ⊢
  obtain ⟨hcc, hηc, -, hlc, -, -, -, hCM, -⟩ := dat_facts D
  obtain ⟨h11, hdet, W, hext, hWc, -, hW, hWd⟩ := typeII_facts hC D hm h hII
  have hW' : ∀ g, (W g).val = wOf (r g) := hW
  have hblk0 : ∀ g ∈ D.η.ker, IsBlockSL2Embedding (r g) := by
    intro g hg
    refine ⟨(r g).mat 0 0, (r g).mat 0 2, (r g).mat 2 0, (r g).mat 2 2, ?_, ?_⟩
    · have := hdet g hg
      rw [Matrix.det_fin_two] at this
      exact this
    · ext i j
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | exact h11 g hg
        | exact hII.1 g hg _ _ (by decide)
  have hblk : ∀ g, IsBlockSL2Embedding (r g) := by
    intro g
    rcases Int.units_eq_one_or (D.η g) with hg | hg
    · exact hblk0 g hg
    · have hk : D.η (g * D.cc⁻¹) = 1 := by rw [map_mul, map_inv, hg, hηc, mul_inv_cancel]
      have e1 : r g = r (g * D.cc⁻¹) * r D.cc := by rw [← map_mul, inv_mul_cancel_right]
      have hr : (r (g * D.cc⁻¹)).right = 1 := (h.mult _).trans hk
      have e2 : (r g).mat = (r (g * D.cc⁻¹)).mat := by
        have hrc := h.norm.atc
        rw [e1]
        simp only [GG.mat] at hrc ⊢
        rw [SemidirectProduct.mul_left, hr, sgnAct_one, Units.val_mul, hrc, Matrix.mul_one]
      obtain ⟨a, b, c, d, h1, h2⟩ := hblk0 _ hk
      exact ⟨a, b, c, d, h1, e2.trans h2⟩
  let θ : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η
  have hθ0 : ∀ g, (θ g : PadicAlgCl l) = ((D.η g : ℤˣ) : ℤ) := fun g => rfl
  have hθ : ∀ g, (θ g : PadicAlgCl l) = if (r g).right = 1 then 1 else -1 := by
    intro g
    rw [hθ0, h.mult g]
    rcases Int.units_eq_one_or (D.η g) with hg | hg <;> simp [hg]
  obtain ⟨hB1, hB2⟩ := _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.kUse' hK D (θ := θ) (_root_.UpperTheory.V.Z.Kato.used_of_alt hC D hm h hII W hext hWc hW hWd ι (hmod W hext)) ι (hmod W hext)
  haveI : IsAlgClosure K Ω := by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    exact ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have hker : ∀ s : G K Ω, D.η (s.restrictScalars ℚ) = 1 := fun s => by
    have : galEmb ℚ K Ω s ∈ D.η.ker := D.η_ker ▸ galEmb_mem ℚ K Ω s
    exact this
  have hrc : (r D.cc).right = -1 := (h.mult _).trans hηc
  have hWcc : (W D.cc).val = !![-1, 0; 0, 1] := by
    have hx' : (r D.cc).mat = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
      rw [h.norm.atc]; ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hW', wOf_eq hx', if_neg (by rw [hrc]; decide), neg_zero]
  have hA : Af.BlochKatoSelmerVanishes l (repA r hblk) := by
    refine hR W hWc hext hWd (hmod W hext) θ hθ0 _ ⟨D.cc, Jgl _ 2, D.conj, fun s s' hs => ?_, fun s X => ?_, fun X => ?_⟩
    · have e1 : W (s'.restrictScalars ℚ) = W D.cc * W (s.restrictScalars ℚ) * W D.cc := by
        rw [hs, inv_eq_of_mul_eq_one_right hcc, map_mul, map_mul]
      have e2 := hWd (s.restrictScalars ℚ)
      change (W (s.restrictScalars ℚ)).valᵀ * Jmat _ 2 *
        (W (s'.restrictScalars ℚ)).val =
          (θ (s.restrictScalars ℚ) : PadicAlgCl l) • Jmat _ 2
      rw [e1, hθ0, ← e2, Units.val_mul, Units.val_mul, hWcc]
      exact pair_eq _
    · exact pA_ad_one (hblk _) ((h.mult _).trans (hker s)) _ (hW' _) X
    · exact pA_ad_c h.norm.atc hrc X
  intro γ hγ hbk
  have eA : ∀ g X, pA (adRep r g X) = repA r hblk g (pA X) := fun g X => pA_ad (hblk g) X
  have eA' : ∀ g Y, sA (repA r hblk g Y) = adRep r g (sA Y) := fun g Y => ad_sA (hblk g) Y
  have t1 : ∀ g v, Loc.colRep (Af.tw W 1) g v =
      ((if (r g).right = 1 then 1 else 1 : PadicAlgCl l) • wOf (r g)) *ᵥ v := fun g v => by
    rw [← hW', ite_self]
    exact congrArg (· *ᵥ v) (Af.tw_val W 1 g)
  have t2 : ∀ g v, Loc.colRep (Af.tw W θ) g v =
      ((if (r g).right = 1 then 1 else -1 : PadicAlgCl l) • wOf (r g)) *ᵥ v := fun g v => by
    rw [← hW', ← hθ]
    exact congrArg (· *ᵥ v) (Af.tw_val W θ g)
  have eB1 : ∀ g X, pB 1 (adRep r g X) = Loc.colRep (Af.tw W 1) g (pB 1 X) := fun g X => by
    rw [t1]; exact pB_ad (hblk g) 1 (by ring) X
  have eB1' : ∀ g v, sB 1 (Loc.colRep (Af.tw W 1) g v) = adRep r g (sB 1 v) := fun g v => by
    rw [t1]; exact ad_sB (hblk g) 1 (by ring) v
  have eB2 : ∀ g X, pB (-1) (adRep r g X) = Loc.colRep (Af.tw W θ) g (pB (-1) X) := fun g X => by
    rw [t2]; exact pB_ad (hblk g) (-1) (by ring) X
  have eB2' : ∀ g v, sB (-1) (Loc.colRep (Af.tw W θ) g v) = adRep r g (sB (-1) v) := fun g v => by
    rw [t2]; exact ad_sB (hblk g) (-1) (by ring) v
  have hblkz : ∀ g, IsBlockSL2Embedding (r0 D.η D.ΨQ g) := fun g => isBlock_reducible_three_dim _ _ g
  have eC : ∀ g X, pC (adRep r g X) = adRep (r0 D.η D.ΨQ) g (pC X) := fun g X => by
    refine (pC_ad (hblk g) X).trans (Eq.trans ?_ (ad_pC (hblkz g) X).symm)
    rw [h.mult g, unitaryThreeReflection_right]
  have eC' : ∀ g X, pC (adRep (r0 D.η D.ΨQ) g X) = adRep r g (pC X) := fun g X => by
    refine (pC_ad (hblkz g) X).trans (Eq.trans ?_ (ad_pC (hblk g) X).symm)
    rw [h.mult g, unitaryThreeReflection_right]
  obtain ⟨zA, bA⟩ := bk_map (adRep r) (repA r hblk) pA cont_pA eA hγ hbk
  obtain ⟨z1, b1⟩ := bk_map (adRep r) _ (pB 1) (cont_pB 1) eB1 hγ hbk
  obtain ⟨z2, b2⟩ := bk_map (adRep r) _ (pB (-1)) (cont_pB (-1)) eB2 hγ hbk
  obtain ⟨zC, bC⟩ := bk_map (adRep r) _ pC cont_pC eC hγ hbk
  obtain ⟨xA, hxA⟩ := (mem_coboundaries1 _ _).1 (hA _ zA bA)
  obtain ⟨x1, hx1⟩ := (mem_coboundaries1 _ _).1 (hB1 _ z1 b1)
  obtain ⟨x2, hx2⟩ := (mem_coboundaries1 _ _).1 (hB2 _ z2 b2)
  obtain ⟨xC, hxC⟩ := (mem_coboundaries1 _ _).1
    (bloch_kato_nonpositive_weight hC D 0 le_rfl _ zC (fun g => pC_mem (γ g)) bC)
  refine (mem_coboundaries1 _ _).2 ⟨sA xA + (2⁻¹ : PadicAlgCl l) • sB 1 x1 + (2⁻¹ : PadicAlgCl l) • sB (-1) x2 + pC xC, fun g => ?_⟩
  rw [decomp (2⁻¹ : PadicAlgCl l) (by norm_num) (γ g), hxA g, hx1 g, hx2 g, hxC g]
  simp only [map_sub, map_add, map_smul, eA', eB1', eB2', eC', smul_sub]
  abel
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private isLocPt_toBar map_reducible_three_dim coboundary_of_mem_B1 isPush_push from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapReducibleThreeDim
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
theorem UpperTheory.V.Z.J.ptHyp_of_autB_of_lemW_of_isBase :
    U3.CohInp → _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW → _root_.UpperTheory.V.Th.RigidityFirstCase → _root_.UpperTheory.V.Th.RigiditySecondCase → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ), _root_.UpperTheory.V.Aut.AutBAlt D ι g₁ → _root_.UpperTheory.V.Aut.LemWAlt D ι g₁ →
      ∀ x₀ : S.R →ₐ[c.O] c.O, IsBase D.η D.Ψ S.r.hom x₀ → PtHyp D.η S.r.hom x₀ := by
  intro hC hK hRI hRII Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx
  have h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ := by
    have e1 : push (toBar x₀) S.r.hom =
        (GG.map (algebraMap c.O (PadicAlgCl l))).comp (push x₀ S.r.hom) := rfl
    rw [e1, show push x₀ S.r.hom = r0 D.η D.Ψ from hx, map_reducible_three_dim]
    rfl
  refine ⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩
  · rw [h0]
    exact pt_fixed hC D hM (isPt_push D hM S f hf) hU hL
  · have h1 := tanCoc_isBK hC D hM S F (hF ▸ isLocPt_toBar x₀)
    rw [hF, h0] at h1
    rw [h0]
    exact coboundary_of_mem_B1 _ _ (bloch_kato_nonpositive_weight hC D j hj _ h1.1 hw h1.2)
  · have h1 := tanCoc_isBK hC D hM S F (hF ▸ hf.1)
    rw [hF] at h1
    have hp := isPt_push D hM S f hf.1
    have hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
      rcases (twoPt_shape S D.gd.l_odd hM f hf).1 with h | h
      · exact hRI D hM S f hf.1 hp.mult ι h (hB U S _ _ hp.mult (isPush_push f _) h)
      · exact _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.bloch_kato_selmer_vanishes_of_type_ii_modular_ext hC hK hRII D hM S f hf.1 ι h
          (hW U S _ _ (isPush_push f _) h (typeII_facts hC D hM hp h).1)
    exact coboundary_of_mem_B1 _ _ (hz _ h1.1 h1.2)
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private chHom gd_chHom exists_unram isPush_push trace_reducible_three_dim from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OneChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Z.J
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
private theorem oneChar_unramU (hC : U3.CohInp) (hLM : LemmaM) (hLM' : LemmaM') (hLP : LemmaP) (hK : _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW)
    (hRI : _root_.UpperTheory.V.Th.RigidityFirstCase) (hRII : _root_.UpperTheory.V.Th.RigiditySecondCase) (hAd : _root_.UpperTheory.V.Z.J.AdmI_s) (hA : _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt)
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (he : eO l c.O = 1) (hG : GD Ω K l e ψ) (ι : Qbar l ≃+* ℂ) (σ : G K Ω) (t : Qbar l)
    (ht : t = algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ) : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ))⁻¹ : c.Oˣ) : c.O)))
    (hne : ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ →
      (ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ t) :
    Vlen Ω c e ψ ≠ ⊤ ∧ ∃ X : Finset (G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ ρ ∈ X, _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ) ∧ (∀ ρ ∈ X, ∀ ρ' ∈ X, Af.RepIso ρ ρ' → ρ = ρ') ∧
      Vn Ω c e ψ ≤ 2 * ∑ ρ ∈ X, vl l ((ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t) := by
  classical
  obtain ⟨D⟩ := exists_dat hG
  obtain ⟨g₁, hM, hFin, hB, hW⟩ := hA Ω K l c N e ψ D he ι
  obtain ⟨U⟩ := exists_uLoc hC D
  obtain ⟨S⟩ := exists_ring hC D U g₁ hM
  obtain ⟨M⟩ := exists_model hC hLP D hM S
  have hmult : ∀ f : S.R →ₐ[c.O] PadicAlgCl l, HasMult D.η (push f S.r.hom) := fun f g => S.r.hasMult g
  let ρ : (S.R →ₐ[c.O] PadicAlgCl l) → (G K Ω →* GL (Fin 3) (Qbar l)) := fun f => D.rhoK (push f S.r.hom) (hmult f)
  have hσ : D.η (galEmb ℚ K Ω σ) = 1 := by
    rw [← MonoidHom.mem_ker, D.η_ker]
    exact galEmb_mem ℚ K Ω σ
  have htr : ∀ f, trDiff D.η D.Ψ S.r.hom (galEmb ℚ K Ω σ) f =
      (ρ f σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t := by
    intro f
    rw [trDiff, trace_reducible_three_dim, ht]
    congr 1
    exact AddMonoidHom.map_trace (f : S.R →+* PadicAlgCl l) _
  have hadm : ∀ f, TwoPt D.η S.r.hom f → _root_.UpperTheory.V.Z.J.Adm3U_s ι e N (ρ f) ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) (ρ f) := by
    intro f hf
    have hp := isPt_push D hM S f hf.1
    rcases (twoPt_shape S hG.l_odd hM f hf).1 with h | h
    · exact Or.inl (hAd D hM S f hf.1 (hmult f) ι h (hB U S _ _ _ (isPush_push f _) h))
    · exact Or.inr (_root_.UpperTheory.GalN.V.adm2B_rhoK_of_typeII_of_modular_extensions hC D hM hp ι h
        (hW U S _ _ (isPush_push f _) h (typeII_facts hC D hM hp h).1))
  obtain ⟨hlen, T, hT, hTo, hle⟩ := model_upper S M hG.l_odd hM hLM (hFin U S)
    (_root_.UpperTheory.V.Z.J.ptHyp_of_autB_of_lemW_of_isBase hC hK hRI hRII D hM S ι hB hW M.x₀ M.base) (galEmb ℚ K Ω σ) hσ
    fun f hf => by rw [htr]; exact sub_ne_zero.2 (hne _ (hadm f hf))
  have hV := vlen_le hC hLM' D hM S M
  have hinj : ∀ f ∈ T, ∀ f' ∈ T, Af.RepIso (ρ f) (ρ f') → f = f' := by
    rintro f hf f' hf' ⟨g, hg⟩
    obtain ⟨s, hs⟩ := (twoPt_shape S hG.l_odd hM f (hT.1 f hf)).2 f' (hT.1 f' hf').1 ⟨g, fun x hx => by
      rw [D.η_ker, ← range_galEmb] at hx
      obtain ⟨y, rfl⟩ := hx
      exact (congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hg y))).symm⟩
    exact hTo f hf f' hf' s hs
  refine ⟨ne_top_of_le_ne_top hlen hV, T.image ρ, fun x hx => ?_, fun x hx x' hx' h => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    exact hadm f (hT.1 f hf)
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hx'
    rw [hinj f hf f' hf' h]
  · rw [Finset.sum_image fun f hf f' hf' h => hinj f hf f' hf' ⟨1, fun s => by rw [h, one_mul, inv_one, mul_one]⟩]
    simp only [← htr]
    exact (Chr.nrm_mono l hV hlen).trans hle
theorem UpperTheory.V.Z.J.oneCharU_of_katoTwoW_rig_admI_automorphy :
    U3.CohInp → LemmaM → LemmaM' → LemmaP → _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.KatoTwoW → _root_.UpperTheory.V.Th.RigidityFirstCase → _root_.UpperTheory.V.Th.RigiditySecondCase → _root_.UpperTheory.V.Z.J.AdmI_s → _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt → _root_.UpperTheory.V.Z.J.OneCharU_s := by
  intro hC hLM hLM' hLP hK hRI hRII hAd hA Ω _ _ _ K _ _ _ _ _ l _ c N _ e ψ hG ι σ t ht hne
  obtain ⟨c', ψ', he, hψ⟩ := exists_unram c ψ hG.ord
  have h1 : chHom c.O.val.toRingHom ψ = chHom c'.O.val.toRingHom ψ' := MulChar.ext fun a => hψ a
  have hG' : GD Ω K l e ψ' :=
    (gd_chHom c'.O.val.toRingHom Subtype.val_injective ψ').1
      (h1 ▸ (gd_chHom c.O.val.toRingHom Subtype.val_injective ψ).2 hG)
  obtain ⟨h2, h3⟩ := coefIndep Ω l c c' N e ψ ψ' hψ
  have h4 : ∀ g, Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g) =
      Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom (Chr.Psi l e (Chr.dirG ℚ Ω ψ') g) := by
    intro g
    simp only [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow]
    congr 1
    exact Units.ext (hψ _)
  have h5 := congrArg Units.val (h4 (galEmb ℚ K Ω σ))
  have h6 := congrArg (fun u : (PadicAlgCl l)ˣ => (u⁻¹).val) (h4 (galEmb ℚ K Ω σ))
  rw [Ne, h2, h3]
  refine oneChar_unramU hC hLM hLM' hLP hK hRI hRII hAd hA Ω K l c' N e ψ' he hG' ι σ t ?_ hne
  rw [ht, map_add, map_add, map_add, map_add, map_one, map_one]
  exact congrArg₂ (· + ·) (congrArg (· + 1) h5) h6
end
end
