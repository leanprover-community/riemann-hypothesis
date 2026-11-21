import Mathlib
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaInfl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.GalTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.PlaceTransport

section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.vLenIndep :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D D' : LData F Ω l) (e : ℤ), D.S = D'.S ∧ VLen D e = VLen D' e := by
  intro F Ω _ _ _ _ _ l _ D D' e
  have hS : D.S = D'.S := Finset.coe_injective (D.hS.trans D'.hS.symm)
  refine ⟨hS, ?_⟩
  obtain ⟨S, hS₁, A, hA, chi, hchi⟩ := D
  obtain ⟨S', hS₂, A', hA', chi', hchi'⟩ := D'
  dsimp only at hS
  subst hS
  have hc : chi = chi' := by
    refine MonoidHom.ext fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact DFunLike.congr_fun (hchi.trans hchi'.symm) g
  subst hc
  rfl
end

section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.imageConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → decImage F l A = decImage F l A' ∧ ineImage F l A = ineImage F l A' := by
  intro F Ω _ _ _ _ _ l _ v
  have hc : ∀ g σ : G F Ω, cycZ F Ω l (g⁻¹ * σ * g) = cycZ F Ω l σ := fun g σ => by
    rw [map_mul, map_mul, map_inv, mul_comm _ (cycZ F Ω l σ), inv_mul_cancel_right]
  have key : ∀ A A' : ValuationSubring Ω, IsPlaceOver A v → IsPlaceOver A' v →
      decImage F l A' ≤ decImage F l A ∧ ineImage F l A' ≤ ineImage F l A := by
    intro A A' hA hA'
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hA'
    constructor
    · rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨_, GlobalTheory.Cut.ShaBound.conj_mem_Dec hσ, hc g σ⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨_, GlobalTheory.Cut.ShaBound.conj_mem_Ine' hσ, hc g σ⟩
  intro A A' hA hA'
  exact ⟨le_antisymm (key A' A hA' hA).1 (key A A' hA hA').1,
    le_antisymm (key A' A hA' hA).2 (key A A' hA hA').2⟩
end

section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.shaAbsRes :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 F'))) (φ : G F' Ω' →* G F Ω) (hφ : Continuous φ),
      (∀ (v' : HeightOneSpectrum (𝓞 F')) (A' : ValuationSubring Ω'), IsPlaceOver A' v' → ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v ∧ (v ∈ S ↔ v' ∈ S') ∧
        (∀ g ∈ Dec (F := F') A', φ g ∈ Dec (F := F) A) ∧ ∀ g ∈ Ine (F := F') A', φ g ∈ Ine (F := F) A) →
      ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R (G F Ω) M), (∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S') ∧
        (Function.Surjective φ → Module.length R (ShaAbs ρ S) ≤ Module.length R (ShaAbs (ρ.comp φ) S')) := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ S S' φ hφ h R _ M _ _ _ _ _ ρ
  have h1 : ∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S' := by
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨ha, hb⟩ := (mk_mem_ShaAbs ρ S z).1 hx
    refine (mk_mem_ShaAbs (ρ.comp φ) S' (restrictCocycles1 ρ φ hφ z)).2 ⟨?_, ?_⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, hD, -⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := ha v (hS.2 hv') A hA
      exact ⟨m, fun g hg => hm (φ g) (hD g hg)⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, -, hI⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := hb v (fun hv => hv' (hS.1 hv)) A hA
      exact ⟨m, fun g hg => hm (φ g) (hI g hg)⟩
  refine ⟨h1, fun hs => ?_⟩
  have hinj : Function.Injective (resH1 ρ φ hφ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : (Submodule.Quotient.mk (restrictCocycles1 ρ φ hφ z) : H1 (ρ.comp φ)) = 0 := hx
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx')
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)
    obtain ⟨g', rfl⟩ := hs g
    exact hm g'
  refine Module.length_le_of_injective ((resH1 ρ φ hφ).restrict h1) ?_
  intro x y hxy
  exact Subtype.ext (hinj (congrArg Subtype.val hxy))
end

section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem map_Sha (D : LData F Ω l) (e : ℤ) :
    (Sha D e).map (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) =
      ShaAbs ((qzTw D e).comp (toGS Ω _)) (Above F l) := by
  rw [← D.hS]
  exact shaInfl F Ω D.S D.A D.hA _ _ _ (contTw F Ω l D e).1

theorem injective_infl (D : LData F Ω l) (e : ℤ) :
    Function.Injective (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) :=
  (infUnram F Ω _ _ _ _ (contTw F Ω l D e).1).1

theorem shaLen_eq_abs (D : LData F Ω l) (e : ℤ) :
    shaLen D e = Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) := by
  rw [← qzTw_comp_toGS D e, ← map_Sha]
  exact (Submodule.equivMapOfInjective _ (injective_infl D e) _).length_eq

variable {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω']

theorem length_ShaAbs_le (f : F ≃+* F') (e : ℤ) :
    Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) ≤
      Module.length ℤ_[l] (ShaAbs (qzG F' Ω' l e) (Above F' l)) := by
  let σ : Ω ≃+* Ω' := IsAlgClosure.equivOfEquiv Ω Ω' f
  have hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f.toRingHom x) :=
    fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω' f x
  obtain ⟨φ, h1, h2, h3, -, h5⟩ := galTransport F Ω F' Ω' f.toRingHom σ hσ
  have e1 : (qzG F Ω l e).comp φ = qzG F' Ω' l e := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [MonoidHom.comp_apply, qzG_apply, qzG_apply, h3]
  rw [← e1]
  refine (shaAbsRes F Ω F' Ω' _ _ φ h1 (fun v' A' hA' => ?_) _ _ _).2 (h5 f.surjective)
  obtain ⟨v, A, a, b, -, c, d⟩ := placeTransport F Ω F' Ω' f.toRingHom σ hσ φ h2 v' A' hA'
  exact ⟨v, A, a, b l, fun g hg => (c g).2 hg, fun g hg => (d g).2 hg⟩

theorem shaLen_congr (f : F ≃+* F') (D : LData F Ω l) (D' : LData F' Ω' l) (e : ℤ) : shaLen D e = shaLen D' e := by
  rw [shaLen_eq_abs, shaLen_eq_abs]
  exact le_antisymm (length_ShaAbs_le f e) (length_ShaAbs_le f.symm e)

theorem shaLen_eq_shaInv (D : LData F Ω l) (e : ℤ) : shaLen D e = shaInv F l e := by
  rw [shaLen_eq_abs]
  exact le_antisymm (length_ShaAbs_le (RingEquiv.refl F) e) (length_ShaAbs_le (RingEquiv.refl F) e)

theorem shaInv_congr (f : F ≃+* F') (e : ℤ) : shaInv F l e = shaInv F' l e :=
  le_antisymm (length_ShaAbs_le f e) (length_ShaAbs_le f.symm e)

end

theorem indep : Indep := fun F Ω _ _ _ _ _ l _ D D' e => by
  refine ⟨shaLen_congr (RingEquiv.refl F) D D' e, (vLenIndep F Ω l D D' e).2, ?_⟩
  have hS := (vLenIndep F Ω l D D' e).1
  rw [local_H0_length_eq_sum, local_H0_length_eq_sum]
  refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun v => by rw [hS]) _ _ fun v => ?_
  rw [(imageConj F Ω l v.1 _ _ (D.hA v) (D'.hA ⟨v.1, hS ▸ v.2⟩)).1]
  rfl

theorem vvle_iff_shaInv (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) :
    UpperTheory.Top.VVle E t B ↔
      (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t → shaInv E p (e : ℤ) ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((@shaInv E _ _ l ⟨l.2⟩ (e : ℤ)).toNat : ℝ) ≤ B := by
  constructor
  · intro h
    have := h (AlgebraicClosure E) fun p _ => (ldata_nonempty p).some
    simpa only [shaLen_eq_shaInv] using this
  · intro h Ω _ _ _ ld
    simpa only [shaLen_eq_shaInv] using h


end UpperTheory.V.LDataCardLeFinrank

end
end
