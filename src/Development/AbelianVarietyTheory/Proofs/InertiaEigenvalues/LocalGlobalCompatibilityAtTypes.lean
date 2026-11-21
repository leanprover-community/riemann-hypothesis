import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.WildUnipotent

open Polynomial in

theorem exists_pow_sub_one_eq {O : Type} [CommRing O] {n l : ℕ} (hl : l.Prime) (u : Matrix (Fin n) (Fin n) O)
    (hu : u.charpoly = (X - 1) ^ n) (M : ℕ) :
    ∃ c : Matrix (Fin n) (Fin n) O, u ^ (l ^ (n + M)) - 1 = ((l : O) ^ (M + 1)) • c := by
  have h0 : (u - 1) ^ n = 0 := by
    have := Matrix.aeval_self_charpoly u
    rw [hu] at this
    simpa using this
  have h1 : (u - 1) ^ (l ^ n) = 0 := pow_eq_zero_of_le (Nat.lt_pow_self hl.one_lt).le h0
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (1 : O[X]) (X - 1) n
  have h2 : (l : O[X]) ∣ X ^ (l ^ n) - (1 + (X - 1) ^ (l ^ n)) := by
    rw [add_sub_cancel, one_pow] at hr
    rw [hr, add_sub_cancel_left, mul_assoc, mul_assoc]
    exact dvd_mul_right _ _
  obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub h2 M
  refine ⟨aeval u c, ?_⟩
  have h3 := congrArg (aeval u) hc
  simp only [map_sub, map_pow, map_add, map_one, aeval_X, h1, add_zero, one_pow, map_mul, map_natCast] at h3
  rw [pow_add, pow_mul, h3, Algebra.smul_def, map_pow, map_natCast]

theorem eq_one_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime) (hA : ¬ A.valuation (l : Ω) < 1)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (had : IsAdic (IsLocalRing.maximalIdeal O)) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O)
    {n : ℕ} (r : G E Ω →* GL (Fin n) O)
    (hr : Continuous (fun g => ((r g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)))
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1)
    (hc : ((r σ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).charpoly = (Polynomial.X - 1) ^ n) : r σ = 1 := by
  have key : ∀ M : ℕ, ∀ a b, (((r σ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) - 1) a b ∈
      IsLocalRing.maximalIdeal O ^ M := by
    intro M
    let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M)
    let H : Subgroup (G E Ω) := ((Matrix.GeneralLinearGroup.map q).comp r).ker
    have hH : ∀ g, g ∈ H ↔ ∀ a b, (((r g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) - 1) a b ∈
        IsLocalRing.maximalIdeal O ^ M := by
      intro g
      rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
      refine forall_congr' fun a => forall_congr' fun b => ?_
      rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
      have e : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M) ((1 : Matrix (Fin n) (Fin n) O) a b) =
          (1 : Matrix (Fin n) (Fin n) (O ⧸ IsLocalRing.maximalIdeal O ^ M)) a b := by
        by_cases h : a = b <;> simp [Matrix.one_apply, h]
      rw [e]
      rfl
    have ho : IsOpen (H : Set (G E Ω)) := by
      have e : (H : Set (G E Ω)) = ⋂ a, ⋂ b,
          (fun g => (((r g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) - 1) a b) ⁻¹'
            ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
        ext g
        simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
        exact hH g
      rw [e]
      refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
      exact ((isAdic_iff.1 had).1 M).preimage ((hr.sub continuous_const).matrix_elem a b)
    refine (hH σ).1 (GlobalTheory.WildKill.mem_of_wild A H ho σ (l ^ (n + M)) ?_ hσ ?_)
    · have h1 : A.valuation (l : Ω) = 1 :=
        le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hA)
      rw [Nat.cast_pow, map_pow, h1, one_pow]
      exact lt_irrefl _
    · rw [hH]
      intro a b
      obtain ⟨c, hc'⟩ := exists_pow_sub_one_eq hl _ hc M
      rw [map_pow, Units.val_pow_eq_pow_val, hc', Matrix.smul_apply, smul_eq_mul, pow_succ, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlO M)
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  ext a b
  have h2 := Ideal.mem_iInf.2 fun M => key M a b
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
  simpa using h2

theorem main : ∀ (D : D7) (i : D.nd.Loc) (n : ℕ) (r : GE D.nd →* GL (Fin n) (D.nd.O i)), Continuous (fun g => ((r g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i))) → ∀ v : HeightOneSpectrum (𝓞 D.host.E), v ∉ placesOver D.host.E (D.nd.l i) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), ((r σ : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i)).charpoly = (Polynomial.X - 1) ^ n → r σ = 1 := by
  intro D i n r hr v hv σ hσ hc
  have := D.nd.trO i
  refine eq_one_of_wild (D.nd.plOm.1 v) (l := D.nd.l i) Fact.out ?_ (D.nd.O_adic i)
    (GlobalTheory.WildAdditive.not_isUnit_natCast (D.nd.l i) (D.nd.O i)) r hr σ hσ hc
  intro h
  apply hv
  have hA : IsPlaceOver (D.nd.plOm.1 v) v := D.nd.plOm.2 v
  show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal
  rw [← hA]
  simpa using h

end GlobalTheory.WildUnipotent
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.WildSetSQ

theorem char_eq_one_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O)) (χ : G E Ω →* Oˣ)
    (hχ : Continuous fun g => ((χ g : Oˣ) : O)) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1)
    (h : χ σ ^ m = 1) : χ σ = 1 := by
  have key : ∀ M : ℕ, ((χ σ : Oˣ) : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ M := by
    intro M
    let H : Subgroup (G E Ω) :=
      ((Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M)).toMonoidHom).comp χ).ker
    have hH : ∀ g, g ∈ H ↔ ((χ g : Oˣ) : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ M := by
      intro g
      rw [← Ideal.Quotient.eq, map_one, MonoidHom.mem_ker, Units.ext_iff]
      rfl
    have ho : IsOpen (H : Set (G E Ω)) := by
      have e : (H : Set (G E Ω)) = (fun g => ((χ g : Oˣ) : O) - 1) ⁻¹'
          ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
        ext g
        exact hH g
      rw [e]
      exact ((isAdic_iff.1 had).1 M).preimage (hχ.sub continuous_const)
    refine (hH σ).1 (GlobalTheory.WildKill.mem_of_wild A H ho σ m hm hσ ?_)
    rw [hH, map_pow, h, Units.val_one, sub_self]
    exact zero_mem _
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  have h2 := Ideal.mem_iInf.2 key
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
  simpa using h2

theorem coprime_pred (g : ℕ) (hg : 1 ≤ g) : (g - 1).Coprime g := by
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  simp

end GlobalTheory.WildSetSQ

namespace GlobalTheory.WildSetSQ

theorem chi_wild_over_g (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) (hS : v ∈ D.nd.S i)
    (k : Fin 2) (hk : v ∈ placesOver D.host.E (D.host.g k)) (σ : GE D.nd)
    (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 v)) : D.nd.chi i 1 σ = 1 := by
  have hvl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inl hS)
  have hvQ : v ∉ D.nd.Q i := Finset.disjoint_left.1 (D.nd.SQ_disj i) hS
  have hpl := D.nd.plOm.2 v
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ
  have hψ : D.ntw.psiL i σ = 1 := by
    by_contra h
    exact hvQ ((D.ntw.psiL_ram i v _ hpl).1 ⟨σ, hI, h⟩)
  have hl : D.ntw.l (D.ntw.twOf i) = D.nd.l i := D.ntw.twOf_l i
  have ht := D.ntw.twistCharacterFamily_tame (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) k v hk (by rw [hl]; exact hvl) _ hpl σ hI
  have hpow : D.nd.chi i 1 σ ^ (D.host.g k - 1) = 1 := by
    rw [D.ntw.chi_tw i, MonoidHom.mul_apply, hψ, mul_one, MonoidHom.comp_apply, ← map_pow, ht, map_one]
  have := D.nd.trO i
  have hgv : (D.nd.plOm.1 v).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := hk
    have h2 := (hpl _).2 h1
    simpa using h2
  exact char_eq_one_of_wild (D.nd.plOm.1 v) (D.nd.O_adic i) (D.nd.chi i 1) (D.nd.chi_cont i 1) σ hσ _
    (GlobalTheory.WildKill.not_lt_one_of_coprime _ (coprime_pred _ (D.host.g_prime k).one_lt.le) hgv) hpow

theorem r_wild_diag (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : SumRepresentations.ConclusionG5 D) (hHG : HG D.nd D.naut i) (hr : GoodR D.nd i r) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∈ D.nd.S i ∨ v ∈ D.nd.Q i)
    (hcase : v ∈ D.nd.Q i ∨ v ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde'))
    (σ : GE D.nd) (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 v)) (hχ : D.nd.chi i 1 σ = 1) (x : D.nd.X i) :
    r x σ = 1 := by
  obtain ⟨ha, -⟩ := h32 i hHG r hr v hv (D.nd.SQ_l i v hv)
  obtain ⟨-, Pm, hPm⟩ := ha hcase x
  have h1 := hPm σ (GlobalTheory.TameGenPowers.wild_mem_Ine hσ)
  have hc : chi1 D.nd i σ = 1 := by
    show ((D.nd.chi i 1 σ : (D.nd.O i)ˣ) : D.nd.O i) = 1
    rw [hχ, Units.val_one]
  rw [hc, map_one] at h1
  have hd : (Matrix.diagonal fun k : Fin D.R.nV =>
      if (k : ℕ) < D.R.r then (1 : Kf D.nd i) else 1) = 1 := by
    simp
  rw [hd] at h1
  have h2 : Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x) σ * Pm = 1 := Units.ext h1
  have h3 : mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x) σ = 1 := by
    have := congrArg (fun g => Pm * g * Pm⁻¹) h2
    simpa [mul_assoc] using this
  have hinj : Function.Injective (algebraMap (D.nd.O i) (Kf D.nd i)) :=
    IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  have e : ((r x σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
      (algebraMap (D.nd.O i) (Kf D.nd i)) =
      ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x) σ : GL _ _) : Matrix _ _ (Kf D.nd i)) := rfl
  have h4 : ((r x σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
      (algebraMap (D.nd.O i) (Kf D.nd i)) =
      ((1 : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
      (algebraMap (D.nd.O i) (Kf D.nd i)) := by
    rw [e, h3, Units.val_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Units.ext (Matrix.map_injective hinj h4)

theorem r_wild_over_g (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (v : HeightOneSpectrum (𝓞 D.host.E)) (hvl : v ∉ placesOver D.host.E (D.nd.l i))
    (hL : ∀ x, ∃ P, D.naut.ptV i P = some x ∧ D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) v =
      D.naut.lpTw (D.naut.locV i P v) ((1 - (D.R.nV : ℝ)) / 2))
    (hIne : ∀ P : D.naut.AV i, ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v),
      D.naut.inePol (D.naut.locV i P v) σ = (Polynomial.X - 1) ^ D.R.nV)
    (σ : GE D.nd) (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 v)) (x : D.nd.X i) : r x σ = 1 := by
  obtain ⟨P, -, hP⟩ := hL x
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ
  have hcont := SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  have hine : D.naut.inePol (D.naut.locV i P v) σ =
      (((r x σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map (iotaO D.nd D.naut i) := by
    rw [← D.naut.inePol_tw (D.naut.locV i P v) ((1 - (D.R.nV : ℝ)) / 2) _ hI, ← hP,
      ← D.naut.wdOf_ine i _ v hvl hcont _ hI]
    have : ((mapRep (iotaOQ D.nd D.naut i) (r x) σ : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) =
        ((r x σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i) := rfl
    rw [this, Matrix.charpoly_map, Polynomial.map_map]
    rfl
  rw [hIne P σ hσ] at hine
  have hc : ((r x σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly =
      (Polynomial.X - 1) ^ D.R.nV := by
    apply Polynomial.map_injective _ hinj
    rw [← hine, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  exact GlobalTheory.WildUnipotent.main D i _ (r x) (hr x).1 v hvl σ hσ hc

end GlobalTheory.WildSetSQ

namespace GlobalTheory.WildSetSQ

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), SumRepresentations.ConclusionG5 D → HG D.nd D.naut i → GoodR D.nd i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i → TameCharacterConditions D i → (∀ w ∈ D.nd.S i, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → (∀ x, ∃ P, D.naut.ptV i P = some x ∧ D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w = D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ P : D.naut.AV i, ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), D.naut.inePol (D.naut.locV i P w) σ = (Polynomial.X - 1) ^ D.R.nV) → PairedCharacterCondition.SetSQ i r := by
  intro D i r h32 hHG hr hadm hjc hLG
  refine ⟨fun v hv => ⟨(hadm v hv).1, fun g hg => ?_⟩, fun q hq => (hadm q (Or.inr hq)).2.2.1 hq⟩
  have hvl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v hv
  by_cases hA : v ∈ D.nd.Q i ∨ v ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')
  · have hjv : v ∈ D.nd.Q i ∨ (v ∈ D.nd.S i ∧ (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde'))) := by
      rcases hA with h | h
      · exact Or.inl h
      · rcases hv with hS | hQ
        · exact Or.inr ⟨hS, h⟩
        · exact Or.inl hQ
    have hχ : D.nd.chi i 1 g = 1 := hjc.1 v hjv g hg
    exact ⟨fun x => r_wild_diag D i r h32 hHG hr v hv hA g hg hχ x, hχ⟩
  · have hS : v ∈ D.nd.S i := hv.resolve_right fun h => hA (Or.inl h)
    obtain ⟨k, hk⟩ : ∃ k, v ∈ placesOver D.host.E (D.host.g k) := by
      obtain ⟨h1, -⟩ := (D.nd.S_def i v).1 hS
      rcases h1 with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exfalso
        split_ifs at h with he
        · exact hA (Or.inr (Or.inr ⟨he, h⟩))
        · exact hA (Or.inr (Or.inl h))
    obtain ⟨hL, hIne⟩ := hLG v hS ⟨k, hk⟩
    exact ⟨fun x => r_wild_over_g D i r hr v hvl hL hIne g hg x, chi_wild_over_g D i v hS k hk g hg⟩

end GlobalTheory.WildSetSQ
end
