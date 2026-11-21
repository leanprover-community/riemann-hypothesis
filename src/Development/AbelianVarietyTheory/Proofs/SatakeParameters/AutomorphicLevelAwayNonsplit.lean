import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalLocalOperators
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormMemOfUnderEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinApproxOfPolyApproxTrc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerOfLinApprox
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

noncomputable section

namespace GlobalTheory.FrobOpsIdx
open Polynomial

theorem frobOpsIdx : SphOps → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (Kw : Levels E a) (W0 : Set (HeightOneSpectrum (𝓞 E))), (∀ w ∈ W0, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ Kw w = GlobalTheory.LFun.KGL w a) → ∃ (J : Type) (T : LocOps l ι Kw J) (x fr : J → G E Ω) (n : J → ℕ), (∀ j, x j = (fr j)⁻¹ ^ n j) ∧ (∀ j, T.pl j ∈ W0 ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A (T.pl j) ∧ IsFrob A (normV (T.pl j)) (fr j)) ∧ (∀ w ∈ W0, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s : G E Ω, IsFrob A (normV w) s → ∃ j, T.pl j = w ∧ fr j = s ∧ n j = 1) ∧ (∀ j g, ∃ q : ℚ, T.f j g = q) ∧ (∀ (j : J) (σ : SmIrr (GL (Fin a) ((T.pl j).adicCompletion E))), GlobalTheory.PRep.fixed σ.ρ (Kw (T.pl j)) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL (T.pl j) σ.ρ B → ∀ ρ : G E Ω →* GL (Fin a) (Qbar l), ((ρ (fr j)⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV (T.pl j)) B).map fun b => Polynomial.X - Polynomial.C b).prod → ι.symm (T.z j σ) = trc ρ (x j)) ∧ ∀ w ∈ W0, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), GlobalTheory.PRep.fixed σ.ρ (Kw w) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL w σ.ρ B → ∀ r : G E Ω →* GL (Fin a) (Qbar l), (∀ j (h : T.pl j = w), trc r (x j) = ι.symm (T.z j (h ▸ σ))) → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s : G E Ω, IsFrob A (normV w) s → ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro hS E Ω _ _ _ _ _ _ l _ ι a Kw W0 hW
  classical
  have hl : l.Prime := Fact.out
  let J : Type := {p : HeightOneSpectrum (𝓞 E) × ValuationSubring Ω × G E Ω × ℕ //
    p.1 ∈ W0 ∧ IsPlaceOver p.2.1 p.1 ∧ IsFrob p.2.1 (normV p.1) p.2.2.1 ∧ 1 ≤ p.2.2.2}
  have hf : ∀ j : J, ∃ f : GL (Fin a) (j.1.1.adicCompletion E) →₀ ℂ,
      (∀ g, ∃ (m : ℤ) (e : ℕ), f g = (m : ℂ) / ((normV j.1.1 : ℕ) : ℂ) ^ e) ∧
      ∀ (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B →
        ∀ v ∈ PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 a),
          opOf σ.ρ f v = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ ((j.1.2.2.2 : ℕ) : ℤ))).sum • v :=
    fun j => (hS E j.1.1 a).2 (j.1.2.2.2 : ℤ)
  let zz : ∀ j : J, SmIrr (GL (Fin a) (j.1.1.adicCompletion E)) → ℂ := fun j σ =>
    if h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B then
      ((UpperTheory.V.Af.algSat a (normV j.1.1) h.choose).map (· ^ j.1.2.2.2)).sum else 0
  have hz : ∀ (j : J) (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ),
      GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B → zz j σ = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ j.1.2.2.2)).sum := by
    intro j σ B hB
    have h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B := ⟨B, hB⟩
    simp only [zz, dif_pos h]
    rw [show h.choose = B from h.choose_spec.unique hB]
  let T : LocOps l ι Kw J :=
    { pl := fun j => j.1.1
      split := fun j => (hW _ j.2.1).1
      away := fun j => (hW _ j.2.1).2.1
      f := fun j => (hf j).choose
      int := fun j g => by
        obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
        rw [he]
        exact GlobalTheory.FrobOps.norm_le_one ι m _ e (GlobalTheory.FrobOps.not_dvd_normV hl _ (hW _ j.2.1).2.1)
      z := zz
      act := fun j σ v hv => by
        rw [(hW _ j.2.1).2.2] at hv
        by_cases h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B
        · obtain ⟨B, hB⟩ := h
          rw [hz j σ B hB, (hf j).choose_spec.2 σ B hB v hv]
          simp only [zpow_natCast]
        · have h0 : PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 a) = ⊥ := by
            by_contra hne
            exact h ((hS E j.1.1 a).1 σ hne)
          rw [h0, Submodule.mem_bot] at hv
          subst hv
          simp [opOf] }
  let fr : J → G E Ω := fun j => j.1.2.2.1
  let nn : J → ℕ := fun j => j.1.2.2.2
  let x : J → G E Ω := fun j => (fr j)⁻¹ ^ nn j
  refine ⟨J, T, x, fr, nn, fun j => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨j.2.1, j.1.2.1, j.2.2.1, j.2.2.2.1⟩
  · intro w hw A hA s hsF
    exact ⟨⟨(w, A, s, 1), hw, hA, hsF, le_rfl⟩, rfl, rfl, rfl⟩
  · intro j g
    obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
    refine ⟨(m : ℚ) / ((normV j.1.1 : ℕ) : ℚ) ^ e, ?_⟩
    show (hf j).choose g = _
    rw [he]
    push_cast
    rfl
  · intro j σ _ B hB ρ hFE
    show ι.symm (zz j σ) = trc ρ (x j)
    rw [hz j σ B hB]
    apply ι.injective
    rw [RingEquiv.apply_symm_apply, GlobalTheory.FrobOps.iota_trc]
    exact (GlobalTheory.FrobOps.trace_pow_of_charpoly _ _ (by rw [Matrix.charpoly_map]; exact hFE) _).symm
  · intro w hw σ _ B hBσ r hr A hA s hsF
    rw [← Matrix.charpoly_map]
    refine GlobalTheory.CharpolyNewton.charpoly_eq_prod_of_trace_pow ℂ a _ _ ?_ ?_
    · simp [UpperTheory.V.Af.algSat, hBσ.card]
    · intro n hn
      let j : J := ⟨(w, A, s, n), hw, hA, hsF, hn⟩
      have h2 : trc r (x j) = ι.symm (zz j σ) := hr j rfl
      rw [hz j σ B hBσ] at h2
      rw [← GlobalTheory.FrobOps.iota_trc]
      change ι (trc r (x j)) = _
      rw [h2, RingEquiv.apply_symm_apply]

end GlobalTheory.FrobOpsIdx
end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL
namespace GlobalTheory.CongL.SatConj

theorem exists_satU_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w u : HeightOneSpectrum (𝓞 E), IsSplitAt w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∃ B, SatU U w B) → ∃ B, SatU U u B := by
  intro E _ _ _ a U hU w u hw hu ⟨B, σ, ⟨hirr, f, hf0, hfm, hf⟩, hS⟩
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.1
  have hf' : ∀ g x, f (σ.ρ g x) = RU E a (GlobalTheory.SplitPts.locPt hw g).1 (f x) := fun g x => by
    have := hf (GlobalTheory.SplitPts.locPt hw g) x
    simpa [GlobalTheory.SplitPts.cLoc_locPt hw g] using this
  have hinj : Function.Injective f := by
    have hk := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr).2 (LinearMap.ker f) (fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hf', hx, map_zero])
    rcases hk with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
  have hloc : locU a u = locU a w := by
    unfold locU
    rw [hu]
  have hsu : IsSplitAt u := by
    by_cases h : u = w
    · exact h ▸ hw
    · exact ⟨w, Ne.symm h, hu.symm⟩
  have hKw : ∀ x : UA E a, cLoc u x ∈ GlobalTheory.LFun.KGL u a → cLoc w x ∈ GlobalTheory.LFun.KGL w a := by
    intro x hx
    rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu with rfl | rfl
    · exact hx
    · have := GlobalTheory.BCT.GlobLev.integral_conjSrc x _ hx
      rwa [GlobalTheory.SplitPts.conjSrc_conjSrc_cm] at this
  have hfix : ∀ x ∈ locU a u, cLoc u x ∈ GlobalTheory.LFun.KGL u a → RU E a x (f v) = f v := by
    intro x hx hk
    have hx' : x ∈ locU a w := hloc ▸ hx
    have h1 : σ.ρ (cLoc w x) v = v := by simpa using hv ⟨_, hKw x hk⟩
    have h2 := hf ⟨x, hx'⟩ v
    rw [← h2]
    exact congrArg f h1
  obtain ⟨σ', S, hloc', hS', -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU u hsu (f v) (hfm v)
    (fun h => hv0 (hinj (h.trans (map_zero f).symm))) hfix
  exact ⟨S, σ', hloc', hS'⟩

end GlobalTheory.CongL.SatConj
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL.UnitLim

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finite_not_sph (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (hU : IsAutRepU U) :
    {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w ∧ ¬ ∃ B, SatU U w B}.Finite := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU E a) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU E a)) := (hU.aut φ hφ).level
  have hev : ∀ᶠ w in Filter.cofinite, IsSplitAt w → ∃ B, SatU U w B := by
    filter_upwards [GlobalTheory.BCT.GlobLev.eventually_locU_mem E a L hLo] with w hw hs
    obtain ⟨σ, B, hc, hB, -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU w hs φ hφ hφ0
      fun x hx hxK => hw x hx hxK hx.1
    exact ⟨B, σ, hc, hB⟩
  exact (Filter.eventually_cofinite.1 hev).subset fun w hw h => hw.2 (h hw.1)

theorem dense_frob_usable_off (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) (hl : l.Prime) (d : ℕ) (hd : ImQ E d) (X : Finset (HeightOneSpectrum (𝓞 E))) :
    Dense {g : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), w ∉ X ∧ UsPl d w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ApartAll X w ∧
      ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) g} := by
  classical
  set M : ℕ := l * (2 * d) * ∏ u ∈ X, Ideal.absNorm u.asIdeal with hM
  have hM0 : M ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hl.ne_zero (mul_ne_zero two_ne_zero hd.1.ne')) ?_
    rw [Finset.prod_ne_zero_iff]
    intro u _
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  have hS1 : {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 E)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have hS3 := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).2
  set S := {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 E)}} ∪
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.ramificationIdx ℤ ≠ 1} with hSdef
  have hS : S.Finite := hS1.union hS3
  have hdense := GlobalTheory.Published.chebotarevDegreeOne'.dense (F := E) (Ω := Ω) hS
  refine hdense.mono ?_
  rintro g ⟨w, hwS, hdeg, A, hA, hg⟩
  simp only [hSdef, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hwS
  obtain ⟨hM', hram⟩ := hwS
  have hMw : ((M : ℕ) : 𝓞 E) ∉ w.asIdeal := fun h => hM' (Ideal.dvd_span_singleton.2 h)
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).2 hdeg
  have hX : ∀ u ∈ X, ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∉ w.asIdeal := fun u hu h =>
    hMw (GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hu) _) h)
  refine ⟨w, fun hwX => hX w hwX (Ideal.absNorm_mem _), ?_, ?_, ?_, A, hA, hg⟩
  · refine GlobalTheory.DenseUsable.usPl_of_absNorm_prime hd w hp hram fun h => hMw ?_
    exact GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_right (dvd_mul_left _ _) _) h
  · exact fun h => hMw (GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_right (dvd_mul_right _ _) _) h)
  · intro u hu hwu
    exact hX u hu (GlobalTheory.DenseUsable.absNorm_mem_of_under_eq w u hwu)

end GlobalTheory.CongL.UnitLim
end
