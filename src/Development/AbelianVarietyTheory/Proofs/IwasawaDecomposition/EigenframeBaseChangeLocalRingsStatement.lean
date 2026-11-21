import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam

theorem FlagCpt.fromTest_and_val_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e), (letI := (constF e C.Y).toAlgebra; FromTest (K := c.F) (fun R _ _ => FrPt Xo c R) (fun φ y z => FrMap φ y z) C.y0) ∧ C.val 1 = 1 ∧ (∀ f g, C.val (f * g) = C.val f * C.val g) ∧ (∀ f g, C.val (f + g) = C.val f + C.val g) ∧ ∀ (a : c.F) f, C.val (a • f) = constF e C.Y a * C.val f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C
  letI := (constF e C.Y).toAlgebra
  have hA : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hT := hA C.Y.Fn C.y0
  exact ⟨hT, evalAt_one _ _ C.y0 hT, fun f g => evalAt_mul _ _ f g C.y0,
    fun f g => evalAt_add _ _ f g C.y0, fun a f => evalAt_smul _ _ a f C.y0⟩

end GlobalTheory.ShFam
end

section
namespace GlobalTheory.PointFunction

open IsLocalRing

theorem nonempty_algHom_algebraicClosure (F k : Type) [Field F] [Field k] [IsAlgClosed k]
    [Algebra F k] : Nonempty (AlgebraicClosure F →ₐ[F] k) :=
  ⟨IsAlgClosed.lift⟩

theorem exists_common_factor (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (q : Ideal A) [q.IsPrime] (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : A →ₐ[K] k)
    (hφ : ∀ a, φ a = 0 ↔ a ∈ q) :
    ∃ χ : AlgebraicClosure q.ResidueField →ₐ[K] k,
      χ.comp (IsScalarTower.toAlgHom K A (AlgebraicClosure q.ResidueField)) = φ := by
  letI : Algebra A k := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A k := .of_algebraMap_eq fun x => (φ.commutes x).symm
  let g : q.ResidueField →ₐ[A] k := Ideal.ResidueField.liftₐ q (Algebra.ofId A k)
    (fun a ha => (hφ a).2 ha) (fun a ha => by
      have : φ a ≠ 0 := fun h => ha ((hφ a).1 h)
      exact isUnit_iff_ne_zero.2 this)
  letI : Algebra q.ResidueField k := g.toRingHom.toAlgebra
  haveI : IsScalarTower A q.ResidueField k := .of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨χ⟩ := nonempty_algHom_algebraicClosure q.ResidueField k
  refine ⟨(χ.restrictScalars A).restrictScalars K, ?_⟩
  ext a
  exact (χ.restrictScalars A).commutes a

theorem valuationSubring_step (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (A →ₐ[K] k) → k)
    (h2 : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V],
      IsAlgClosed (FractionRing V) → ∀ ι : A →ₐ[K] V, ∃ v : V,
        ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : V →ₐ[K] k),
          W k (φ.comp ι) = φ v)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (ι : A →ₐ[K] Ω)
    (V : ValuationSubring Ω) (h : ∀ a, ι a ∈ V) :
    W Ω ι ∈ V ∧ ∃ (_ : Algebra K (AlgebraicClosure (ResidueField V)))
      (φ : A →ₐ[K] AlgebraicClosure (ResidueField V)),
      (∀ a, φ a = 0 ↔ (⟨ι a, h a⟩ : V) ∈ maximalIdeal V) ∧
        ∀ r, ι r = W Ω ι → W _ φ = φ r := by
  let j : A →+* V := ι.toRingHom.codRestrict V.toSubring h
  letI : Algebra K V := (j.comp (algebraMap K A)).toAlgebra
  let jA : A →ₐ[K] V := { j with commutes' := fun _ => rfl }
  let s : V →ₐ[K] Ω := { V.subtype with commutes' := fun x => ι.commutes x }
  have hs : s.comp jA = ι := by ext a; rfl
  have hcl : IsAlgClosed (FractionRing V) :=
    IsAlgClosed.of_ringEquiv Ω _ (FractionRing.algEquiv V Ω).symm.toRingEquiv
  obtain ⟨v, hv⟩ := h2 V hcl jA
  have hw : W Ω ι = v := by rw [← hs, hv]; rfl
  refine ⟨hw ▸ v.2, ?_⟩
  let ρ : V →+* AlgebraicClosure (ResidueField V) :=
    (algebraMap (ResidueField V) _).comp (residue V)
  letI alg : Algebra K (AlgebraicClosure (ResidueField V)) := (ρ.comp (algebraMap K V)).toAlgebra
  let ρA : V →ₐ[K] AlgebraicClosure (ResidueField V) := { ρ with commutes' := fun _ => rfl }
  refine ⟨alg, ρA.comp jA, fun a => ?_, fun r hr => ?_⟩
  · change algebraMap (ResidueField V) (AlgebraicClosure (ResidueField V)) (residue V ⟨ι a, h a⟩) = 0 ↔ _
    rw [map_eq_zero, residue_eq_zero_iff]
  · rw [hv]
    have : v = jA r := Subtype.ext (by rw [← hw, ← hr]; rfl)
    rw [this]; rfl

theorem exists_eq_eval (K : Type) [Field K] [CharZero K] (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra K A]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (A →ₐ[K] k) → k)
    (h1 : ∀ (k k' : Type) [Field k] [IsAlgClosed k] [Algebra K k] [Field k'] [IsAlgClosed k']
      [Algebra K k'] (φ : A →ₐ[K] k) (χ : k →ₐ[K] k'), W k' (χ.comp φ) = χ (W k φ))
    (h2 : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V],
      IsAlgClosed (FractionRing V) → ∀ ι : A →ₐ[K] V, ∃ v : V,
        ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : V →ₐ[K] k),
          W k (φ.comp ι) = φ v) :
    ∃ r : A, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : A →ₐ[K] k),
      W k φ = φ r := by
  let L := FractionRing A
  let Ω := AlgebraicClosure L
  let ι : A →ₐ[K] Ω := IsScalarTower.toAlgHom K A Ω
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsGalois L Ω := inferInstance
  have hinj : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A L Ω]
    exact (algebraMap L Ω).injective.comp (IsFractionRing.injective A L)
  obtain ⟨x, hx⟩ : W Ω ι ∈ Set.range (algebraMap L Ω) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (W Ω ι)).2 fun σ => ?_
    have e : ((σ : Ω →ₐ[L] Ω).restrictScalars K).comp ι = ι := by
      ext a
      exact ((σ : Ω →ₐ[L] Ω).restrictScalars A).commutes a
    have := h1 Ω Ω ι ((σ : Ω →ₐ[L] Ω).restrictScalars K)
    rw [e] at this
    exact this.symm
  have hint : IsIntegral A (W Ω ι) := by
    by_contra hn
    haveI : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω :=
      inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
    obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure A Ω).toSubring) (x := W Ω ι) hn
    exact hxV (valuationSubring_step K A W h2 Ω ι V
      fun a => hV ((integralClosure A Ω).algebraMap_mem a)).1
  have hint' : IsIntegral A x := by
    rw [← hx] at hint
    exact (isIntegral_algebraMap_iff (algebraMap L Ω).injective).1 hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint'
  have hrw : ι r = W Ω ι := by
    rw [← hx, ← hr]; exact IsScalarTower.algebraMap_apply A L Ω r
  refine ⟨r, fun k _ _ _ φ => ?_⟩
  let q : Ideal A := RingHom.ker φ
  haveI : q.IsPrime := RingHom.ker_isPrime φ
  let f : Localization.AtPrime q →+* Ω := IsLocalization.lift (M := q.primeCompl)
    (g := algebraMap A Ω) fun y => by
      refine isUnit_iff_ne_zero.2 fun h0 => y.2 ?_
      have : (y : A) = 0 := hinj (by rw [h0, map_zero])
      rw [this]; exact q.zero_mem
  have hf : ∀ a, f (algebraMap A _ a) = ι a := fun a => IsLocalization.lift_eq _ a
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hmem : ∀ a, ι a ∈ V := fun a => hf a ▸ hV _
  obtain ⟨-, alg, ψ, hψ, hψr⟩ := valuationSubring_step K A W h2 Ω ι V hmem
  have hψq : ∀ a, ψ a = 0 ↔ a ∈ q := fun a => by
    rw [hψ, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q a,
      mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      ← isUnit_map_iff (f.codRestrict V.toSubring hV)]
    have : f.codRestrict V.toSubring hV (algebraMap A _ a) = ⟨ι a, hmem a⟩ := Subtype.ext (hf a)
    rw [this]
  obtain ⟨χ, hχ⟩ := exists_common_factor K A q k φ fun a => Iff.rfl
  obtain ⟨χ', hχ'⟩ := exists_common_factor K A q _ ψ hψq
  have e := hψr r hrw
  rw [← hχ', h1] at e
  rw [← hχ, h1, χ'.toRingHom.injective e]
  rfl

end GlobalTheory.PointFunction
end

section
namespace GlobalTheory

theorem exists_eq_of_locally_fraction_on_generisations
    (K : Type) [Field K] (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra K R]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (R →ₐ[K] k) → k)
    (hW : ∀ (q : Ideal R) [q.IsPrime], ∃ a : Localization.AtPrime q,
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : Localization.AtPrime q →ₐ[K] k),
        W k (φ.comp (IsScalarTower.toAlgHom K R (Localization.AtPrime q))) = φ a) :
    ∃ r : R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k),
      W k φ = φ r := by
  classical
  have h1 : ∀ (q : Ideal R) [q.IsPrime], ∃ g ∉ q, ∃ a : R,
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k),
        RingHom.ker φ ≤ q → φ g * W k φ = φ a := by
    intro q _
    obtain ⟨b, hb⟩ := hW q
    obtain ⟨⟨a, g⟩, hg⟩ := IsLocalization.surj q.primeCompl b
    refine ⟨g, g.2, a, fun k _ _ _ φ hφ => ?_⟩
    have hu : ∀ y : q.primeCompl, IsUnit (φ y) := fun y =>
      IsUnit.mk0 _ fun h => y.2 (hφ h)
    let ψ : Localization.AtPrime q →ₐ[K] k := IsLocalization.liftAlgHom (M := q.primeCompl) hu
    have hψ : ∀ x : R, ψ (algebraMap R _ x) = φ x := fun x => by
      simp [ψ, IsLocalization.liftAlgHom_apply]
    have hc : ψ.comp (IsScalarTower.toAlgHom K R (Localization.AtPrime q)) = φ := by
      ext x; simpa using hψ x
    have h2 := hb k ψ
    rw [hc] at h2
    have h3 := congrArg ψ hg
    simp only [map_mul, hψ] at h3
    rw [h2, mul_comm]; exact h3
  let I : Ideal R :=
    { carrier := {g | ∃ a : R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k]
        (φ : R →ₐ[K] k), RingHom.ker φ ∈ minimalPrimes R → φ g * W k φ = φ a}
      zero_mem' := ⟨0, fun k _ _ _ φ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', fun k _ _ _ φ h => by
          rw [map_add, map_add, add_mul, ha k φ h, ha' k φ h]⟩
      smul_mem' := by
        rintro c g ⟨a, ha⟩
        exact ⟨c * a, fun k _ _ _ φ h => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, ha k φ h]⟩ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hne
    haveI := hq.isPrime
    obtain ⟨g, hg, a, ha⟩ := h1 q
    have hfin := minimalPrimes.finite_of_isNoetherianRing R
    let S : Finset (Ideal R) := hfin.toFinset.filter fun m => ¬ m ≤ q
    have hS : ¬ S.inf id ≤ q := by
      rw [Ideal.IsPrime.inf_le' inferInstance]
      rintro ⟨m, hm, hmq⟩
      exact (Finset.mem_filter.1 hm).2 hmq
    obtain ⟨h, hh, hhq⟩ := Set.not_subset.1 hS
    have hmem : h * g ∈ I := by
      refine ⟨h * a, fun k _ _ _ φ hφ => ?_⟩
      by_cases hle : RingHom.ker φ ≤ q
      · rw [map_mul, map_mul, mul_assoc, ha k φ hle]
      · have hm : RingHom.ker φ ∈ S := Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hφ, hle⟩
        have h0 : φ h = 0 := (Finset.inf_le (f := id) hm : S.inf id ≤ RingHom.ker φ) hh
        simp [h0]
    rcases hq.isPrime.mem_or_mem (hIq hmem) with h' | h'
    · exact hhq h'
    · exact hg h'
  obtain ⟨r, hr⟩ : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  refine ⟨r, fun k _ _ _ φ => ?_⟩
  haveI hp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨g, hg, a, ha⟩ := h1 (RingHom.ker φ)
  obtain ⟨m, hm, hmq⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
    (J := RingHom.ker φ) bot_le
  haveI : m.IsPrime := hm.1.1
  let k' := AlgebraicClosure (FractionRing (R ⧸ m))
  let ψ : R →ₐ[K] k' := (IsScalarTower.toAlgHom K (R ⧸ m) k').comp (Ideal.Quotient.mkₐ K m)
  have hinj : Function.Injective (algebraMap (R ⧸ m) k') := by
    rw [IsScalarTower.algebraMap_eq (R ⧸ m) (FractionRing (R ⧸ m)) k']
    exact (algebraMap (FractionRing (R ⧸ m)) k').injective.comp (IsFractionRing.injective _ _)
  have hker : RingHom.ker ψ = m := by
    ext x
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff _ hinj]
    rfl
  have e1 := hr k' ψ (by rw [hker]; exact hm)
  have e2 := ha k' ψ (by rw [hker]; exact hmq)
  have e3 : g * r - a ∈ m := by
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, ← e1, ← e2, map_one, one_mul, sub_self]
  have e4 : φ (g * r - a) = 0 := hmq e3
  have e5 := ha k φ le_rfl
  rw [map_sub, map_mul, ← e5, sub_eq_zero] at e4
  exact (mul_left_cancel₀ hg e4).symm

end GlobalTheory
end

section
open GlobalTheory.Frames

namespace GlobalTheory

theorem isIntegrallyClosed_mvPolynomial_of_finite (σ : Type) [Finite σ] (R : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed (MvPolynomial σ R) := by
  have h : ∀ n : ℕ, IsIntegrallyClosed (MvPolynomial (Fin n) R) := by
    intro n
    induction n with
    | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm
    | succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have := h n
  exact IsIntegrallyClosed.of_equiv (MvPolynomial.renameEquiv R e).symm.toRingEquiv

theorem exists_frameRing_integrallyClosed :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra K R], ∃ (A : Type) (_ : CommRing A) (_ : Algebra K A) (_ : IsDomain A) (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ), IsIntegrallyClosed A ∧ FrameRing m π X s := by
  intro K _ J _ m R _ _ _ _
  let σ := Option (Σ τ, Fin (m τ) × Fin (m τ))
  let P := MvPolynomial σ R
  let Y : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) P := fun τ => Matrix.of fun i j => MvPolynomial.X (some ⟨τ, i, j⟩)
  let d : P := MvPolynomial.X none * ∏ τ, (Y τ).det
  let A := Localization.Away d
  have hd : IsUnit (algebraMap P A d) := IsLocalization.Away.algebraMap_isUnit d
  have hs : IsUnit (algebraMap P A (MvPolynomial.X none)) := by
    exact isUnit_of_dvd_unit (map_dvd (algebraMap P A) (dvd_mul_right _ _)) hd
  have hY : ∀ τ, IsUnit (algebraMap P A (Y τ).det) := by
    intro τ
    have h0 : (Y τ).det ∣ d :=
      Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun τ => (Y τ).det) (Finset.mem_univ τ)) _
    exact isUnit_of_dvd_unit (map_dvd (algebraMap P A) h0) hd
  have hd0 : d ≠ 0 := by
    intro h0
    let w : σ → R := fun o => Option.elim o 1 (fun x => (1 : Matrix (Fin (m x.1)) (Fin (m x.1)) R) x.2.1 x.2.2)
    let ev : P →+* R := MvPolynomial.eval w
    have h1 : ∀ τ, ev.mapMatrix (Y τ) = 1 := by
      intro τ; ext i j
      simp [ev, Y, w, P]
    have h2 : ev d = 1 := by
      simp only [d, map_mul, map_prod, RingHom.map_det, h1, Matrix.det_one, Finset.prod_const_one, mul_one]
      simp [ev, w, P]
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  have hle : Submonoid.powers d ≤ nonZeroDivisors P := powers_le_nonZeroDivisors_of_noZeroDivisors hd0
  have hdom : IsDomain A := IsLocalization.isDomain_localization hle
  have hP : IsIntegrallyClosed P := isIntegrallyClosed_mvPolynomial_of_finite σ R
  have hA : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A _ hle
  refine ⟨A, inferInstance, inferInstance, hdom, IsScalarTower.toAlgHom K R A,
    fun τ => (Y τ).map (algebraMap P A), hs.unit, hA, fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩
  · have := hY τ
    rw [RingHom.map_det] at this
    exact this
  · let v : σ → T := fun o => Option.elim o (a : T) (fun x => g x.1 x.2.1 x.2.2)
    let φ : P →ₐ[K] T := MvPolynomial.aevalTower ψ v
    have hφY : ∀ τ, (Y τ).map φ = g τ := by
      intro τ; ext i j
      simp [φ, Y, v, P]
    have hφs : φ (MvPolynomial.X none) = a := by simp [φ, v, P]
    have hφd : IsUnit (φ d) := by
      simp only [d, map_mul, map_prod, hφs]
      refine a.isUnit.mul (IsUnit.prod_univ_iff.2 fun τ => ?_)
      rw [AlgHom.map_det]
      have := hg τ
      rw [← hφY τ] at this
      exact this
    let k : A →ₐ[K] T := IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := φ) (by
      rintro ⟨_, n, rfl⟩
      simpa using hφd.pow n)
    have hk : ∀ x : P, k (algebraMap P A x) = φ x := fun x => by simp [k]
    refine ⟨k, ⟨?_, fun τ => ?_, ?_⟩, ?_⟩
    · ext x
      change k (algebraMap R A x) = ψ x
      rw [IsScalarTower.algebraMap_apply R P A, hk]
      simp [φ, P]
    · rw [← hφY τ]; ext i j; simp [hk]
    · simp [hk, hφs]
    · rintro k' ⟨h1, h2, h3⟩
      have key : (k' : A →+* T).comp (algebraMap P A) = (φ : P →+* T) := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun o => ?_)
        · have := AlgHom.congr_fun h1 r
          change k' (algebraMap R A r) = ψ r at this
          rw [IsScalarTower.algebraMap_apply R P A] at this
          have h' : φ (MvPolynomial.C r) = ψ r := by simp [φ, P]
          exact this.trans h'.symm
        · rcases o with _ | ⟨τ, i, j⟩
          · exact h3.trans hφs.symm
          · have a1 := congrFun (congrFun (h2 τ) i) j
            have a2 := congrFun (congrFun (hφY τ) i) j
            exact a1.trans a2.symm
      apply AlgHom.coe_ringHom_injective
      apply IsLocalization.ringHom_ext (Submonoid.powers d)
      rw [key]
      ext x
      · exact (hk _).symm
      · exact (hk _).symm

end GlobalTheory
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FlagTan

namespace GlobalTheory.ShFam

namespace Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

section Cpt

variable (C : FlagCpt Z e)

def Fk : Type := C.Y.Fn

instance : Field (Fk C) := inferInstanceAs (Field C.Y.Fn)

instance : Algebra c.F (Fk C) := RingHom.toAlgebra (constF e C.Y : c.F →+* C.Y.Fn)

def St (y : C.Y.X) : Type := C.Y.X.presheaf.stalk y

instance (y : C.Y.X) : CommRing (St C y) := inferInstanceAs (CommRing (C.Y.X.presheaf.stalk y))

instance (y : C.Y.X) : IsLocalRing (St C y) := inferInstanceAs (IsLocalRing (C.Y.X.presheaf.stalk y))

def pt (y : C.Y.X) : Sp (St C y) ⟶ C.Y.X := stalkPt C.Y y

instance (y : C.Y.X) : Mono (pt C y) := inferInstanceAs (Mono (C.Y.X.fromSpecStalk y))

instance (y : C.Y.X) : Algebra c.F (St C y) := (Spec.preimage (pt C y ≫ C.π ≫ genStr Z)).hom.toAlgebra

theorem pt_str (y : C.Y.X) : pt C y ≫ C.π ≫ genStr Z = spMap (algebraMap c.F (St C y)) := (Spec.map_preimage _).symm

def gpt : Sp (Fk C) ⟶ C.Y.X := genericPt C.Y

def fr0 : FrPt Xo c (Fk C) := C.y0

theorem frame_point_over : GlobalTheory.AllWt.ptF (fr0 C) ≫ Z.jQ = gpt C ≫ C.π := C.y0_x

theorem str_of_over {T : Type} [CommRing T] [Algebra c.F T] {z : FrPt Xo c T} {x : Sp T ⟶ gen Z}
    (h : GlobalTheory.AllWt.ptF z ≫ Z.jQ = x) : x ≫ genStr Z = spMap (algebraMap c.F T) := by
  rw [← h, Category.assoc, Z.jQ_over, ptF_snd]

variable {C} in

def algOf {T : Type} [CommRing T] [Algebra c.F T] {y : C.Y.X} (ψ : St C y →+* T) {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (hp : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) : St C y →ₐ[c.F] T :=
  { ψ with commutes' := fun a => DFunLike.congr_fun (sp_inj (f := ψ.comp (algebraMap c.F (St C y))) (by
      rw [← sp_comp, ← pt_str, ← Category.assoc, h, hp])) a }

def toFkR (y : C.Y.X) : St C y →+* Fk C := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField

theorem toFkR_pt (y : C.Y.X) : spMap (toFkR C y) ≫ pt C y = gpt C :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

def toFk (y : C.Y.X) : St C y →ₐ[c.F] Fk C :=
  algOf (toFkR C y) (toFkR_pt C y) (by rw [← Category.assoc]; exact str_of_over (frame_point_over C))

theorem toFk_pt (y : C.Y.X) : spMap (toFk C y).toRingHom ≫ pt C y = gpt C := toFkR_pt C y

theorem toFk_injective (y : C.Y.X) : Function.Injective (toFk C y) :=
  IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField

variable {C}

theorem exists_factor {T : Type} [CommRing T] [IsLocalRing T] [Algebra c.F T] (p : Sp T ⟶ C.Y.X)
    (hp : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) :
    ∃ (y : C.Y.X) (ψ : St C y →ₐ[c.F] T), spMap ψ.toRingHom ≫ pt C y = p ∧ p (IsLocalRing.closedPoint T) = y :=
  have h : spMap (R := St C _) (Scheme.stalkClosedPointTo p).hom ≫ pt C _ = p :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk p
  ⟨_, algOf _ h hp, h, rfl⟩

theorem specializes_of {T : Type} [CommRing T] {y : C.Y.X} {ψ : St C y →+* T} {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (s : Sp T) : p s ⤳ y := by
  have : p s ∈ Set.range (C.Y.X.fromSpecStalk y) := ⟨spMap ψ s, by rw [← h]; rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

theorem hom_eq {T : Type} [CommRing T] {y : C.Y.X} {ψ ψ' : St C y →+* T} (h : spMap ψ ≫ pt C y = spMap ψ' ≫ pt C y) :
    ψ = ψ' := sp_inj ((cancel_mono _).1 h)

theorem exists_spec {y y' : C.Y.X} (h : y' ⤳ y) : ∃ sp : St C y →ₐ[c.F] St C y',
    spMap sp.toRingHom ≫ pt C y = pt C y' ∧ ∀ a, toFk C y' (sp a) = toFk C y a := by
  have k : spMap (R := St C y) (R' := St C y') (C.Y.X.presheaf.stalkSpecializes h).hom ≫ pt C y = pt C y' :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  refine ⟨algOf _ k (pt_str C y'), k, fun a => ?_⟩
  refine DFunLike.congr_fun (hom_eq (ψ := (toFk C y').toRingHom.comp (algOf _ k (pt_str C y')).toRingHom)
    (ψ' := (toFk C y).toRingHom) ?_) a
  rw [← sp_comp, Category.assoc, toFk_pt]
  exact (congrArg (_ ≫ ·) k).trans (toFk_pt C y')

theorem exists_lift_open {T : Type} [CommRing T] [IsLocalRing T] (x : Sp T ⟶ gen Z)
    (h : x (IsLocalRing.closedPoint T) ∉ genBd Z) : ∃ xF : Sp T ⟶ Xo.XF c, xF ≫ Z.jQ = x := by
  have := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨s, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint s).map x.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range
    (not_not.1 h)

theorem x_eq_of_over {T : Type} [CommRing T] [Algebra c.F T] {z z' : FrPt Xo c T}
    (h : GlobalTheory.AllWt.ptF z' ≫ Z.jQ = GlobalTheory.AllWt.ptF z ≫ Z.jQ) : z'.x = z.x := by
  have := Z.jQ_open
  rw [← ptF_fst, ← ptF_fst, (cancel_mono _).1 h]

variable (C) in

def rationalEigenFrame : EigFrame Z (algebraMap c.F (Fk C)) (gpt C ≫ C.π ≫ genι Z) := C.f0

theorem tie0 : Comparison₂ (fr0 C) (rationalEigenFrame C) := by
  have hx : GlobalTheory.AllWt.ptF (fr0 C) ≫ Z.j = gpt C ≫ C.π ≫ genι Z := by
    rw [Model.j, ← Category.assoc, frame_point_over, Category.assoc]
  exact ⟨rfl, hx, C.flagComponentFramedPoint_frame⟩

variable (C) in

structure Chart (y : C.Y.X) (P : FrPt Xo c (St C y)) (t : Ix Dw → (Fk C)ˣ) : Prop where
  ov : GlobalTheory.AllWt.ptF P ≫ Z.jQ = pt C y ≫ C.π
  bm : BM (toFk C y) t P (fr0 C)

theorem Chart.over_j {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ} (h : Chart C y P t) :
    GlobalTheory.AllWt.ptF P ≫ Z.j = pt C y ≫ C.π ≫ genι Z := by
  rw [Model.j, ← Category.assoc, h.ov, Category.assoc]

theorem pt_closedPoint (y : C.Y.X) : pt C y (IsLocalRing.closedPoint (St C y)) = y :=
  Scheme.fromSpecStalk_closedPoint

theorem Chart.notMem {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ} (h : Chart C y P t) :
    C.π y ∉ genBd Z := fun hb => hb ⟨GlobalTheory.AllWt.ptF P (IsLocalRing.closedPoint _), (congrArg (fun g => g (IsLocalRing.closedPoint (St C y))) h.ov).trans (congrArg C.π (pt_closedPoint y))⟩

theorem exists_chart {y : C.Y.X} (hy : C.π y ∉ genBd Z) :
    ∃ P t, Chart C y P t ∧ ∀ τ i, (C.gr τ i).IsEqn y (t (some ⟨τ, i⟩)) := by
  obtain ⟨φ, f, t, hf, ht⟩ := C.gr_spec y
  obtain ⟨xF, hx⟩ := exists_lift_open (pt C y ≫ C.π) fun h => hy ((congrArg C.π (pt_closedPoint y)) ▸ h)
  have hφ : (φ : c.F →+* St C y) = algebraMap c.F (St C y) := RingHom.ext fun a => toFk_injective C y
    ((DFunLike.congr_fun hf.2.1 a).symm.trans ((toFk C y).commutes a).symm)
  obtain ⟨P, hP, hT⟩ := exists_tie_point (S := St C y) (xF := xF) (x := pt C y ≫ C.π ≫ genι Z)
    (by rw [← Z.jQ_over, ← Category.assoc, hx, Category.assoc, pt_str])
    (by rw [Model.j, ← Category.assoc, hx, Category.assoc]) hφ f
  have := Z.jQ_open
  have hx0 : (fr0 C).x = spMap (toFk C y).toRingHom ≫ P.x := by
    rw [← ptF_fst, ← ptF_fst, ← Category.assoc]
    congr 1
    rw [← cancel_mono Z.jQ, frame_point_over, Category.assoc, hP, hx, ← Category.assoc, toFk_pt]
  obtain ⟨u, hu, hu'⟩ := hT.bm_of_tri tie0 hx0 (t := t) hf
  exact ⟨P, u, ⟨hP ▸ hx, hu⟩, fun τ i => (hu' τ i).symm ▸ ht τ i⟩

theorem isEqn_LEx {y : C.Y.X} {t : Ix Dw → (Fk C)ˣ} (ht : ∀ τ i, (C.gr τ i).IsEqn y (t (some ⟨τ, i⟩)))
    {ex : Ix Dw → ℤ} (hex : ex none = 0) : (C.LEx ex).IsEqn y (chi ex t)⁻¹ := by
  have key : ∀ s : Finset (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      (∑ x ∈ s, ex (some x) • C.gr x.1 x.2).IsEqn y (∏ x ∈ s, t (some x) ^ ex (some x) : (Fk C)ˣ) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => exact CartierDiv.isEqn_zero y
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact ((ht a.1 a.2).zsmul _).add ih
  have e : chi ex t = ∏ x, t (some x) ^ ex (some x) := by
    rw [chi, Fintype.prod_option, hex, zpow_zero, one_mul]
  exact (congrArg (fun u : (Fk C)ˣ => (C.LEx ex).IsEqn y u⁻¹) e).mpr (key Finset.univ).neg

theorem Chart.exists_coeff {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ}
    (h : Chart C y P t) {ex : Ix Dw → ℤ} (hex : ex none = 0) {s : Fk C} (hs : (C.LEx ex).RegularAt y s) :
    ∃ a, toFk C y a * chi ex t = s := by
  obtain ⟨P₂, t₂, h₂, ht⟩ := exists_chart h.notMem
  have ha := (isEqn_LEx ht hex).regularAt_iff.1 hs
  obtain ⟨v, -, rfl⟩ := BM.descend (toFk_injective C y) (x_eq_of_over (h.ov.trans h₂.ov.symm)) h₂.bm h.bm
  obtain ⟨a, ha'⟩ : ∃ a : St C y, toFk C y a = s * ((chi ex (t * umap (toFk C y) v))⁻¹ : (Fk C)ˣ) := ha
  refine ⟨a * (chi ex v : (St C y)ˣ), ?_⟩
  rw [map_mul, ha', ← chi_umap, mul_assoc, mul_assoc, ← Units.val_mul, ← Units.val_mul, chi_mul, mul_comm (chi ex t),
    inv_mul_cancel, Units.val_one, mul_one]

theorem Chart.move {y y' : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ} (h : Chart C y P t) (hy : y' ⤳ y) :
    ∃ (sp : St C y →ₐ[c.F] St C y') (P' : FrPt Xo c (St C y')), FrMap sp P P' ∧ Chart C y' P' t ∧
      spMap sp.toRingHom ≫ pt C y = pt C y' ∧ ∀ a, toFk C y' (sp a) = toFk C y a := by
  obtain ⟨sp, h1, h2⟩ := exists_spec hy
  obtain ⟨P', hP⟩ := exists_frMap sp P
  exact ⟨sp, P', hP, ⟨by rw [ptF_map hP.1, Category.assoc, h.ov, ← Category.assoc, h1], BM.cancel hP h.bm h2⟩, h1, h2⟩

end Cpt

section Wit

variable {C : FlagCpt Z e} {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']

variable (C) in

structure Wit (p : Sp T ⟶ C.Y.X) (z : FrPt Xo c T) : Type where
  y : C.Y.X
  ψ : St C y →ₐ[c.F] T
  P : FrPt Xo c (St C y)
  t : Ix Dw → (Fk C)ˣ
  t' : Ix Dw → Tˣ
  chart : Chart C y P t
  hp : spMap ψ.toRingHom ≫ pt C y = p
  bm : BM ψ t' P z

variable {p : Sp T ⟶ C.Y.X} {z : FrPt Xo c T}

theorem Wit.ov (w : Wit C p z) : GlobalTheory.AllWt.ptF z ≫ Z.jQ = p ≫ C.π := by
  rw [ptF_map w.bm.x_eq, Category.assoc, w.chart.ov, ← Category.assoc, w.hp]

theorem Wit.transfer [IsLocalRing T] (w : Wit C p z) {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ}
    (h : Chart C y P t) {ψ : St C y →ₐ[c.F] T} (hp : spMap ψ.toRingHom ≫ pt C y = p) :
    ∃ t', BM ψ t' P z ∧ ∀ (ex : Ix Dw → ℤ) a₁ a₂, toFk C w.y a₁ * chi ex w.t = toFk C y a₂ * chi ex t →
      chi ex w.t' * w.ψ a₁ = chi ex t' * ψ a₂ := by
  obtain ⟨y', χ, hχ, hy'⟩ := exists_factor p (by rw [← Category.assoc]; exact str_of_over w.ov)
  obtain ⟨s₁, P₁, a1, a2, a3, a4⟩ := w.chart.move (hy' ▸ specializes_of w.hp (IsLocalRing.closedPoint T) : y' ⤳ w.y)
  obtain ⟨s₂, P₂, b1, b2, b3, b4⟩ := h.move (hy' ▸ specializes_of hp (IsLocalRing.closedPoint T) : y' ⤳ y)
  have e1 : ∀ a, χ (s₁ a) = w.ψ a := fun a => DFunLike.congr_fun
    (hom_eq (ψ := χ.toRingHom.comp s₁.toRingHom) (by rw [← sp_comp, Category.assoc, a3, hχ, w.hp])) a
  have e2 : ∀ a, χ (s₂ a) = ψ a := fun a => DFunLike.congr_fun
    (hom_eq (ψ := χ.toRingHom.comp s₂.toRingHom) (by rw [← sp_comp, Category.assoc, b3, hχ, hp])) a
  obtain ⟨v, hv, ht⟩ := BM.descend (toFk_injective C _) (x_eq_of_over (a2.ov.trans b2.ov.symm)) b2.bm a2.bm
  have k1 : BM χ (w.t' * umap χ v) P₂ z := (BM.of_frBor hv).comp (BM.cancel a1 w.bm e1) fun _ => rfl
  have k2 := (BM.of_frMap b1).comp k1 e2
  have e3 : umap χ (1 : Ix Dw → (St C _)ˣ) = 1 := funext fun i => map_one _
  rw [e3, mul_one] at k2
  refine ⟨_, k2, fun ex a₁ a₂ ha => ?_⟩
  rw [ht, chi_mul, Units.val_mul, chi_umap, ← a4, ← b4] at ha
  have ha' : s₁ a₁ = s₂ a₂ * (chi ex v : (St C _)ˣ) := toFk_injective C _ (by
    rw [map_mul]
    refine (chi ex w.t).isUnit.mul_right_cancel ?_
    rw [ha]; ring)
  rw [chi_mul, Units.val_mul, chi_umap, ← e1, ← e2, ha', map_mul]
  ring

theorem carries_iff {k : Type} [Field k] {p : Sp k ⟶ C.Y.X} {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} :
    C.Carries p g ↔ ∃ (y : C.Y.X) (ψ : St C y →+* k) (φ₁ : c.F →+* St C y)
    (f : EigFrame Z φ₁ (pt C y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fk C)ˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), p = spMap ψ ≫ pt C y ∧
      f.Tri (toFk C y).toRingHom (rationalEigenFrame C) t ∧ f.Tri ψ g t' := Iff.rfl

theorem Wit.carries {k : Type} [Field k] [Algebra c.F k] {p : Sp k ⟶ C.Y.X} {z : FrPt Xo c k} (w : Wit C p z)
    {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} (hg : Comparison₂ z g) : C.Carries p g := by
  obtain ⟨f, hf⟩ := exists_tie_frame w.P w.chart.over_j
  exact carries_iff.2 ⟨w.y, w.ψ.toRingHom, _, f, _, _, w.hp.symm, hf.tri_of_bm tie0 w.chart.bm, hf.tri_of_bm hg w.bm⟩

theorem lower_of_mul {k : Type} [Field k] {n : ℕ} {A M : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, i < j → A i j = 0)
    (hd : ∀ i, A i i ≠ 0) (h : ∀ i j, i < j → (A * M) i j = 0) : ∀ i j, i < j → M i j = 0 := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro j hij
    have := h i j hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun m _ hm => ?_) (by simp)] at this
    · exact (mul_eq_zero.1 this).resolve_left (hd i)
    · rcases lt_or_gt_of_ne hm with h1 | h1
      · rw [ih m h1 j (h1.trans hij), mul_zero]
      · rw [hA i m h1, zero_mul]

theorem lower_mul {k : Type} [CommRing k] {n : ℕ} {A M : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, i < j → A i j = 0)
    (hM : ∀ i j, i < j → M i j = 0) (i j : Fin n) (hij : i < j) : (A * M) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases le_or_gt m i with h | h
  · rw [hM m j (h.trans_lt hij), mul_zero]
  · rw [hA i m h, zero_mul]

theorem dual_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem dual_eps {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    spMap (dualMap f) ≫ spMap (epsMul a) = spMap (epsMul (f a)) ≫ spMap (dualMap f) := by
  rw [sp_comp, sp_comp]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap, epsMul, mul_comm]

theorem wit_of_carries {k : Type} [Field k] [Algebra c.F k] {p : Sp k ⟶ C.Y.X} {z : FrPt Xo c k}
    (hp : GlobalTheory.AllWt.ptF z ≫ Z.jQ = p ≫ C.π) {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} (hg : Comparison₂ z g)
    (h : C.Carries p g) : Nonempty (Wit C p z) := by
  obtain ⟨y, ψ, φ₁, f, t, t', e0, h1, h2⟩ := carries_iff.1 h
  obtain rfl : φ₁ = algebraMap c.F (St C y) := RingHom.ext fun a => toFk_injective C y
    ((DFunLike.congr_fun h1.2.1 a).symm.trans ((toFk C y).commutes a).symm)
  obtain ⟨y', χ, hχ, hy'⟩ := exists_factor p (by rw [← Category.assoc]; exact str_of_over hp)
  obtain ⟨sp, s1, s2⟩ := exists_spec (hy' ▸ specializes_of e0.symm (IsLocalRing.closedPoint k) : y' ⤳ y)
  obtain ⟨P, u, hC, -⟩ := exists_chart (C := C) (y := y') fun hb =>
    hb ⟨GlobalTheory.AllWt.ptF z (IsLocalRing.closedPoint k),
      (congrArg (fun g => g (IsLocalRing.closedPoint k)) hp).trans (congrArg C.π hy')⟩
  obtain ⟨f', hf'⟩ := exists_tie_frame P hC.over_j
  have e1 : χ.toRingHom.comp sp.toRingHom = ψ := hom_eq (by rw [← sp_comp, Category.assoc, s1, hχ, e0])
  have e2 : (toFk C y').toRingHom.comp sp.toRingHom = (toFk C y).toRingHom := RingHom.ext s2
  have hM : ∀ τ i, ∃ a, IsCombAtG Z.t (pt C y' ≫ C.π ≫ genι Z) (f'.v τ) a
      (spMap (dualMap sp.toRingHom) ≫ f.v τ i) := fun τ i => by
    refine (f'.basis τ _ ?_ fun a => ?_).exists
    · have := GlobalTheory.FactorDepth.isTanAtG_map Z.t sp.toRingHom (f.tan τ i)
      rwa [← Category.assoc, s1] at this
    · have e3 : sp.toRingHom (algebraMap c.F (St C y) (embK c τ a)) = algebraMap c.F (St C y') (embK c τ a) :=
        sp.commutes _
      rw [Category.assoc, f.eig, ← Category.assoc, dual_eps, Category.assoc, e3]
  choose M hM using hM
  choose A A1 A2 A3 using h1.2.2
  choose B B1 B2 B3 using h2.2.2
  obtain ⟨P', p1, p2⟩ := hC.bm
  have low : ∀ τ i j, i < j → M τ i j = 0 := fun τ i j hij => by
    have key := lower_of_mul (A := A τ) (M := Matrix.map (M τ) (toFk C y')) (A2 τ)
      (fun i => by rw [A1]; exact Units.ne_zero _) (fun i j hij => ?_) i j hij
    · exact toFk_injective C _ (key.trans (map_zero _).symm)
    · obtain ⟨cf, -, c2, c3⟩ := p2.2.1 τ i
      have c4 := hf'.comb tie0 p1 p2.1 τ (M := M τ) (N := A τ) (hM τ) (fun i => by
        simp only [← Category.assoc, dual_comp, e2]
        exact A3 τ i) i
      rw [(P'.basis τ _ (p2.1 ▸ (fr0 C).tan τ i) ((fr0 C).eig τ i)).unique c4 c3]
      exact c2 j hij
  obtain ⟨Q, hQ⟩ := exists_frMap χ P
  have hx : z.x = Q.x := x_eq_of_over (by
    rw [hp, ptF_map hQ.1, Category.assoc, hC.ov, ← Category.assoc, hχ])
  obtain ⟨v, hv, -⟩ := exists_frBor hx (fun τ => Matrix.of (B τ) * Matrix.map (M τ) χ)
    (fun τ => lower_mul (B2 τ) fun i j hij => (congrArg χ (low τ i j hij)).trans (map_zero _))
    fun τ i => hf'.comb hg hQ hx τ (M := M τ) (N := B τ) (hM τ) (fun i => by
      simp only [← Category.assoc, dual_comp, e1]
      exact B3 τ i) i
  exact ⟨⟨_, χ, P, u, v, hC, hχ, Q, hQ, hv⟩⟩

theorem Wit.extend {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    [Algebra c.F V] [Algebra c.F K] [IsScalarTower c.F V K] {p : Sp K ⟶ C.Y.X} {z : FrPt Xo c V} {zK : FrPt Xo c K}
    (w : Wit C p zK) (hz : FrMap (IsScalarTower.toAlgHom c.F V K) z zK) : ∃ q, Nonempty (Wit C q z) := by
  have : IsProper Z.s := by
    obtain ⟨N, i, _, hi⟩ := Z.proj
    have := isProper_str O N
    rw [← hi]; infer_instance
  have : IsIso (spMap e.toRingHom) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
    infer_instance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  have hv : ValuativeCriterion.Existence C.π := by
    have h : UniversallyClosed C.π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have sq : p ≫ C.π = spMap (algebraMap V K) ≫ GlobalTheory.AllWt.ptF z ≫ Z.jQ := by
    rw [← w.ov, ptF_map hz.1, Category.assoc]; rfl
  obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨V, K, p, GlobalTheory.AllWt.ptF z ≫ Z.jQ, ⟨sq⟩⟩).exists_lift
  change Sp V ⟶ C.Y.X at q
  change spMap (algebraMap V K) ≫ q = p at q1
  change q ≫ C.π = GlobalTheory.AllWt.ptF z ≫ Z.jQ at q2
  obtain ⟨y', χ, hχ, hy'⟩ := exists_factor q (by rw [← Category.assoc]; exact str_of_over q2.symm)
  obtain ⟨P, u, hC, -⟩ := exists_chart (C := C) (y := y') fun hb =>
    hb ⟨GlobalTheory.AllWt.ptF z (IsLocalRing.closedPoint V),
      (congrArg (fun g => g (IsLocalRing.closedPoint V)) q2.symm).trans (congrArg C.π hy')⟩
  obtain ⟨t', ht', -⟩ := w.transfer hC (ψ := (IsScalarTower.toAlgHom c.F V K).comp χ) (by
    rw [← q1, ← hχ, ← Category.assoc, sp_comp]; rfl)
  obtain ⟨Q, hQ⟩ := exists_frMap χ P
  have hx : z.x = Q.x := x_eq_of_over (by
    rw [← q2, ptF_map hQ.1, Category.assoc, hC.ov, ← Category.assoc, hχ])
  obtain ⟨v, hv, -⟩ := BM.descend (IsFractionRing.injective V K) hx (BM.cancel hQ ht' fun _ => rfl) (BM.of_frMap hz)
  exact ⟨q, ⟨⟨_, χ, P, u, v, hC, hχ, Q, hQ, hv⟩⟩⟩

end Wit

section Global

variable {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (ex : Ix Dw → ℤ)
  (s : ∀ k, Fk (Φ.C k)) {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']

def Val (z : FrPt Xo c T) (v : T) : Prop :=
  ∃ (i : U.Comp) (p : Sp T ⟶ (Φ.C i).Y.X) (w : Wit (Φ.C i) p z) (a : St (Φ.C i) w.y),
    toFk _ w.y a * chi ex w.t = s i ∧ v = chi ex w.t' * w.ψ a

def Rep (P : FrPt Xo c T) (r : T) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (φ : T →ₐ[c.F] k) (z : FrPt Xo c k), FrMap φ P z →
    Val Φ ex s z (φ r)

variable {Φ ex s}

theorem Val.comp {z : FrPt Xo c T} {v : T} (h : Val Φ ex s z v) {χ : T →ₐ[c.F] T'} {u : Ix Dw → T'ˣ}
    {z' : FrPt Xo c T'} (hz : BM χ u z z') : Val Φ ex s z' (chi ex u * χ v) := by
  obtain ⟨i, p, w, a, h1, rfl⟩ := h
  refine ⟨i, _, ⟨w.y, χ.comp w.ψ, w.P, w.t, _, w.chart, rfl, w.bm.comp hz fun _ => rfl⟩, a, h1, ?_⟩
  show _ = (chi ex (u * umap χ w.t') : T') * χ (w.ψ a)
  rw [chi_mul, Units.val_mul, chi_umap, map_mul, mul_assoc]

theorem Val.map {z : FrPt Xo c T} {v : T} (h : Val Φ ex s z v) {χ : T →ₐ[c.F] T'}
    {z' : FrPt Xo c T'} (hz : FrMap χ z z') : Val Φ ex s z' (χ v) := by
  simpa [chi_one] using h.comp (BM.of_frMap hz)

theorem lift_frame {k : Type} [Field k] [Algebra c.F k] (z : FrPt Xo c k) :
    ∃ g : EigFrame Z (algebraMap c.F k) ((GlobalTheory.AllWt.ptF z ≫ Z.jQ) ≫ genι Z), Comparison₂ z g :=
  exists_tie_frame z (by rw [Model.j, Category.assoc])

theorem Val.unique {k : Type} [Field k] [IsAlgClosed k] [Algebra c.F k] {z : FrPt Xo c k} {v v' : k}
    (h : Val Φ ex s z v) (h' : Val Φ ex s z v') : v = v' := by
  obtain ⟨i, p, w, a, h1, rfl⟩ := h
  obtain ⟨i', p', w', a', h1', rfl⟩ := h'
  obtain ⟨g, hg⟩ := lift_frame (Z := Z) z
  have e0 : (⟨i, p⟩ : Σ i : U.Comp, (Sp k ⟶ (Φ.C i).Y.X)) = ⟨i', p'⟩ :=
    (Φ.lifts k _ _ (str_of_over rfl) g).unique ⟨w.ov.symm, w.carries hg⟩ ⟨w'.ov.symm, w'.carries hg⟩
  cases e0
  obtain ⟨t', k1, k2⟩ := w.transfer w'.chart w'.hp
  rw [k2 ex a a' (h1.trans h1'.symm), k1.unique w'.bm]

theorem exists_wit {k : Type} [Field k] [IsAlgClosed k] [Algebra c.F k] (z : FrPt Xo c k) :
    ∃ i p, Nonempty (Wit (Φ.C i) p z) := by
  obtain ⟨g, hg⟩ := lift_frame (Z := Z) z
  obtain ⟨⟨i, p⟩, ⟨h1, h2⟩, -⟩ := Φ.lifts k _ _ (str_of_over rfl) g
  exact ⟨i, p, wit_of_carries h1.symm hg h2⟩

theorem Rep.map {P : FrPt Xo c T} {r : T} (h : Rep Φ ex s P r) {χ : T →ₐ[c.F] T'} {Q : FrPt Xo c T'}
    (hQ : FrMap χ P Q) : Rep Φ ex s Q (χ r) := fun k _ _ _ φ z hz =>
  h k (φ.comp χ) z (frMap_comp hQ hz fun _ => rfl)

theorem Rep.unique [IsReduced T] {P : FrPt Xo c T} {r r' : T} (h : Rep Φ ex s P r) (h' : Rep Φ ex s P r') : r = r' := by
  refine sub_eq_zero.1 (GeometricValues.eq_zero_of_forall_algClosed (K := c.F) _ fun k _ _ _ φ => ?_)
  obtain ⟨z, hz⟩ := exists_frMap φ P
  rw [map_sub, (h k φ z hz).unique (h' k φ z hz), sub_self]

theorem Val.rep {P : FrPt Xo c T} {r : T} (h : Val Φ ex s P r) : Rep Φ ex s P r := fun _ _ _ _ _ _ hz => h.map hz

theorem Rep.bor {P Q : FrPt Xo c T} {r : T} (h : Rep Φ ex s P r) {t : Ix Dw → Tˣ} (hb : FrBor t P Q) :
    Rep Φ ex s Q (chi ex t * r) := fun k _ _ _ φ z hz => by
  obtain ⟨P', hP⟩ := exists_frMap φ P
  have := (h k φ P' hP).comp (BM.of_frBor (frBor_map hb hP hz))
  rwa [chi_umap, AlgHom.id_apply, ← map_mul] at this

variable (hex : ex none = 0)
  (hs : ∀ k (y : (Φ.C k).Y.X), (Φ.C k).π y ∉ genBd Z → ((Φ.C k).LEx ex).RegularAt y (s k))

include hex hs

theorem Wit.exists_val {i : U.Comp} {p : Sp T ⟶ (Φ.C i).Y.X} {z : FrPt Xo c T} (w : Wit (Φ.C i) p z) :
    ∃ v, Val Φ ex s z v := by
  obtain ⟨a, ha⟩ := w.chart.exists_coeff hex (hs i _ w.chart.notMem)
  exact ⟨_, i, p, w, a, ha, rfl⟩

theorem exists_values (P : FrPt Xo c T) :
    ∃ W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k], (T →ₐ[c.F] k) → k,
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (φ : T →ₐ[c.F] k) (z : FrPt Xo c k), FrMap φ P z →
        Val Φ ex s z (W k φ) := by
  have : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (φ : T →ₐ[c.F] k), ∃ v : k, ∀ z : FrPt Xo c k,
      FrMap φ P z → Val Φ ex s z v := fun k _ _ _ φ => by
    obtain ⟨z, hz⟩ := exists_frMap φ P
    obtain ⟨i, p, ⟨w⟩⟩ := exists_wit (Φ := Φ) z
    obtain ⟨v, hv⟩ := w.exists_val hex hs
    exact ⟨v, fun z' hz' => frMap_unique hz hz' ▸ hv⟩
  exact ⟨fun k _ _ _ φ => (this k φ).choose, fun k _ _ _ φ => (this k φ).choose_spec⟩

theorem exists_rep_valuationRing {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Algebra c.F V]
    (hV : IsAlgClosed (FractionRing V)) (P : FrPt Xo c V) : ∃ r, Rep Φ ex s P r := by
  obtain ⟨z, hz⟩ := exists_frMap (IsScalarTower.toAlgHom c.F V (FractionRing V)) P
  obtain ⟨i, p, ⟨w⟩⟩ := exists_wit (Φ := Φ) z
  obtain ⟨q, ⟨w'⟩⟩ := w.extend hz
  obtain ⟨v, hv⟩ := w'.exists_val hex hs
  exact ⟨v, hv.rep⟩

theorem exists_rep_normal [IsDomain T] [IsIntegrallyClosed T] (P : FrPt Xo c T) : ∃ r, Rep Φ ex s P r := by
  obtain ⟨W, hW⟩ := exists_values hex hs P
  obtain ⟨r, hr⟩ := GlobalTheory.PointFunction.exists_eq_eval c.F T W (fun k k' _ _ _ _ _ _ φ χ => by
    obtain ⟨z, hz⟩ := exists_frMap φ P
    obtain ⟨z', hz'⟩ := exists_frMap χ z
    exact (hW k' _ z' (frMap_comp hz hz' fun _ => rfl)).unique ((hW k φ z hz).map hz')) (fun V _ _ _ _ hV ι => by
    obtain ⟨Q, hQ⟩ := exists_frMap ι P
    obtain ⟨v, hv⟩ := exists_rep_valuationRing hex hs hV Q
    refine ⟨v, fun k _ _ _ φ => ?_⟩
    obtain ⟨z, hz⟩ := exists_frMap φ Q
    exact (hW k _ z (frMap_comp hQ hz fun _ => rfl)).unique (hv k φ z hz))
  exact ⟨r, fun k _ _ _ φ z hz => hr k φ ▸ hW k φ z hz⟩

theorem exists_rep_local [IsLocalRing T] (P : FrPt Xo c T) : ∃ r, Rep Φ ex s P r := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have hn := (GlobalTheory.isNormalScheme_iff _).1 (GlobalTheory.isNormalScheme_of_smooth (S := Spec (.of c.F))
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)))
  obtain ⟨B, _, _, _, _, j, ψ, hj⟩ : ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsDomain B)
      (_ : IsIntegrallyClosed B) (j : Sp B ⟶ Xo.XF c) (ψ : B →+* T), spMap ψ ≫ j = GlobalTheory.AllWt.ptF P :=
    ⟨(Xo.XF c).presheaf.stalk (GlobalTheory.AllWt.ptF P (IsLocalRing.closedPoint T)), inferInstance, inferInstance, (hn _).1,
      (hn _).2, (Xo.XF c).fromSpecStalk _, (Scheme.stalkClosedPointTo (GlobalTheory.AllWt.ptF P)).hom,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk _⟩
  letI : Algebra c.F B := (Spec.preimage (j ≫ pullback.snd _ _)).hom.toAlgebra
  have hB : j ≫ pullback.snd _ _ = spMap (algebraMap c.F B) := (Spec.map_preimage _).symm
  let ψ' : B →ₐ[c.F] T := { ψ with commutes' := fun a => DFunLike.congr_fun (sp_inj (f := ψ.comp (algebraMap c.F B)) (by
      rw [← sp_comp, ← hB, ← Category.assoc, hj, ptF_snd])) a }
  obtain ⟨y₀, hy₀⟩ := exists_frPt (c := c) (j ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hB, sp_comp]; rfl)
  obtain ⟨A, _, _, _, π, X, u, _, hA⟩ := GlobalTheory.exists_frameRing_integrallyClosed c.F (E →+* ℂ) (fun τ => Dw.mult τ) B
  obtain ⟨u₀, hu₀⟩ := exists_frMap π y₀
  obtain ⟨Q, hQ, -⟩ := existsUnique_frChg E H Dw l Xo c A u₀ X u hA.1
  obtain ⟨a, ⟨-, ha⟩, -⟩ := univFrame_classifies GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c B A y₀ π X u Q
    ⟨hA, u₀, hu₀, hQ⟩ T P ψ' (by rw [hy₀, ← ptF_fst, ← hj, Category.assoc])
  obtain ⟨r, hr⟩ := exists_rep_normal hex hs Q
  exact ⟨_, hr.map ha⟩

theorem exists_rep [IsNoetherianRing T] (P : FrPt Xo c T) : ∃ r, Rep Φ ex s P r := by
  obtain ⟨W, hW⟩ := exists_values hex hs P
  obtain ⟨r, hr⟩ := GlobalTheory.exists_eq_of_locally_fraction_on_generisations c.F T W fun q _ => by
    obtain ⟨Q, hQ⟩ := exists_frMap (IsScalarTower.toAlgHom c.F T (Localization.AtPrime q)) P
    obtain ⟨v, hv⟩ := exists_rep_local hex hs Q
    refine ⟨v, fun k _ _ _ φ => ?_⟩
    obtain ⟨z, hz⟩ := exists_frMap φ Q
    exact (hW k _ z (frMap_comp hQ hz fun _ => rfl)).unique (hv k φ z hz)
  exact ⟨r, fun k _ _ _ φ z hz => hr k φ ▸ hW k φ z hz⟩

theorem val_frame_zero (i : U.Comp) : Val Φ ex s (fr0 (Φ.C i)) (s i) := by
  obtain ⟨y, χ, hχ, hy⟩ := exists_factor (gpt (Φ.C i)) (by rw [← Category.assoc]; exact str_of_over (frame_point_over _))
  obtain ⟨P, t, hC, -⟩ := exists_chart (C := Φ.C i) (y := y) fun hb =>
    hb ⟨GlobalTheory.AllWt.ptF (fr0 (Φ.C i)) (IsLocalRing.closedPoint (Fk (Φ.C i))),
      (congrArg (fun g => g (IsLocalRing.closedPoint (Fk (Φ.C i)))) (frame_point_over _)).trans (congrArg (Φ.C i).π hy)⟩
  obtain ⟨a, ha⟩ := hC.exists_coeff hex (hs i _ hC.notMem)
  exact ⟨i, _, ⟨y, toFk _ y, P, t, t, hC, rfl, hC.bm⟩, a, ha, ha.symm.trans (mul_comm _ _)⟩

omit hex hs in
theorem rep_of_mem {f : Rul Xo c} (hf : f ∈ secZ Xo c ex) (hv : ∀ i, evR Xo c f (fr0 (Φ.C i)) = s i) (p : TRing c.F)
    (P : FrPt Xo c p.R) : Rep Φ ex s P (f p P) := fun k _ _ _ φ z hz => by
  obtain ⟨i, q, ⟨w⟩⟩ := exists_wit (Φ := Φ) z
  refine ⟨i, q, w, evR Xo c f w.P, ?_, ?_⟩
  · rw [← hv, w.chart.bm.evR hf, mul_comm]
  · rw [← w.bm.evR hf, evR_eq hf.1 hz]

theorem existsUnique_rule : ∃! f : Rul Xo c, f ∈ secZ Xo c ex ∧ ∀ i, evR Xo c f (fr0 (Φ.C i)) = s i := by
  have red : ∀ p : TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  choose f hf using fun (p : TRing c.F) (P : FrPt Xo c p.R) => exists_rep hex hs P
  have hm : f ∈ secZ Xo c ex := ⟨fun p q φ y z h => (hf q z).unique ((hf p y).map h),
    fun p t y y' h => (hf p y').unique ((hf p y).bor h)⟩
  refine ⟨f, ⟨hm, fun i => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨p, φ, y, hy⟩ := fromTest_of_isLocalRing (fr0 (Φ.C i))
    rw [evR_eq hm.1 hy]
    exact ((hf p y).map hy).unique (val_frame_zero hex hs i).rep
  · funext p P
    exact (rep_of_mem hg.1 hg.2 p P).unique (hf p P)

end Global

end Descent

theorem existsUnique_rule_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (ex : Ix Dw → ℤ), ex none = 0 → ∀ s : ∀ k, (Φ.C k).Y.Fn, (∀ k (y : (Φ.C k).Y.X), (Φ.C k).π y ∉ genBd Z → ((Φ.C k).LEx ex).RegularAt y (s k)) → ∃! f : Rul Xo c, f ∈ GlobalTheory.AllWt.secZ Xo c ex ∧ ∀ k, (Φ.C k).val f = s k := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ ex hex s hs
  exact Descent.existsUnique_rule (s := s) hex hs

end GlobalTheory.ShFam
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.Vanish

open GlobalTheory.ShFam.Descent GlobalTheory.FlagTan GlobalTheory.AllWt GlobalTheory.Cartier

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

def FrameBC (Z : Model Xo c β) : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X)
    (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x),
      ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i

theorem FrameBC.at (hbc : FrameBC Z) {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') {x' : Sp R' ⟶ Z.X}
    (hx : x' = spMap ψ ≫ x) : ∃ g : EigFrame Z (ψ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  subst hx
  exact hbc R R' φ x f ψ

section Cpt

variable {C : FlagCpt Z e}

theorem exists_extension {A k : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k]
    [IsFractionRing A k] (p : Sp k ⟶ C.Y.X) (xA : Sp A ⟶ gen Z) (h : p ≫ C.π = spMap (algebraMap A k) ≫ xA) :
    ∃ q : Sp A ⟶ C.Y.X, spMap (algebraMap A k) ≫ q = p ∧ q ≫ C.π = xA := by
  have : IsProper Z.s := by
    obtain ⟨N, i, _, hi⟩ := Z.proj
    have := isProper_str O N
    rw [← hi]; infer_instance
  have : IsIso (spMap e.toRingHom) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
    infer_instance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  have hv : ValuativeCriterion.Existence C.π := by
    have h : UniversallyClosed C.π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨A, k, p, xA, ⟨h⟩⟩).exists_lift
  exact ⟨q, q1, q2⟩

theorem exists_local_factor {T : Type} [CommRing T] [IsLocalRing T] [Algebra c.F T] (q : Sp T ⟶ C.Y.X)
    (hq : q ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) :
    ∃ (y : C.Y.X) (ψ : St C y →ₐ[c.F] T), IsLocalHom ψ.toRingHom ∧ spMap ψ.toRingHom ≫ pt C y = q ∧
      q (IsLocalRing.closedPoint T) = y :=
  have h : spMap (R := St C _) (Scheme.stalkClosedPointTo q).hom ≫ pt C _ = q :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk q
  ⟨_, algOf _ h hq, inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo q).hom), h, rfl⟩

theorem exists_zero_coeff {y : C.Y.X} {t : Ix Dw → (Fk C)ˣ} (ht : ∀ τ i, (C.gr τ i).IsEqn y (t (some ⟨τ, i⟩)))
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {s : Fk C} (hs : (C.LEx ex).VanishesAt y s) :
    ∃ a ∈ IsLocalRing.maximalIdeal (St C y), toFk C y a * Descent.chi ex t = s := by
  obtain ⟨a, ha, h⟩ := (isEqn_LEx ht hex).vanishesAt_iff.1 hs
  refine ⟨a, ha, ?_⟩
  have h' : toFk C y a = s * ((Descent.chi ex t)⁻¹ : (Fk C)ˣ) := h
  rw [h', mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end Cpt

theorem chi_congr {A : Type} [CommRing A] {ex : Ix Dw → ℤ} (hex : ex none = 0) {t u : Ix Dw → Aˣ}
    (h : ∀ x, t (some x) = u (some x)) : Descent.chi ex t = Descent.chi ex u := by
  simp only [Descent.chi, Fintype.prod_option, hex, zpow_zero, one_mul, h]

section Core

theorem exists_mem_of_wit (hbc : FrameBC Z) {C : FlagCpt Z e} {A k : Type} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field k] [Algebra A k] [IsFractionRing A k] [Algebra c.F A] [Algebra c.F k] [IsScalarTower c.F A k]
    (xA : Sp A ⟶ gen Z) (hxA : xA ≫ genStr Z = spMap (algebraMap c.F A))
    (gA : EigFrame Z (algebraMap c.F A) (xA ≫ genι Z)) (z : FrPt Xo c k) {φk : c.F →+* k} {xk : Sp k ⟶ Z.X}
    (gk : EigFrame Z φk xk) (hxk : xk = spMap (algebraMap A k) ≫ xA ≫ genι Z) (hφk : φk = algebraMap c.F k)
    (hgk : ∀ τ i, gk.v τ i = spMap (dualMap (algebraMap A k)) ≫ gA.v τ i) (hTz : Comparison₂ z gk) (p : Sp k ⟶ C.Y.X)
    (hp : p ≫ C.π = spMap (algebraMap A k) ≫ xA) (w : Descent.Wit C p z)
    (hbd : xA (IsLocalRing.closedPoint A) ∈ genBd Z) {ex : Ix Dw → ℤ} (hex : ex none = 0) {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) (hv : C.Y.vanishOn (C.LEx ex) (C.val f) C.Ybd) :
    ∃ b ∈ IsLocalRing.maximalIdeal A, evR Xo c f z = algebraMap A k b := by
  obtain ⟨q, q1, q2⟩ := exists_extension p xA hp
  obtain ⟨y₀, ψ₀, hloc, hψ₀, hy₀⟩ := exists_local_factor q (by rw [← Category.assoc, q2, hxA])
  have hmem : y₀ ∈ C.Ybd := by
    have h1 : C.π y₀ ∈ genBd Z := by
      have e0 : C.π (q (IsLocalRing.closedPoint A)) = xA (IsLocalRing.closedPoint A) :=
        congrArg (fun g => g (IsLocalRing.closedPoint A)) q2
      rw [← hy₀, e0]; exact hbd
    exact (C.bd_supp y₀).2 h1
  obtain ⟨φ₀, f₀, t₀, hT, ht⟩ := C.gr_spec y₀
  obtain rfl : φ₀ = algebraMap c.F (St C y₀) := RingHom.ext fun a => toFk_injective C y₀
    ((DFunLike.congr_fun hT.2.1 a).symm.trans ((toFk C y₀).commutes a).symm)
  let T₀ : Ix Dw → (Fk C)ˣ := fun j => j.elim 1 fun x => t₀ x.1 x.2
  obtain ⟨a, ha, ha'⟩ := exists_zero_coeff (t := T₀) ht hex (hv y₀ hmem)
  have hpstr : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F k) := by
    rw [← Category.assoc]; exact str_of_over w.ov
  obtain ⟨y₂, χ₂, hχ₂, hy₂⟩ := exists_factor p hpstr
  have hspec : y₂ ⤳ y₀ := hy₂ ▸ specializes_of (ψ := (algebraMap A k).comp ψ₀.toRingHom) (p := p)
    (by rw [← sp_comp, Category.assoc, hψ₀, q1]) (IsLocalRing.closedPoint k)
  obtain ⟨sp, s1, s2⟩ := exists_spec hspec
  have e1 : χ₂.toRingHom.comp sp.toRingHom = (algebraMap A k).comp ψ₀.toRingHom := hom_eq (by
    rw [← sp_comp, ← sp_comp, Category.assoc, Category.assoc, s1, hχ₂, hψ₀, q1])
  obtain ⟨f₂, hf₂⟩ := hbc.at (x := pt C y₀ ≫ C.π ≫ genι Z) f₀ sp.toRingHom (x' := pt C y₂ ≫ C.π ≫ genι Z)
    (by rw [← s1, Category.assoc])
  have hy₂b : C.π y₂ ∉ genBd Z := fun hb => hb ⟨GlobalTheory.AllWt.ptF z (IsLocalRing.closedPoint k),
    (congrArg (fun g => g (IsLocalRing.closedPoint k)) w.ov).trans (congrArg C.π hy₂)⟩
  obtain ⟨xF, hxF⟩ := exists_lift_open (pt C y₂ ≫ C.π) fun h => hy₂b ((congrArg C.π (pt_closedPoint y₂)) ▸ h)
  have hφ₂ : sp.toRingHom.comp (algebraMap c.F (St C y₀)) = algebraMap c.F (St C y₂) := sp.comp_algebraMap
  obtain ⟨P, hP, hTP⟩ := exists_tie_point (S := St C y₂) (xF := xF) (x := pt C y₂ ≫ C.π ≫ genι Z)
    (by rw [← Z.jQ_over, ← Category.assoc, hxF, Category.assoc, pt_str])
    (by rw [Model.j, ← Category.assoc, hxF, Category.assoc]) hφ₂ f₂
  have := Z.jQ_open
  have hx0 : (fr0 C).x = spMap (toFk C y₂).toRingHom ≫ P.x := by
    rw [← ptF_fst, ← ptF_fst, ← Category.assoc]
    congr 1
    rw [← cancel_mono Z.jQ, frame_point_over, Category.assoc, hP, hxF, ← Category.assoc, toFk_pt]
  have e2 : (toFk C y₂).toRingHom.comp sp.toRingHom = (toFk C y₀).toRingHom := RingHom.ext s2
  have hTf : f₂.Tri (toFk C y₂).toRingHom (rationalEigenFrame C) t₀ := by
    refine ⟨?_, ?_, fun τ i => ?_⟩
    · show gpt C ≫ C.π ≫ genι Z = _
      rw [← toFk_pt C y₂, Category.assoc]
    · rw [← RingHom.comp_assoc, e2]; exact hT.2.1
    · obtain ⟨cf, c1, c2, c3⟩ := hT.2.2 τ i
      refine ⟨cf, c1, c2, ?_⟩
      have e : ∀ j, spMap (dualMap (toFk C y₂).toRingHom) ≫ f₂.v τ j = spMap (dualMap (toFk C y₀).toRingHom) ≫ f₀.v τ j :=
        fun j => by rw [hf₂, ← Category.assoc, dual_comp, e2]
      simp only [e]
      exact c3
  obtain ⟨u, hu1, hu2⟩ := hTP.bm_of_tri tie0 hx0 hTf
  have hC : Chart C y₂ P u := ⟨by rw [hP, hxF], hu1⟩
  obtain ⟨t', hb, -⟩ := w.transfer hC hχ₂
  have v1 := hb.evR hf
  have v2 := hu1.evR hf
  have hchi : Descent.chi ex u = Descent.chi ex T₀ := chi_congr hex fun x => hu2 x.1 x.2
  have hval : sp a = evR Xo c f P := toFk_injective C y₂ (by
    refine (Descent.chi ex T₀).isUnit.mul_left_cancel ?_
    rw [s2, mul_comm, ha', ← hchi]
    exact v2)
  obtain ⟨fA, hfA⟩ := hbc.at (x := pt C y₀ ≫ C.π ≫ genι Z) f₀ ψ₀.toRingHom (x' := xA ≫ genι Z)
    (by rw [← q2, ← hψ₀]; simp only [Category.assoc])
  have hT1 := hTP.tri_of_bm hTz hb
  have hF : fA.Tri (algebraMap A k) gk (fun τ i => t' (some ⟨τ, i⟩)) := by
    refine ⟨hxk, ?_, fun τ i => ?_⟩
    · have h3 : ψ₀.toRingHom.comp (algebraMap c.F (St C y₀)) = algebraMap c.F A := ψ₀.comp_algebraMap
      show φk = (algebraMap A k).comp (ψ₀.toRingHom.comp (algebraMap c.F (St C y₀)))
      rw [hφk, h3]; exact IsScalarTower.algebraMap_eq _ _ _
    · obtain ⟨cf, c1, c2, c3⟩ := hT1.2.2 τ i
      refine ⟨cf, c1, c2, ?_⟩
      have e : ∀ j, spMap (dualMap (algebraMap A k)) ≫ fA.v τ j = spMap (dualMap χ₂.toRingHom) ≫ f₂.v τ j :=
        fun j => by
          rw [hfA, hf₂, ← Category.assoc (spMap (dualMap (algebraMap A k))),
            ← Category.assoc (spMap (dualMap χ₂.toRingHom)), dual_comp, dual_comp, e1]
      simp only [e]
      exact c3
  have hG : gA.Tri (algebraMap A k) gk 1 := by
    refine ⟨hxk, ?_, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩⟩
    · rw [hφk]; exact IsScalarTower.algebraMap_eq _ _ _
    · have e : (fun j => spMap (dualMap (algebraMap A k)) ≫ gA.v τ j) = gk.v τ := funext fun j => (hgk τ j).symm
      rw [e]
      exact isCombAtG_single Z.t _ (gk.tan τ) i
  obtain ⟨uu, huu⟩ := CoordUniq.exists_unit_ratio fA gA (IsFractionRing.injective A k) hF hG
  have hu' := huu (algebraMap A k) gk _ _ hF hG
  let W : Aˣ := ∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), uu x.1 x.2 ^ ex (some x)
  have hW : (Descent.chi ex t' : k) = algebraMap A k (W : A) := by
    have : Descent.chi ex t' = Units.map (algebraMap A k : A →* k) W := by
      simp only [Descent.chi, Fintype.prod_option, hex, zpow_zero, one_mul, W, map_prod, map_zpow]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [show t' (some x) = _ from hu' x.1 x.2]
      simp
    rw [this]; rfl
  have hψa : ψ₀ a ∈ IsLocalRing.maximalIdeal A := fun h => ha (isUnit_of_map_unit ψ₀.toRingHom a h)
  refine ⟨W * ψ₀ a, Ideal.mul_mem_left _ _ hψa, ?_⟩
  rw [v1, hW, ← hval, map_mul]
  congr 1
  exact DFunLike.congr_fun e1 a

theorem exists_mem_maximalIdeal_evR (hbc : FrameBC Z) {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}
    (Φ : FlagTor Z e U) {A k : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [IsAlgClosed k] [Algebra A k]
    [IsFractionRing A k] [Algebra c.F A] [Algebra c.F k] [IsScalarTower c.F A k]
    (xA : Sp A ⟶ gen Z) (hxA : xA ≫ genStr Z = spMap (algebraMap c.F A))
    (gA : EigFrame Z (algebraMap c.F A) (xA ≫ genι Z)) (z : FrPt Xo c k)
    (hz : GlobalTheory.AllWt.ptF z ≫ Z.jQ = spMap (algebraMap A k) ≫ xA)
    (hu : ∀ τ i, TanRel Z (GlobalTheory.AllWt.ptF z) (z.u τ i) (spMap (dualMap (algebraMap A k)) ≫ gA.v τ i))
    (hbd : xA (IsLocalRing.closedPoint A) ∈ genBd Z) {ex : Ix Dw → ℤ} (hex : ex none = 0) {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex)
    (hv : ∀ i, (Φ.C i).Y.vanishOn ((Φ.C i).LEx ex) ((Φ.C i).val f) (Φ.C i).Ybd) :
    ∃ b ∈ IsLocalRing.maximalIdeal A, evR Xo c f z = algebraMap A k b := by
  have hφ : (algebraMap A k).comp (algebraMap c.F A) = algebraMap c.F k := (IsScalarTower.algebraMap_eq _ _ _).symm
  obtain ⟨gk, hgk⟩ := hbc.at gA (algebraMap A k) (x' := (spMap (algebraMap A k) ≫ xA) ≫ genι Z) (Category.assoc _ _ _)
  have hTz : Comparison₂ z gk := ⟨hφ, by rw [Model.j, ← Category.assoc, hz], fun τ i => by rw [hgk]; exact hu τ i⟩
  have hstr : (spMap (algebraMap A k) ≫ xA) ≫ genStr Z = spMap ((algebraMap A k).comp (algebraMap c.F A)) := by
    rw [Category.assoc, hxA, sp_comp]
  obtain ⟨⟨i, p⟩, ⟨hp, hc⟩, -⟩ := Φ.lifts k _ _ hstr gk
  obtain ⟨w⟩ := wit_of_carries (hz.trans hp.symm) hTz hc
  exact exists_mem_of_wit hbc xA hxA gA z gk (Category.assoc _ _ _) hφ hgk hTz p hp w hbd hex hf (hv i)

theorem mem_of_dominates {V K A k : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CommRing A] [IsLocalRing A] [Field k] [Algebra A k]
    (hinj : Function.Injective (algebraMap A k)) (j : K →+* k) (i : V →+* A) [IsLocalHom i]
    (h : (algebraMap A k).comp i = j.comp (algebraMap V K)) {w : K} {b : A} (hb : b ∈ IsLocalRing.maximalIdeal A)
    (hw : j w = algebraMap A k b) : ∃ v ∈ IsLocalRing.maximalIdeal V, w = algebraMap V K v := by
  have hc : ∀ a, algebraMap A k (i a) = j (algebraMap V K a) := fun a => DFunLike.congr_fun h a
  rcases ValuationRing.isInteger_or_isInteger V w with ⟨a, ha⟩ | ⟨a, ha⟩
  · have e : i a = b := hinj (by rw [hc, ha, hw])
    exact ⟨a, fun hu => hb (e ▸ hu.map i), ha.symm⟩
  · by_cases h0 : w = 0
    · exact ⟨0, Ideal.zero_mem _, by simp [h0]⟩
    · exfalso
      have e : i a * b = 1 := hinj (by
        rw [map_mul, hc, ha, ← hw, ← map_mul, inv_mul_cancel₀ h0, map_one, map_one])
      exact hb (IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at e))

theorem mem_of_boundary_extension_valuation (hbc : FrameBC Z) {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U)
    {V K A k : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    [Algebra c.F K] [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [IsAlgClosed k] [Algebra A k]
    [IsFractionRing A k] [Algebra K k] [Algebra c.F A] [Algebra c.F k] [IsScalarTower c.F A k] [IsScalarTower c.F K k]
    (i : V →+* A) [IsLocalHom i] (hi : (algebraMap A k).comp i = (algebraMap K k).comp (algebraMap V K))
    (φ : c.F →+* V) (hiφ : i.comp φ = algebraMap c.F A) (y : FrPt Xo c K) {ex : Ix Dw → ℤ} {f : Rul Xo c}
    (hB : BdExt Z φ y) (hex : ex none = 0) (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex)
    (hv : ∀ i, (Φ.C i).Y.vanishOn ((Φ.C i).LEx ex) ((Φ.C i).val f) (Φ.C i).Ybd) :
    ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f y = algebraMap V K v := by
  obtain ⟨χ, g, hχ, hpt, hw, hbd⟩ := hB
  obtain ⟨z, hzm⟩ := exists_frMap (IsScalarTower.toAlgHom c.F K k) y
  obtain ⟨gA, hgA⟩ : ∃ gA : EigFrame Z (algebraMap c.F A) ((spMap i ≫ χ) ≫ genι Z), ∀ τ j,
      gA.v τ j = spMap (dualMap i) ≫ g.v τ j := hiφ ▸ hbc.at g i (x' := (spMap i ≫ χ) ≫ genι Z) (Category.assoc _ _ _)
  have hspm : spMap (algebraMap A k) ≫ spMap i = spMap (algebraMap K k) ≫ spMap (algebraMap V K) := by
    rw [sp_comp, sp_comp, hi]
  have hcoe : (IsScalarTower.toAlgHom c.F K k).toRingHom = algebraMap K k := RingHom.ext fun _ => rfl
  have hptz : GlobalTheory.AllWt.ptF z = spMap (algebraMap K k) ≫ GlobalTheory.AllWt.ptF y := by
    have h0 := ptF_map (φ := IsScalarTower.toAlgHom c.F K k) hzm.1
    rwa [hcoe] at h0
  obtain ⟨b, hb, hbv⟩ := exists_mem_maximalIdeal_evR (A := A) (k := k) hbc Φ (spMap i ≫ χ)
    (by rw [Category.assoc, hχ, sp_comp, hiφ]) gA z
    (by rw [hptz, Category.assoc, hpt, ← Category.assoc, ← hspm, Category.assoc])
    (fun τ j => by
      obtain ⟨w, w1, w2, w3⟩ := hw τ j
      have h1 : TanRel Z (GlobalTheory.AllWt.ptF y) (y.u τ j) (spMap (dualMap (algebraMap V K)) ≫ g.v τ j) := ⟨w, w1, w2, w3⟩
      have h2 := h1.map (algebraMap K k)
      have h3 : spMap (dualMap (algebraMap K k)) ≫ spMap (dualMap (algebraMap V K)) ≫ g.v τ j =
          spMap (dualMap (algebraMap A k)) ≫ gA.v τ j := by
        rw [hgA, ← Category.assoc (spMap (dualMap (algebraMap K k))), ← Category.assoc (spMap (dualMap (algebraMap A k))),
          dual_comp, dual_comp, hi]
      rw [hptz, show z.u τ j = _ from hzm.2.1 τ j, ← h3]
      exact h2)
    (by
      have h1 : (spMap i) (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint V :=
        IsLocalRing.comap_closedPoint i
      have h2 : (spMap i ≫ χ) (IsLocalRing.closedPoint A) = χ ((spMap i) (IsLocalRing.closedPoint A)) := rfl
      rw [h2, h1]; exact hbd)
    hex hf hv
  have hj := evR_frMap hf.1 hzm
  exact mem_of_dominates (IsFractionRing.injective A k) (algebraMap K k) i hi hb (hj.symm.trans hbv)

theorem mem_of_bdExt (hbc : FrameBC Z) {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U)
    {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) {ex : Ix Dw → ℤ} {f : Rul Xo c}
    (hφ : (algebraMap V K).comp φ = algebraMap c.F K) (hB : BdExt Z φ y) (hex : ex none = 0)
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex)
    (hv : ∀ i, (Φ.C i).Y.vanishOn ((Φ.C i).LEx ex) ((Φ.C i).val f) (Φ.C i).Ybd) :
    ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f y = algebraMap V K v := by
  let ι₁ : V →+* AlgebraicClosure K := (algebraMap K (AlgebraicClosure K)).comp (algebraMap V K)
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing ι₁
  let i : V →+* A := ι₁.codRestrict A.toSubring hA
  haveI : IsLocalHom i := hloc
  have hi : (algebraMap A (AlgebraicClosure K)).comp i = ι₁ := rfl
  letI : Algebra c.F A := (i.comp φ).toAlgebra
  haveI : IsScalarTower c.F A (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq' (by
    change algebraMap c.F (AlgebraicClosure K) = (algebraMap A (AlgebraicClosure K)).comp (i.comp φ)
    rw [← RingHom.comp_assoc, hi, RingHom.comp_assoc, hφ]
    exact IsScalarTower.algebraMap_eq _ _ _)
  exact mem_of_boundary_extension_valuation hbc Φ i hi φ rfl y hB hex hf hv

end Core

end GlobalTheory.CuspFrom.Vanish

namespace GlobalTheory.CuspFrom

theorem evR_mem_maximalIdeal_of_vanishOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), (∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i) → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Φ : FlagTor Z e U) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) (ex : Ix Dw → ℤ) (f : Rul Xo c), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z φ y → ex none = 0 → f ∈ GlobalTheory.AllWt.secZ Xo c ex → (∀ k, (Φ.C k).Y.vanishOn ((Φ.C k).LEx ex) ((Φ.C k).val f) (Φ.C k).Ybd) → ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f y = algebraMap V K v :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ Z hbc _ _ _ _ _ _ Φ _ _ _ _ _ _ _ _ _ φ y ex f hφ hB hex hf hv =>
    Vanish.mem_of_bdExt (Z := Z) hbc Φ φ y hφ hB hex hf hv

end GlobalTheory.CuspFrom
end
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_base_change_local_rings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), (∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i) → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Φ : FlagTor Z e U) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) (ex : Ix Dw → ℤ) (f : Rul Xo c), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z φ y → ex none = 0 → f ∈ GlobalTheory.AllWt.secZ Xo c ex → (∀ k, (Φ.C k).Y.vanishOn ((Φ.C k).LEx ex) ((Φ.C k).val f) (Φ.C k).Ybd) → ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f y = algebraMap V K v := by
  first | exact @GlobalTheory.CuspFrom.evR_mem_maximalIdeal_of_vanishOn | exact GlobalTheory.CuspFrom.evR_mem_maximalIdeal_of_vanishOn | (intros; apply GlobalTheory.CuspFrom.evR_mem_maximalIdeal_of_vanishOn <;> assumption)
end
