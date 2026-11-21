import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSimR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetOfInvolutive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugacyClassClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCentralizerTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrbitCentralizerAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointOfEventuallyIntegralLocaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactIntegralUnitaryPointsAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedDoubleCosetsLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatInt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitIdempotentConjugation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtPStatement

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int : ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  first | (exact @GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (exact GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (intros; apply GlobalTheory.AdeleZ.exists_continuous_adele_equiv <;> assumption)
end

section
open IsDedekindDomain

namespace GlobalTheory.LKTrip

theorem AfP.continuous_restr (p : ℕ) : Continuous (AfP.restr p) :=
  RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ) Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ RingHom.id _) (Filter.Eventually.of_forall fun _ ↦ Set.mapsTo_id _)
    (fun _ ↦ continuous_id)

end GlobalTheory.LKTrip
end

section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_afP_restr : ∀ (p : ℕ), Continuous (GlobalTheory.LKTrip.AfP.restr p) := by
  first | (exact @GlobalTheory.LKTrip.AfP.continuous_restr) | (exact GlobalTheory.LKTrip.AfP.continuous_restr) | (intros; apply GlobalTheory.LKTrip.AfP.continuous_restr  <;> assumption)
end

section
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.AdeleSplitP

open GlobalTheory.LKTrip Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

def placeP (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(p : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).2
    (Nat.prime_iff_prime_int.mp hp.out)
  ne_bot := by simpa using hp.out.ne_zero

theorem primesEquiv_placeP (p : ℕ) [hp : Fact p.Prime] :
    primesEquiv (placeP p) = (⟨p, hp.out⟩ : Nat.Primes) := by
  apply Subtype.ext
  change natGenerator (placeP p) = p
  have h1 := span_natGenerator (placeP p)
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ :=
    RingEquiv.ext fun x ↦ by simpa using eq_intCast (Rat.IsIntegralClosure.intEquiv ℤ) x
  have h2 : (placeP p).asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) = (placeP p).asIdeal := by
    rw [he]
    exact Ideal.map_id _
  rw [h2] at h1
  change Ideal.span {((natGenerator (placeP p) : ℕ) : ℤ)} = Ideal.span {(p : ℤ)} at h1
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h1
  simpa using h1

def compP (p : ℕ) [hp : Fact p.Prime] : FiniteAdeleRing ℤ ℚ →+* ℚ_[p] :=
  ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).toRingEquiv.toRingHom.comp
    (adicCompletion.padicEquiv (placeP p)).toRingEquiv.toRingHom).comp
    (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ) (placeP p))

theorem compP_apply (p : ℕ) [Fact p.Prime] (a : FiniteAdeleRing ℤ ℚ) :
    compP p a = ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)
      (adicCompletion.padicEquiv (placeP p) (a (placeP p))) := rfl

theorem continuous_compP (p : ℕ) [Fact p.Prime] : Continuous (compP p) :=
  show Continuous (fun a ↦ compP p a) from (ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).continuous.comp
    ((adicCompletion.padicEquiv (placeP p)).continuous.comp (RestrictedProduct.continuous_eval _))

theorem restr_eval (p : ℕ) (a : FiniteAdeleRing ℤ ℚ) (w : AwayP p) :
    AfP.eval w (AfP.restr p a) = a w.1 := rfl

theorem finiteAdeleRingAway_ext {p : ℕ} {b c : AfP p} (h : ∀ w, AfP.eval w b = AfP.eval w c) : b = c :=
  Subtype.ext (funext fun w ↦ h w)

theorem eq_placeP {p : ℕ} [Fact p.Prime] {v : HeightOneSpectrum ℤ}
    (hv : v.asIdeal = Ideal.span {(p : ℤ)}) : v = placeP p :=
  HeightOneSpectrum.ext hv

theorem finiteAdele_split (p : ℕ) [Fact p.Prime] :
    ∃ π : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] ℚ_[p], Continuous π ∧
      Function.Bijective (fun a ↦ (GlobalTheory.LKTrip.AfP.restr p a, π a)) := by
  refine ⟨(compP p).toRatAlgHom, continuous_compP p, ?_, ?_⟩
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    refine FiniteAdeleRing.ext _ fun v ↦ ?_
    by_cases hv : v.asIdeal = Ideal.span {(p : ℤ)}
    · obtain rfl := eq_placeP hv
      have h2' : compP p a = compP p b := h2
      rw [compP_apply, compP_apply] at h2'
      exact (adicCompletion.padicEquiv (placeP p)).injective
        ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).injective h2')
    · exact congrArg (AfP.eval ⟨v, hv⟩) h1
  · rintro ⟨b, y⟩
    classical
    let x0 : (placeP p).adicCompletion ℚ := (adicCompletion.padicEquiv (placeP p)).symm
      ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).symm y)
    let g0 : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ := fun v ↦
      if h : v.asIdeal = Ideal.span {(p : ℤ)} then 0 else AfP.eval ⟨v, h⟩ b
    let g : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ := Function.update g0 (placeP p) x0
    have hg : ∀ v (hv : v.asIdeal ≠ Ideal.span {(p : ℤ)}), g v = AfP.eval ⟨v, hv⟩ b := by
      intro v hv
      have hv0 : v ≠ placeP p := fun h ↦ hv (h ▸ rfl)
      simp only [g, g0, Function.update_of_ne hv0, dif_neg hv]
    have hS : {w : AwayP p | ¬ AfP.eval w b ∈ w.1.adicCompletionIntegers ℚ}.Finite :=
      Filter.eventually_cofinite.1 b.2
    have hfin : {v : HeightOneSpectrum ℤ | ¬ g v ∈ v.adicCompletionIntegers ℚ}.Finite := by
      refine ((hS.image Subtype.val).insert (placeP p)).subset fun v hv ↦ ?_
      by_cases hv0 : v = placeP p
      · exact Or.inl hv0
      · have hv' : v.asIdeal ≠ Ideal.span {(p : ℤ)} := fun h ↦ hv0 (eq_placeP h)
        refine Or.inr ⟨⟨v, hv'⟩, ?_, rfl⟩
        have hv2 : ¬ g v ∈ v.adicCompletionIntegers ℚ := hv
        rw [hg v hv'] at hv2
        exact hv2
    let A : FiniteAdeleRing ℤ ℚ := ⟨g, Filter.eventually_cofinite.2 hfin⟩
    refine ⟨A, Prod.ext ?_ ?_⟩
    · show AfP.restr p A = b
      refine finiteAdeleRingAway_ext fun w ↦ ?_
      rw [restr_eval]
      exact hg w.1 w.2
    · show compP p A = y
      change ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)
        (adicCompletion.padicEquiv (placeP p) (g (placeP p))) = y
      simp only [g, Function.update_self, x0, ContinuousAlgEquiv.apply_symm_apply]

end GlobalTheory.AdeleSplitP
end
end

section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic : ∀ (p : ℕ) [Fact p.Prime], ∃ π : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] ℚ_[p], Continuous π ∧ Function.Bijective (fun a => (GlobalTheory.LKTrip.AfP.restr p a, π a)) := by
  first | (exact @GlobalTheory.AdeleSplitP.finiteAdele_split) | (exact GlobalTheory.AdeleSplitP.finiteAdele_split) | (intros; apply GlobalTheory.AdeleSplitP.finiteAdele_split  <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.CentTorus
open scoped TensorProduct

namespace GlobalTheory.CentTorus.ClassSplit

section Tmap

variable {A B L : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] [CommRing L] [Algebra ℚ L]

def tmap (π : A →ₐ[ℚ] B) : L ⊗[ℚ] A →ₐ[ℚ] B ⊗[ℚ] L :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeLeft.comp π)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tmap_tmul (π : A →ₐ[ℚ] B) (l : L) (a : A) : tmap π (l ⊗ₜ[ℚ] a) = π a ⊗ₜ[ℚ] l := by
  simp [tmap]

end Tmap

end GlobalTheory.CentTorus.ClassSplit

namespace GlobalTheory.CentTorus.ClassSplit

end GlobalTheory.CentTorus.ClassSplit

namespace GlobalTheory.CentTorus.ClassSplit

theorem adele_split (p : ℕ) [Fact p.Prime] :
    ∃ (π₁ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p) (π₂ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] ℚ_[p]),
      Continuous π₁ ∧ Continuous π₂ ∧ Function.Bijective (fun a => (π₁ a, π₂ a)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int
  obtain ⟨π, hπc, hπb⟩ := GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic p
  let r : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] AfP p := { AfP.restr p with commutes' := fun _ => rfl }
  exact ⟨r.comp e.toAlgHom, π.comp e.toAlgHom, (GlobalTheory.T.continuous_afP_restr p).comp he, hπc.comp he, hπb.comp e.bijective⟩

end GlobalTheory.CentTorus.ClassSplit

section Final

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

end Final
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAway

theorem flat_centralizer (R B L : Type) [CommRing R] [Algebra ℚ R] [Ring B] [Algebra ℚ B] [Ring L] [Algebra ℚ L]
    (γ : B) (f : L →ₐ[ℚ] B) (hf : Function.Injective f)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R) f) ∧
      ∀ y : R ⊗[ℚ] B, y * ((1 : R) ⊗ₜ[ℚ] γ) = ((1 : R) ⊗ₜ[ℚ] γ) * y ↔
        y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id R R) f) := by
  let ad : B →ₗ[ℚ] B := LinearMap.mulRight ℚ γ - LinearMap.mulLeft ℚ γ
  have hex : Function.Exact f.toLinearMap ad := by
    intro x
    simp only [ad, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply]
    exact hcent x
  have hmap : ∀ y, Algebra.TensorProduct.map (AlgHom.id R R) f y = LinearMap.lTensor R f.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have had : ∀ y : R ⊗[ℚ] B, y * ((1 : R) ⊗ₜ[ℚ] γ) - ((1 : R) ⊗ₜ[ℚ] γ) * y = LinearMap.lTensor R ad y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      simp [ad, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add, ← hx, ← hy]; noncomm_ring
  have hex' := Module.Flat.lTensor_exact R hex
  refine ⟨?_, fun y => ?_⟩
  · have h := Module.Flat.lTensor_preserves_injective_linearMap (M := R) f.toLinearMap hf
    intro a b hab
    rw [hmap, hmap] at hab
    exact h hab
  · rw [← sub_eq_zero, had, hex' y]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, hmap z⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, (hmap z).symm⟩

variable {p : ℕ} [Fact p.Prime]

def incl (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    R ⊗[ℚ] algF P →ₐ[R] R ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id R R) ((algF P).val.restrictScalars ℚ)

theorem incl_tmul (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (a : R) (m : algF P) :
    incl R P (a ⊗ₜ m) = a ⊗ₜ (m : G.C) := rfl

theorem cent_iff {G : HTGroup p} (P : Pair G) (x : G.C) :
    x * P.γ = P.γ * x ↔ x ∈ Set.range ((algF P).val.restrictScalars ℚ) := by
  have h := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC (P.γ : G.C) P.reg.2 P.reg.1
  constructor
  · intro hx
    have hm : x ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.1 hg]
      exact hx.symm
    rw [h] at hm
    exact ⟨⟨x, hm⟩, rfl⟩
  · rintro ⟨m, rfl⟩
    have hm : (m : G.C) ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by rw [h]; exact m.2
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact (hm _ (Set.mem_singleton _)).symm

theorem incl_facts (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    Function.Injective (incl R P) ∧ ∀ y : R ⊗[ℚ] G.C, y * inC G R P.γ = inC G R P.γ * y ↔ y ∈ Set.range (incl R P) :=
  flat_centralizer R G.C (algF P) (P.γ : G.C) _ Subtype.val_injective (cent_iff P)

theorem exists_retr (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    ∃ π : R ⊗[ℚ] algF P →ₗ[R] R, ∀ a, π (algebraMap R _ a) = a := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ (algF P))
    (LinearMap.ker_eq_bot.2 (algebraMap ℚ (algF P)).injective)
  have h1 : φ 1 = 1 := by
    have := LinearMap.congr_fun hφ 1
    simpa using this
  refine ⟨(TensorProduct.AlgebraTensorModule.rid ℚ R R).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor R R φ, fun a => ?_⟩
  simp [Algebra.TensorProduct.algebraMap_apply, h1]

theorem alg_inj (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    Function.Injective (algebraMap R (R ⊗[ℚ] algF P)) := by
  obtain ⟨π, hπ⟩ := exists_retr R P
  intro a b h
  rw [← hπ a, ← hπ b, h]

theorem incl_extC (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)
    (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (z : R ⊗[ℚ] algF P) :
    incl R P (extC R c z) =
      inC G R P.β * (starT G.star R (incl R P z)).unop * inC G R ((P.β⁻¹ : G.Cˣ) : G.C) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [incl_tmul, starT_tmul]
    simp only [extC, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, incl_tmul, hc, inC, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, sh]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, MulOpposite.unop_add, mul_add, add_mul]

theorem incl_sim (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)
    (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (y : R ⊗[ℚ] algF P) (s : R) (hy : y * extC R c y = algebraMap R _ s) :
    incl R P y * inC G R P.β * (starT G.star R (incl R P y)).unop = algebraMap R (R ⊗[ℚ] G.C) s * inC G R P.β := by
  have h1 := congrArg (incl R P) hy
  rw [map_mul, incl_extC R P c hc, AlgHom.commutes] at h1
  have hb : inC G R ((P.β⁻¹ : G.Cˣ) : G.C) * inC G R P.β = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  calc incl R P y * inC G R P.β * (starT G.star R (incl R P y)).unop
      = incl R P y * (inC G R P.β * (starT G.star R (incl R P y)).unop * inC G R ((P.β⁻¹ : G.Cˣ) : G.C)) *
          inC G R P.β := by
        simp only [mul_assoc, hb, mul_one]
    _ = _ := by rw [h1]

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

variable {p : ℕ} [Fact p.Prime]

section Generic

variable (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)

def nu (y : simR R (extC R c)) : Rˣ := (mem_simR.1 y.2).choose

theorem nu_spec (y : simR R (extC R c)) :
    ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) =
      algebraMap R _ ((nu R P c y : Rˣ) : R) :=
  (mem_simR.1 y.2).choose_spec

theorem nu_eq (y : simR R (extC R c)) (s : Rˣ)
    (h : ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) =
      algebraMap R _ (s : R)) : nu R P c y = s :=
  Units.ext (alg_inj R P (by rw [← nu_spec, h]))

def nuHom : simR R (extC R c) →* Rˣ where
  toFun := nu R P c
  map_one' := nu_eq R P c 1 1 (by simp [Algebra.TensorProduct.one_def])
  map_mul' y z := nu_eq R P c _ _ (by
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
    rw [show ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * ((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) *
        (extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P)) =
        (((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P)) *
        (((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P)) by ring,
      nu_spec, nu_spec])

def conjHom (x : (R ⊗[ℚ] G.C)ˣ) : simR R (extC R c) →* (R ⊗[ℚ] G.C)ˣ :=
  (MulAut.conj x).toMonoidHom.comp
    ((Units.map (incl R P).toRingHom.toMonoidHom).comp (simR R (extC R c)).subtype)

def phi0 (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ) (hx : Triv G R P.β x t) : simR R (extC R c) →* UPts G.star R :=
  ((conjHom R P c x).prod (nuHom R P c)).codRestrict _ fun y =>
    conj_mul_star (starT G.star R) (inC G R P.β) x
      (Units.map (incl R P).toRingHom.toMonoidHom (y : (R ⊗[ℚ] algF P)ˣ)) t ((nu R P c y : Rˣ) : R) hx
      (incl_sim R P c hc _ _ (nu_spec R P c y))

end Generic

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

open GlobalTheory.BCT

variable {p : ℕ} [Fact p.Prime]

def phi {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)
    (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) :
    simR (AfP p) (extC (AfP p) c) →* twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self) :=
  (phi0 (AfP p) P c hc x t hx).codRestrict _ fun y => by
    have hYΓ : Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) *
        Units.map (inC G (AfP p)).toMonoidHom P.γ =
        Units.map (inC G (AfP p)).toMonoidHom P.γ * Units.map (incl (AfP p) P).toRingHom.toMonoidHom y :=
      Units.ext (((incl_facts (AfP p) P).2 _).2 ⟨_, rfl⟩)
    refine Subtype.ext (Prod.ext ?_ (mul_comm _ _))
    change x * Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) * x⁻¹ *
        (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) =
      x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹ *
        (x * Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) * x⁻¹)
    calc _ = x * (Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) *
          Units.map (inC G (AfP p)).toMonoidHom P.γ) * x⁻¹ := by group
      _ = _ := by rw [hYΓ]; group

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

open GlobalTheory.BCT

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.CentAway
end
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.CentTorus
open scoped TensorProduct

namespace GlobalTheory.CentTorus.AdelicSplit

section Tmap

variable {A B L : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] [CommRing L] [Algebra ℚ L]

def tmap (π : A →ₐ[ℚ] B) : L ⊗[ℚ] A →ₐ[ℚ] B ⊗[ℚ] L :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeLeft.comp π)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tmap_tmul (π : A →ₐ[ℚ] B) (l : L) (a : A) : tmap π (l ⊗ₜ[ℚ] a) = π a ⊗ₜ[ℚ] l := by
  simp [tmap]

end Tmap

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

theorem adele_split (p : ℕ) [Fact p.Prime] :
    ∃ (π₁ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p) (π₂ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] ℚ_[p]),
      Continuous π₁ ∧ Continuous π₂ ∧ Function.Bijective (fun a => (π₁ a, π₂ a)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int
  obtain ⟨π, hπc, hπb⟩ := GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic p
  let r : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] AfP p := { AfP.restr p with commutes' := fun _ => rfl }
  exact ⟨r.comp e.toAlgHom, π.comp e.toAlgHom, (GlobalTheory.T.continuous_afP_restr p).comp he, hπc.comp he, hπb.comp e.bijective⟩

end GlobalTheory.CentTorus.AdelicSplit

section Final

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

end Final
end
end
