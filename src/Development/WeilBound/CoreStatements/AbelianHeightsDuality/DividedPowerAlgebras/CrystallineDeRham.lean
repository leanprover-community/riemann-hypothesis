import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompF
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsFilEqBot
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallDescentH1Surjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

section Push

variable (S : Thick (dp0 R) s) {A : Type} [CommRing A] (a : S.B →+* A) {JA : Ideal A} (θ : DividedPowers JA)
  (ha : IsDPMorphism S.δ θ a)

include ha in
theorem push_ker : RingHom.ker S.π ≤ RingHom.ker ((Ideal.Quotient.mk JA).comp a) := fun b hb ↦
  Ideal.Quotient.eq_zero_iff_mem.2 (ha.1 (Ideal.mem_map_of_mem _ ((S.ker b).1 hb)))

def pushRed : S.B₀ →+* A ⧸ JA := RingHom.liftOfSurjective S.π S.surj ⟨_, push_ker S a θ ha⟩

theorem pushRed_π (b : S.B) : pushRed S a θ ha (S.π b) = Ideal.Quotient.mk JA (a b) :=
  RingHom.liftOfSurjective_comp_apply S.π S.surj ⟨_, push_ker S a θ ha⟩ b

variable (hn : IsNilDP θ)

def push : Thick (dp0 R) s where
  B := A
  alg := (a.comp (algebraMap R S.B)).toAlgebra
  J := JA
  δ := θ
  nil := hn
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  B₀ := A ⧸ JA
  π := Ideal.Quotient.mk JA
  surj := Ideal.Quotient.mk_surjective
  ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem
  x := spMap (pushRed S a θ ha) ≫ S.x
  w := by
    rw [Category.assoc, S.w, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ pushRed_π S a θ ha _

def pushHom : S ⟶ push S a θ ha hn where
  φ := { a with commutes' := fun _ ↦ rfl }
  φ₀ := pushRed S a θ ha
  comm := pushRed_π S a θ ha
  dp := ha
  pt := rfl

def pushDesc {V : Thick (dp0 R) s} (φ : S ⟶ V) (G : A →+* V.B) (hG : IsDPMorphism θ V.δ G)
    (e : G.comp a = (φ.φ : S.B →+* V.B)) : push S a θ ha hn ⟶ V where
  φ := { G with commutes' := fun r ↦ (DFunLike.congr_fun e _).trans (φ.φ.commutes r) }
  φ₀ := Ideal.Quotient.lift JA (V.π.comp G) fun _ hc ↦ (V.ker _).2 (hG.1 (Ideal.mem_map_of_mem _ hc))
  comm := fun _ ↦ rfl
  dp := hG
  pt := by
    change spMap _ ≫ spMap (pushRed S a θ ha) ≫ S.x = V.x
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← φ.pt]
    congr 2
    refine RingHom.ext fun b ↦ ?_
    obtain ⟨b, rfl⟩ := S.surj b
    rw [RingHom.comp_apply, pushRed_π, φ.comm]
    exact congrArg V.π (DFunLike.congr_fun e b)

end Push

theorem exists_trunc (S : Thick (dp0 R) s) (hS : InN κ S) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P), InN κ P ∧ IsLev P.δ n ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V), ∃! ψ : P ⟶ V, i ≫ ψ = φ := by
  obtain ⟨A, _, a, JA, θ, ha, hlev, hext, hsurj, huniv⟩ := ring_trunc κ (algebraMap R S.B) S.δ hS n hn
  have hnil : IsNilDP θ := Fil.nil_of_lev hlev
  refine ⟨push S a θ ha hnil, pushHom S a θ ha hnil, hext, hlev, ?_⟩
  intro V hV φ
  obtain ⟨G, hG, hGa⟩ := huniv V.B V.J V.δ hV (φ.φ : S.B →+* V.B) φ.dp
  refine ⟨pushDesc S a θ ha hnil φ G hG hGa, ?_, ?_⟩
  · refine Thick.hom_ext fun b ↦ ?_
    rw [Thick.comp_φ]
    exact DFunLike.congr_fun hGa b
  · intro ψ hψ
    refine Thick.hom_ext fun x ↦ ?_
    obtain ⟨b, rfl⟩ := hsurj x
    have h1 := Thick.comp_φ (pushHom S a θ ha hnil) ψ b
    rw [hψ] at h1
    have h2 : G (a b) = φ.φ b := DFunLike.congr_fun hGa b
    exact h1.symm.trans h2.symm

theorem exists_adj_one (S : Thick (dp0 R) s) (hS : InN κ S) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (y : P.B), InN κ P ∧ IsLev P.δ n ∧ y ∈ P.J ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (z : V.B), z ∈ V.J →
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ ψ.φ y = z := by
  obtain ⟨A, _, a, JA, θ, y, ha, hlev, hext, hy, huniv⟩ := ring_adj κ (algebraMap R S.B) S.δ hS n hn
  have hnil : IsNilDP θ := Fil.nil_of_lev hlev
  refine ⟨push S a θ ha hnil, pushHom S a θ ha hnil, y, hext, hlev, hy, ?_⟩
  intro V hV φ z hz
  obtain ⟨G, ⟨hG, hGa, hGy⟩, huniq⟩ := huniv V.B V.J V.δ hV (φ.φ : S.B →+* V.B) φ.dp z hz
  refine ⟨pushDesc S a θ ha hnil φ G hG hGa, ⟨?_, hGy⟩, ?_⟩
  · refine Thick.hom_ext fun b ↦ ?_
    rw [Thick.comp_φ]
    exact DFunLike.congr_fun hGa b
  · rintro ψ ⟨hψ, hψy⟩
    let g : A →+* V.B := ψ.φ.toRingHom
    have hcomp : g.comp a = (φ.φ : S.B →+* V.B) := by
      refine RingHom.ext fun b ↦ ?_
      have h1 := Thick.comp_φ (pushHom S a θ ha hnil) ψ b
      rw [hψ] at h1
      exact h1.symm
    have heq : g = G := huniq g ⟨ψ.dp, hcomp, hψy⟩
    refine Thick.hom_ext fun x ↦ ?_
    exact DFunLike.congr_fun heq x

theorem exists_adj' (S : Thick (dp0 R) s) (hS : InN κ S) (d n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (y : Fin d → P.B), InN κ P ∧ IsLev P.δ n ∧ (∀ k, y k ∈ P.J) ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (z : Fin d → V.B), (∀ k, z k ∈ V.J) →
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ ∀ k, ψ.φ (y k) = z k := by
  induction d with
  | zero =>
    obtain ⟨P, i, hP, hlev, huniv⟩ := exists_trunc S hS n hn
    refine ⟨P, i, Fin.elim0, hP, hlev, fun k ↦ Fin.elim0 k, ?_⟩
    intro V hV φ z _
    obtain ⟨ψ, hψ, huniq⟩ := huniv V hV φ
    exact ⟨ψ, ⟨hψ, fun k ↦ Fin.elim0 k⟩, fun ψ' h ↦ huniq ψ' h.1⟩
  | succ d ih =>
    obtain ⟨P, i, y, hP, hlev, hy, huniv⟩ := ih
    obtain ⟨Q, j, w, hQ, hlevQ, hw, hunivQ⟩ := exists_adj_one P hP n hn
    refine ⟨Q, i ≫ j, Fin.cons w (fun k ↦ j.φ (y k)), hQ, hlevQ, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · simpa using hw
      · simp only [Fin.cons_succ]
        exact j.dp.ideal_comp (Ideal.mem_map_of_mem _ (hy k))
    · intro V hV φ z hz
      obtain ⟨ψ₁, ⟨hψ₁, hψ₁y⟩, huniq₁⟩ := huniv V hV φ (fun k ↦ z k.succ) (fun k ↦ hz k.succ)
      obtain ⟨ψ, ⟨hψ, hψw⟩, huniq⟩ := hunivQ V hV ψ₁ (z 0) (hz 0)
      refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
      · rw [Category.assoc, hψ, hψ₁]
      · intro k
        refine Fin.cases ?_ (fun k ↦ ?_) k
        · simpa using hψw
        · simp only [Fin.cons_succ]
          rw [← Thick.comp_φ, hψ]
          exact hψ₁y k
      · rintro ψ' ⟨hψ', hψ'y⟩
        have h1 : j ≫ ψ' = ψ₁ := by
          refine huniq₁ (j ≫ ψ') ⟨?_, fun k ↦ ?_⟩
          · rw [← Category.assoc]
            exact hψ'
          · rw [Thick.comp_φ]
            have := hψ'y k.succ
            simpa only [Fin.cons_succ] using this
        refine huniq ψ' ⟨h1, ?_⟩
        have := hψ'y 0
        simpa only [Fin.cons_zero] using this

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

theorem exists_adj (S : Thick (dp0 R) s) (hS : InN κ S) (d n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (y : Fin d → P.B), InN κ P ∧ IsLev P.δ n ∧ (∀ k, y k ∈ P.J) ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (z : Fin d → V.B), (∀ k, z k ∈ V.J) →
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ ∀ k, ψ.φ (y k) = z k :=
  exists_adj' S hS d n hn

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

section Rings

variable {P A B C : Type} [CommRing P] [CommRing A] [CommRing B] [CommRing C]

theorem fe_lift (t : P →+* A) (ht : t.FormallyEtale) (π : B →+* C) (hπ : Function.Surjective π)
    (hn : IsNilpotent (RingHom.ker π)) (u : P →+* B) (f : A →+* C) (h : f.comp t = π.comp u) :
    ∃ g : A →+* B, g.comp t = u ∧ π.comp g = f := by
  letI := t.toAlgebra
  letI : Algebra P C := (π.comp u).toAlgebra
  letI : Algebra P B := u.toAlgebra
  haveI : Algebra.FormallyEtale P A := ht
  let fA : A →ₐ[P] C := { f with commutes' := fun r => RingHom.congr_fun h r }
  let πA : B →ₐ[P] C := { π with commutes' := fun r => rfl }
  let g := Algebra.FormallySmooth.liftOfSurjective fA πA hπ hn
  refine ⟨g.toRingHom, ?_, ?_⟩
  · ext r
    exact g.commutes r
  · ext x
    exact Algebra.FormallySmooth.liftOfSurjective_apply fA πA hπ hn x

theorem fe_uniq (t : P →+* A) (ht : t.FormallyEtale) (π : B →+* C) (hn : IsNilpotent (RingHom.ker π))
    (g₁ g₂ : A →+* B) (h : g₁.comp t = g₂.comp t) (h' : π.comp g₁ = π.comp g₂) : g₁ = g₂ := by
  letI := t.toAlgebra
  letI : Algebra P B := (g₁.comp t).toAlgebra
  haveI : Algebra.FormallyEtale P A := ht
  let a₁ : A →ₐ[P] B := { g₁ with commutes' := fun r => rfl }
  let a₂ : A →ₐ[P] B := { g₂ with commutes' := fun r => (RingHom.congr_fun h r).symm }
  have key := Algebra.FormallyUnramified.ext' π hn a₁ a₂ (fun x => RingHom.congr_fun h' x)
  ext x
  exact AlgHom.congr_fun key x

theorem fe_of_etale {t : P →+* A} (ht : t.Etale) : t.FormallyEtale := by
  letI := t.toAlgebra
  haveI : Algebra.Etale P A := ht
  show Algebra.FormallyEtale P A
  infer_instance

theorem isNilpotent_of_isNilDP {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) : IsNilpotent J := by
  obtain ⟨N, hN⟩ := h.exists_dpow_eq_zero
  have hexp : ∀ xs : List B, (∀ x ∈ xs, x ∈ J) → ∀ y ∈ J, ∀ n, N ≤ n →
      PowerSeries.coeff n ((xs.map fun x => δ.exp x - 1).prod * δ.exp y) = 0 := by
    intro xs
    induction xs with
    | nil =>
      intro _ y _ n hn
      simp [DividedPowers.exp, PowerSeries.coeff_mk, hN n hn]
    | cons x xs ih =>
      intro hxs y hy n hn
      have hx : x ∈ J := hxs x (by simp)
      have hxs' : ∀ z ∈ xs, z ∈ J := fun z hz => hxs z (by simp [hz])
      have e : (List.map (fun x => δ.exp x - 1) (x :: xs)).prod * δ.exp y
          = (xs.map fun x => δ.exp x - 1).prod * δ.exp (x + y)
            - (xs.map fun x => δ.exp x - 1).prod * δ.exp y := by
        rw [δ.exp_add hx hy, List.map_cons, List.prod_cons]
        ring
      rw [e, map_sub, ih hxs' (x + y) (J.add_mem hx hy) n hn, ih hxs' y hy n hn, sub_zero]
  have hone : δ.exp 0 = 1 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [DividedPowers.exp, δ.dpow_zero J.zero_mem]
    · simp [DividedPowers.exp, PowerSeries.coeff_one, δ.dpow_eval_zero hn.ne', hn.ne']
  have hfac : ∀ xs : List B, (∀ x ∈ xs, x ∈ J) → ∃ G : PowerSeries B,
      (xs.map fun x => δ.exp x - 1).prod = PowerSeries.X ^ xs.length * G ∧
        PowerSeries.constantCoeff G = xs.prod := by
    intro xs
    induction xs with
    | nil => exact fun _ => ⟨1, by simp, by simp⟩
    | cons x xs ih =>
      intro hxs
      have hx : x ∈ J := hxs x (by simp)
      obtain ⟨G, hG, hG0⟩ := ih (fun z hz => hxs z (by simp [hz]))
      refine ⟨PowerSeries.mk (fun n => δ.dpow (n + 1) x) * G, ?_, ?_⟩
      · have ex : δ.exp x - 1 = PowerSeries.X * PowerSeries.mk (fun n => δ.dpow (n + 1) x) := by
          ext n
          rcases n with _ | n
          · simp [DividedPowers.exp, δ.dpow_zero hx]
          · rw [PowerSeries.coeff_succ_X_mul]
            simp [DividedPowers.exp, PowerSeries.coeff_one]
        rw [List.map_cons, List.prod_cons, hG, ex, List.length_cons, pow_succ]
        ring
      · rw [map_mul, hG0, List.prod_cons, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_mk, zero_add, δ.dpow_one hx]
  have hprod : ∀ xs : List B, (∀ x ∈ xs, x ∈ J) → N ≤ xs.length → xs.prod = 0 := by
    intro xs hxs hlen
    obtain ⟨G, hG, hG0⟩ := hfac xs hxs
    have := hexp xs hxs 0 J.zero_mem xs.length hlen
    rw [hone, mul_one, hG] at this
    have e2 := PowerSeries.coeff_X_pow_mul G xs.length 0
    rw [zero_add] at e2
    rw [e2, PowerSeries.coeff_zero_eq_constantCoeff_apply, hG0] at this
    exact this
  have key : ∀ n, ∀ z ∈ J ^ n, ∀ xs : List B, (∀ x ∈ xs, x ∈ J) → N ≤ n + xs.length →
      z * xs.prod = 0 := by
    intro n
    induction n with
    | zero =>
      intro z _ xs hxs hlen
      rw [hprod xs hxs (by simpa using hlen), mul_zero]
    | succ n ih =>
      intro z hz xs hxs hlen
      rw [pow_succ'] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        have := ih b hb (a :: xs) (fun x hx' => by
          rcases List.mem_cons.1 hx' with rfl | hx'
          · exact ha
          · exact hxs x hx') (by simp; omega)
        rw [List.prod_cons] at this
        rw [← this]
        ring
      · intro u v hu hv
        rw [add_mul, hu, hv, add_zero]
  refine ⟨N, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  intro z hz
  have := key N z hz [] (by simp) (by simp)
  simpa using this

end Rings

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

instance (U : X.affineOpens) : IsOpenImmersion (affPt s U) := U.2.isOpenImmersion_fromSpec

theorem nil_ker {γ : DividedPowers I} (T : Thick γ s) : IsNilpotent (RingHom.ker T.π) := by
  have : RingHom.ker T.π = T.J := Ideal.ext T.ker
  rw [this]
  exact isNilpotent_of_isNilDP T.nil

theorem res_etale {U V : X.affineOpens} (h : V.1 ≤ U.1) : (Sec.res s h : Sec s U.1 →+* Sec s V.1).Etale := by
  have e : V.1 ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U.1 := h
  have H := (𝟙 X : X ⟶ X).etale_appLE U.2 V.2 e
  have key : ((𝟙 X : X ⟶ X).appLE U.1 V.1 e).hom = (Sec.res s h : Sec s U.1 →+* Sec s V.1) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    rfl
  rw [key] at H
  exact H

theorem sec_smooth (hs : Smooth s) (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have e : U.1 ≤ s ⁻¹ᵁ (⊤ : (Sp R).Opens) := le_top
  have H1 : (s.appLE ⊤ U.1 e).hom.Smooth := hs.smooth_appLE (isAffineOpen_top (Sp R)) U.2 e
  have H0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Smooth :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have H := H0.comp H1
  rw [← RingHom.smooth_algebraMap]
  exact H

theorem chart_cover (hs : Smooth s) : ⨆ U : Chart s, U.1.1 = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  rw [TopologicalSpace.Opens.mem_iSup]
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  letI algV : Algebra R Γ(X, V) := (secMap s V).hom.toAlgebra
  have hsmV : Algebra.Smooth R Γ(X, V) := by
    have e : V ≤ s ⁻¹ᵁ (⊤ : (Sp R).Opens) := le_top
    have H1 : (s.appLE ⊤ V e).hom.Smooth := hs.smooth_appLE (isAffineOpen_top (Sp R)) hV e
    have H0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Smooth :=
      RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact H0.comp H1
  obtain ⟨S, hS, hSt⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R Γ(X, V)
  have hcov := (hV.iSup_basicOpen_eq_self_iff (s := S)).2 hS
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hxV
  obtain ⟨⟨g, hgS⟩, hxg⟩ := hxV
  let W : X.affineOpens := ⟨X.basicOpen g, hV.basicOpen g⟩
  refine ⟨⟨W, ?_, ?_⟩, hxg⟩
  · exact RingHom.flat_algebraMap_iff.1
      (RingHom.Smooth.flat (RingHom.smooth_algebraMap.2 (sec_smooth hs W)))
  · haveI := hSt g hgS
    obtain ⟨d, g', hg'C, hg'e⟩ :=
      RingHom.IsStandardSmooth.exists_etale_mvPolynomial (RingHom.isStandardSmooth_algebraMap.2 this)
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) := hV.isLocalization_basicOpen g
    let e : Localization.Away g ≃ₐ[Γ(X, V)] Γ(X, X.basicOpen g) :=
      IsLocalization.algEquiv (Submonoid.powers g) _ _
    have he : (e : Localization.Away g →+* Γ(X, X.basicOpen g)).FormallyEtale := by
      letI := (e : Localization.Away g →+* Γ(X, X.basicOpen g)).toAlgebra
      show Algebra.FormallyEtale (Localization.Away g) Γ(X, X.basicOpen g)
      exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ => rfl))
    have hcompat : ∀ r, e (algebraMap R (Localization.Away g) r) = algebraMap R (Sec s W.1) r := by
      intro r
      rw [IsScalarTower.algebraMap_apply R Γ(X, V) (Localization.Away g), e.commutes]
      show (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom ((secMap s V).hom r) =
        (secMap s (X.basicOpen g)).hom r
      rw [← CommRingCat.comp_apply]
      have key := Scheme.Hom.appLE_map s (U := ⊤) (V := V) (V' := X.basicOpen g) le_top
        (homOfLE (X.basicOpen_le g)).op
      simp only [secMap, Category.assoc]
      exact congrArg (fun φ => ConcreteCategory.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ) r) key
    let tr : MvPolynomial (Fin d) R →+* Sec s W.1 := (e : Localization.Away g →+* Γ(X, X.basicOpen g)).comp g'
    refine ⟨d, { tr with commutes' := fun r => ?_ }, ?_⟩
    · show e (g' (MvPolynomial.C r)) = algebraMap R (Sec s W.1) r
      rw [← RingHom.comp_apply g' MvPolynomial.C, hg'C]
      exact hcompat r
    · exact RingHom.FormallyEtale.comp (fe_of_etale hg'e) he

theorem chart_inf (hs : IsSeparated s) (U V : Chart s) : ∃ W : Chart s, W.1.1 = U.1.1 ⊓ V.1.1 := by
  have ha : IsAffineOpen (U.1.1 ⊓ V.1.1) :=
    isAffineHom_diagonal_iff.1 (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _)
      _ le_top _ le_top U.1.2 V.1.2
  let W : X.affineOpens := ⟨_, ha⟩
  have hW : W.1 ≤ U.1.1 := inf_le_left
  have he := res_etale (s := s) hW
  obtain ⟨hf, d, t, ht⟩ := U.2
  refine ⟨⟨W, ?_, d, (Sec.res s hW).comp t, ht.comp (fe_of_etale he)⟩, rfl⟩
  have k := (RingHom.flat_algebraMap_iff.2 hf).comp (RingHom.Etale.iff_flat_and_formallyUnramified.1 he).1
  rw [AlgHom.comp_algebraMap] at k
  exact RingHom.flat_algebraMap_iff.1 k

theorem bas_le (U : X.affineOpens) : ⊤ ≤ (bas s U).x ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge

theorem bas_inN (U : Chart s) : InN κ (bas s U.1) := by
  haveI : Module.Flat R (Sec s U.1.1) := U.2.1
  obtain ⟨δ, hδ⟩ := flatExt R (Sec s U.1.1) I κ
  refine ExtDP.of_eq (κ := κ) δ (bot_sup_eq _).symm ⟨by simp, fun {n} a ha => ?_⟩ hδ
  rw [Ideal.mem_bot] at ha
  subst ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [RingHom.id_apply, RingHom.id_apply, DividedPowers.dpow_zero _ (Ideal.zero_mem _),
      DividedPowers.dpow_zero _ (Ideal.zero_mem _)]
  · rw [RingHom.id_apply, RingHom.id_apply, DividedPowers.dpow_eval_zero _ hn.ne',
      DividedPowers.dpow_eval_zero _ hn.ne']

theorem eq_of_affPt (U : X.affineOpens) {B : Type} [CommRing B] {f g : Sec s U.1 →+* B}
    (h : spMap f ≫ affPt s U = spMap g ≫ affPt s U) : f = g := by
  have h1 : spMap f = spMap g := (cancel_mono (affPt s U)).1 h
  have h2 : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

theorem exists_hom_of_le (U : X.affineOpens) {B : Type} [CommRing B] (x : Sp B ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U.1) :
    ∃ f : Sec s U.1 →+* B, spMap f ≫ affPt s U = x := by
  have hr : Set.range x ⊆ Set.range (affPt s U) := by
    rintro _ ⟨p, rfl⟩
    have hp : p ∈ x ⁻¹ᵁ U.1 := h trivial
    show _ ∈ Set.range U.2.fromSpec
    rw [U.2.range_fromSpec]
    exact hp
  let y := IsOpenImmersion.lift (affPt s U) x hr
  refine ⟨(Spec.preimage y).hom, ?_⟩
  have e : spMap (Spec.preimage y).hom = y := Spec.map_preimage y
  rw [e]
  exact IsOpenImmersion.lift_fac _ _ _

theorem exists_lift_of_coord (U : X.affineOpens) {d : ℕ} (t : MvPolynomial (Fin d) R →ₐ[R] Sec s U.1)
    (ht : t.toRingHom.FormallyEtale) (T : Thick (dp0 R) s) (f : Sec s U.1 →+* T.B₀) (hf : spMap f ≫ affPt s U = T.x)
    (z : Fin d → T.B) (hz : ∀ k, T.π (z k) = f (t (MvPolynomial.X k))) :
    ∃ j : bas s U ⟶ T, ∀ k, j.φ (t (MvPolynomial.X k)) = z k := by
  have hw : affPt s U ≫ s = spMap (algebraMap R (Sec s U.1)) := (bas s U).w
  have hsp : spMap (f.comp (algebraMap R (Sec s U.1))) = spMap (T.π.comp (algebraMap R T.B)) := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← hw, ← Category.assoc, hf, T.w]
  have hR : f.comp (algebraMap R (Sec s U.1)) = T.π.comp (algebraMap R T.B) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective hsp)
  let u : MvPolynomial (Fin d) R →ₐ[R] T.B := MvPolynomial.aeval z
  have hfu : f.comp t.toRingHom = T.π.comp u.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := RingHom.congr_fun hR r
      show f (t (MvPolynomial.C r)) = T.π (u (MvPolynomial.C r))
      rw [← MvPolynomial.algebraMap_eq, t.commutes, u.commutes]
      exact h1
    · intro k
      show f (t (MvPolynomial.X k)) = T.π (u (MvPolynomial.X k))
      rw [MvPolynomial.aeval_X]
      exact (hz k).symm
  obtain ⟨g, hg1, hg2⟩ := fe_lift t.toRingHom ht T.π T.surj (nil_ker T) u.toRingHom f hfu
  let φ : Sec s U.1 →ₐ[R] T.B :=
    { g with
      commutes' := fun r => by
        have h1 := RingHom.congr_fun hg1 (algebraMap R (MvPolynomial (Fin d) R) r)
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes] at h1
        exact h1 }
  have hφ : spMap (T.π.comp (φ : Sec s U.1 →+* T.B)) ≫ affPt s U = T.x := by
    have e : T.π.comp (φ : Sec s U.1 →+* T.B) = f := hg2
    rw [e, hf]
  refine ⟨Thick.trivHom φ hφ, fun k => ?_⟩
  have h1 := RingHom.congr_fun hg1 (MvPolynomial.X k)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [MvPolynomial.aeval_X] at h1
  exact h1

theorem exists_lift (U : Chart s) (T : Thick (dp0 R) s) (h : ⊤ ≤ T.x ⁻¹ᵁ U.1.1) : Nonempty (bas s U.1 ⟶ T) := by
  obtain ⟨-, d, t, ht⟩ := U.2
  obtain ⟨f, hf⟩ := exists_hom_of_le (s := s) U.1 T.x h
  choose z hz using fun k ↦ T.surj (f (t (MvPolynomial.X k)))
  exact ⟨(exists_lift_of_coord U.1 t ht T f hf z hz).choose⟩

theorem π_eq (U : X.affineOpens) {T : Thick (dp0 R) s} (a b : bas s U ⟶ T) (c : Sec s U.1) :
    T.π (a.φ c) = T.π (b.φ c) :=
  (a.comm c).symm.trans ((RingHom.congr_fun (eq_of_affPt U (a.pt.trans b.pt.symm)) c).trans (b.comm c))

theorem lift_ext (U : X.affineOpens) {d : ℕ} (t : MvPolynomial (Fin d) R →ₐ[R] Sec s U.1)
    (ht : t.toRingHom.FormallyEtale) {T : Thick (dp0 R) s} (a b : bas s U ⟶ T)
    (h : ∀ k, a.φ (t (MvPolynomial.X k)) = b.φ (t (MvPolynomial.X k))) : a = b := by
  have e1 : (a.φ.comp t : MvPolynomial (Fin d) R →ₐ[R] T.B) = b.φ.comp t :=
    MvPolynomial.algHom_ext (fun k => h k)
  have key := fe_uniq t.toRingHom ht T.π (nil_ker T) (a.φ : Sec s U.1 →+* T.B) (b.φ : Sec s U.1 →+* T.B)
    (RingHom.ext fun p => AlgHom.congr_fun e1 p) (RingHom.ext fun c => π_eq U a b c)
  apply Thick.hom_ext
  intro c
  exact RingHom.congr_fun key c

theorem exists_coprod (U : Chart s) (S : Thick (dp0 R) s) (hS : InN κ S) (h : ⊤ ≤ S.x ⁻¹ᵁ U.1.1) (n : ℕ)
    (hn : 1 ≤ n) : ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (j : bas s U.1 ⟶ P), InN κ P ∧ IsLev P.δ n ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (b : bas s U.1 ⟶ V),
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ j ≫ ψ = b := by
  obtain ⟨-, d, t, ht⟩ := U.2
  obtain ⟨fS, hfS⟩ := @exists_hom_of_le R _ X s U.1 S.B₀ S.ring₀ S.x h
  choose zS hzS using fun k : Fin d => S.surj (fS (t (MvPolynomial.X k)))
  obtain ⟨jS, -⟩ := exists_lift_of_coord U.1 t ht S fS hfS zS hzS
  obtain ⟨P, i, y, hP, hlev, hy, huniv⟩ := exists_adj S hS d n hn
  have hbπ : ∀ {T : Thick (dp0 R) s} (a : bas s U.1 ⟶ T) (c : Sec s U.1.1), T.π (a.φ c) = a.φ₀ c :=
    fun a c => (a.comm c).symm
  have hyπ : ∀ k, P.π (y k) = 0 := fun k => (P.ker _).2 (hy k)
  obtain ⟨j, hj⟩ := exists_lift_of_coord U.1 t ht P (jS ≫ i).φ₀ (jS ≫ i).pt
    (fun k => (jS ≫ i).φ (t (MvPolynomial.X k)) + y k)
    (fun k => by
      simp only []
      rw [map_add, hyπ, add_zero, hbπ])
  refine ⟨P, i, j, hP, hlev, fun V hV φ b => ?_⟩
  have hiψ : ∀ (ψ : P ⟶ V), i ≫ ψ = φ → ∀ x, ψ.φ (i.φ x) = φ.φ x := by
    intro ψ e x
    rw [← Thick.comp_φ, e]
  let zV : Fin d → V.B := fun k => b.φ (t (MvPolynomial.X k)) - (jS ≫ φ).φ (t (MvPolynomial.X k))
  have hzV : ∀ k, zV k ∈ V.J := fun k => by
    refine (V.ker _).1 ?_
    simp only [zV, map_sub]
    exact sub_eq_zero.2 (π_eq U.1 b (jS ≫ φ) _)
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := huniv V hV φ zV hzV
  refine ⟨ψ, ⟨hψ1, ?_⟩, ?_⟩
  · apply lift_ext U.1 t ht
    intro k
    rw [Thick.comp_φ, hj k, map_add, hψ2]
    simp only [zV]
    rw [Thick.comp_φ jS i, Thick.comp_φ jS φ, hiψ ψ hψ1]
    ring
  · rintro ψ' ⟨h1, h2⟩
    apply hψu
    refine ⟨h1, fun k => ?_⟩
    have e1 : ψ'.φ (j.φ (t (MvPolynomial.X k))) = b.φ (t (MvPolynomial.X k)) := by
      rw [← Thick.comp_φ, h2]
    rw [hj k, map_add, Thick.comp_φ jS i, hiψ ψ' h1] at e1
    simp only [zV]
    rw [Thick.comp_φ jS φ, ← e1]
    ring

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh

namespace FubiniStudyChowHeightFormula₂.Adr

universe v u v' u'

def Acyc (R : Type) [CommRing R] (D : Type u) [Category.{v} D] : Prop :=
  Nonempty D ∧ ∀ M : CommAlgCat.{0} R, (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a b, g a = g b) ∧
    (∀ c : H1 ((Functor.const D).obj M), c = 0) ∧ ∀ c : H2 ((Functor.const D).obj M), c = 0

section Contract

variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D]

def cm (M : CommAlgCat.{0} R) (G : D ⥤ D) :
    CoefMap (RingHom.id R) ((Functor.const D).obj M) ((Functor.const D).obj M) where
  G := G
  α _ := RingHom.id M
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem cm_zigzag (M : CommAlgCat.{0} R) {G G' : D ⥤ D} (h : Zigzag G G') :
    (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a, g (G.obj a) = g (G'.obj a)) ∧
    (∀ c, (cm M G).pull1 c = (cm M G').pull1 c) ∧ ∀ c, (cm M G).pull2 c = (cm M G').pull2 c := by
  have one : ∀ {G G' : D ⥤ D} (_ : G ⟶ G'),
      (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a, g (G.obj a) = g (G'.obj a)) ∧
      (∀ c, (cm M G).pull1 c = (cm M G').pull1 c) ∧ ∀ c, (cm M G).pull2 c = (cm M G').pull2 c :=
    fun {G G'} θ ↦ ⟨fun g hg a ↦ (hg _ _ (θ.app a)).symm,
      (cm M G).pullCohomologyOne_eq_of_natTrans (cm M G') θ fun _ _ ↦ rfl,
      (cm M G).pullCohomologyTwo_eq_of_natTrans (cm M G') θ fun _ _ ↦ rfl⟩
  induction h with
  | refl => exact ⟨fun _ _ _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  | tail _ hz ih =>
    rcases hz with ⟨⟨θ⟩⟩ | ⟨⟨θ⟩⟩
    · exact ⟨fun g hg a ↦ (ih.1 g hg a).trans ((one θ).1 g hg a), fun c ↦ (ih.2.1 c).trans ((one θ).2.1 c),
        fun c ↦ (ih.2.2 c).trans ((one θ).2.2 c)⟩
    · exact ⟨fun g hg a ↦ (ih.1 g hg a).trans ((one θ).1 g hg a).symm,
        fun c ↦ (ih.2.1 c).trans ((one θ).2.1 c).symm, fun c ↦ (ih.2.2 c).trans ((one θ).2.2 c).symm⟩

theorem acyc_of_zigzag (d : D) (h : Zigzag (𝟭 D) ((Functor.const D).obj d)) : Acyc R D := by
  refine ⟨⟨d⟩, fun M ↦ ?_⟩
  obtain ⟨h0, h1, h2⟩ := cm_zigzag M h
  refine ⟨fun g hg a b ↦ (h0 g hg a).trans (h0 g hg b).symm, fun c ↦ ?_, fun c ↦ ?_⟩
  · refine ((CoefMap.pullCohomologyOne_id c).symm.trans (h1 c)).trans ?_
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    funext T T' φ
    exact (Z1.id f d).symm
  · refine ((CoefMap.pullCohomologyTwo_id c).symm.trans (h2 c)).trans ?_
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    refine ⟨fun _ _ _ ↦ (z.1 d d d (𝟙 d) (𝟙 d) : M), ?_⟩
    funext T T' T'' φ ψ
    exact sub_add_cancel (z.1 d d d (𝟙 d) (𝟙 d) : M) (z.1 d d d (𝟙 d) (𝟙 d) : M)

theorem acyc_of_coprod (d : D) (P : D → D) (i : ∀ a, a ⟶ P a) (j : ∀ a, d ⟶ P a)
    (h : ∀ a b (φ : a ⟶ P b), ∃! ψ : P a ⟶ P b, i a ≫ ψ = φ ∧ j a ≫ ψ = j b) : Acyc R D := by
  choose m hm hu using h
  let Q : D ⥤ D :=
    { obj := P
      map := fun {a b} φ ↦ m a b (φ ≫ i b)
      map_id := fun a ↦ (hu a a _ (𝟙 _) ⟨by simp, by simp⟩).symm
      map_comp := fun {a b c} φ ψ ↦ (hu a c _ _ ⟨by
        rw [← Category.assoc, (hm a b _).1, Category.assoc, (hm b c _).1, Category.assoc], by
        rw [← Category.assoc, (hm a b _).2, (hm b c _).2]⟩).symm }
  let θ : 𝟭 D ⟶ Q := { app := i, naturality := fun a b φ ↦ (hm a b _).1.symm }
  let η : (Functor.const D).obj d ⟶ Q :=
    { app := j, naturality := fun a b φ ↦ (Category.id_comp _).trans (hm a b _).2.symm }
  exact acyc_of_zigzag d ((Zigzag.of_hom θ).trans (Zigzag.of_inv η))

end Contract

section Comma

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {G : C' ⥤ C} {T : C}

theorem Acyc.zero (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R) (g : ∀ S, (G.obj S ⟶ T) → M)
    (hg : ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), g S (G.map ψ ≫ c) = g S' c) : ∃ m, ∀ S c, g S c = m := by
  obtain ⟨⟨a⟩, h⟩ := h
  refine ⟨g a.left a.hom, fun S c ↦ (h M).1 (fun b ↦ g b.left b.hom) (fun b b' φ ↦ ?_) (CostructuredArrow.mk c) a⟩
  exact (hg _ _ φ.left b'.hom).symm.trans (congrArg _ (CostructuredArrow.w φ))

theorem Acyc.one (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R)
    (f : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M)
    (hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      f S S'' (φ ≫ ψ) c = f S S' φ (G.map ψ ≫ c) + f S' S'' ψ c) :
    ∃ v : ∀ S, (G.obj S ⟶ T) → M, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), f S S' ψ c = v S' c - v S (G.map ψ ≫ c) := by
  let f' : Z1 ((Functor.const (CostructuredArrow G T)).obj M) :=
    ⟨fun a b φ ↦ (f a.left b.left φ.left b.hom : M), fun a b c φ ψ ↦
      (hf _ _ _ φ.left ψ.left c.hom).trans
        (congrArg (fun t ↦ f _ _ φ.left t + f _ _ ψ.left c.hom) (CostructuredArrow.w ψ))⟩
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 ((h.2 M).2.1 (H1.mk _ f'))
  exact ⟨fun S c ↦ g (CostructuredArrow.mk c), fun S S' ψ c ↦
    (congrFun (congrFun (congrFun hg (CostructuredArrow.mk (G.map ψ ≫ c))) (CostructuredArrow.mk c))
      (CostructuredArrow.homMk ψ rfl)).symm⟩

theorem Acyc.two (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R)
    (z : ∀ S S' S'', (S ⟶ S') → (S' ⟶ S'') → (G.obj S'' ⟶ T) → M)
    (hz : ∀ S S' S'' S''' (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S'' ⟶ S''') (c : G.obj S''' ⟶ T),
      z S S' S'' φ ψ (G.map χ ≫ c) + z S S'' S''' (φ ≫ ψ) χ c = z S S' S''' φ (ψ ≫ χ) c + z S' S'' S''' ψ χ c) :
    ∃ w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M, ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      z S S' S'' φ ψ c = w S S' φ (G.map ψ ≫ c) - w S S'' (φ ≫ ψ) c + w S' S'' ψ c := by
  let z' : Z2 ((Functor.const (CostructuredArrow G T)).obj M) :=
    ⟨fun a b c φ ψ ↦ (z a.left b.left c.left φ.left ψ.left c.hom : M), fun a b c e φ ψ χ ↦
      (congrArg (fun t ↦ z _ _ _ φ.left ψ.left t + z _ _ _ (φ.left ≫ ψ.left) χ.left e.hom)
        (CostructuredArrow.w χ)).symm.trans (hz _ _ _ _ φ.left ψ.left χ.left e.hom)⟩
  obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 ((h.2 M).2.2 (H2.mk _ z'))
  let w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M := fun S S' ψ c ↦
    g (CostructuredArrow.mk (G.map ψ ≫ c)) (CostructuredArrow.mk c) (CostructuredArrow.homMk ψ rfl)
  have hw : ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T) (c₀ : G.obj S ⟶ T) (e : G.map ψ ≫ c = c₀),
      (g (CostructuredArrow.mk c₀) (CostructuredArrow.mk c) (CostructuredArrow.homMk ψ e) : M) = w S S' ψ c := by
    intro S S' ψ c c₀ e
    subst e
    rfl
  refine ⟨w, fun S S' S'' φ ψ c ↦ ?_⟩
  have k := congrFun (congrFun (congrFun (congrFun (congrFun hg
    (CostructuredArrow.mk (G.map φ ≫ G.map ψ ≫ c))) (CostructuredArrow.mk (G.map ψ ≫ c))) (CostructuredArrow.mk c))
      (CostructuredArrow.homMk φ rfl)) (CostructuredArrow.homMk ψ rfl)
  rw [← hw S S'' (φ ≫ ψ) c (G.map φ ≫ G.map ψ ≫ c) (by simp)]
  exact k.symm

end Comma

section QA

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

theorem qa1 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (h : ∀ T, Acyc R (CostructuredArrow G T)) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let g' : ∀ S, F.obj (G.obj S) := g
    have hg' : ∀ S S' (ψ : S ⟶ S'), f.1 _ _ (G.map ψ) = g' S' - mp F (G.map ψ) (g' S) := fun S S' ψ ↦
      (congrFun (congrFun (congrFun hg S) S') ψ).symm
    have ex : ∀ T, ∃ m : F.obj T, ∀ S (c : G.obj S ⟶ T), f.1 _ _ c + mp F c (g' S) = m := fun T ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        simp only [Z1.comp f, hg', mp_comp, map_sub]; ring
    choose m hm using ex
    refine H1.mk_eq_zero.2 ⟨m, ?_⟩
    funext T T' φ
    obtain ⟨a⟩ := (h T).1
    let c : G.obj a.left ⟶ T := a.hom
    rw [amitsur_d0_apply, ← hm T _ c, ← hm T' _ (c ≫ φ)]
    simp only [Z1.comp f, mp_comp, map_add]; ring
  · intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    let f' : ∀ S S', (S ⟶ S') → F.obj (G.obj S') := f.1
    have hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S''),
        f' S S'' (φ ≫ ψ) = mp F (G.map ψ) (f' S S' φ) + f' S' S'' ψ := fun S S' S'' φ ψ ↦ f.2 φ ψ
    have ex : ∀ T, ∃ v : ∀ S, (G.obj S ⟶ T) → F.obj T, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        -mp F c (f' S S' ψ) = v S' c - v S (G.map ψ ≫ c) := fun T ↦
      (h T).one _ (fun S S' ψ c ↦ -mp F c (f' S S' ψ)) fun S S' S'' φ ψ c ↦ by
        simp only [hf, mp_comp, map_add]; ring
    choose v hv using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ m : F.obj T', ∀ S (c : G.obj S ⟶ T),
        v T' S (c ≫ φ) - mp F φ (v T S c) = m := fun T T' φ ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e1 := hv T' S S' ψ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hv T S S' ψ c)
        simp only [mp_comp, map_sub, map_neg, Category.assoc] at e1 e2 ⊢
        linear_combination e1 - e2
    choose m hm using ex
    refine ⟨H1.mk _ ⟨m, fun T T' T'' φ ψ ↦ ?_⟩, ?_⟩
    · obtain ⟨a⟩ := (h T).1
      let c : G.obj a.left ⟶ T := a.hom
      rw [← hm T T'' _ _ c, ← hm T T' _ _ c, ← hm T' T'' _ _ (c ≫ φ)]
      simp only [mp_comp, map_sub, Category.assoc]; ring
    · rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
      refine ⟨fun S ↦ v _ S (𝟙 _), ?_⟩
      funext S S' ψ
      have e1 := hm _ _ (G.map ψ) S (𝟙 _)
      have e2 := hv _ S S' ψ (𝟙 _)
      rw [Category.id_comp] at e1
      rw [Category.comp_id, mp_id] at e2
      change v _ S' (𝟙 _) - mp F (G.map ψ) (v _ S (𝟙 _)) = m _ _ (G.map ψ) - f' S S' ψ
      linear_combination e1 - e2

theorem qa2 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (h : ∀ T, Acyc R (CostructuredArrow G T)) :
    Function.Bijective (CoefMap.restrict F G).pull2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let f : ∀ S S', (S ⟶ S') → F.obj (G.obj S') := g
    have hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S''), z.1 _ _ _ (G.map φ) (G.map ψ) =
        mp F (G.map ψ) (f S S' φ) - f S S'' (φ ≫ ψ) + f S' S'' ψ := fun S S' S'' φ ψ ↦
      (congrFun (congrFun (congrFun (congrFun (congrFun hg S) S') S'') φ) ψ).symm
    have ex : ∀ T, ∃ v : ∀ S, (G.obj S ⟶ T) → F.obj T, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        z.1 _ _ _ (G.map ψ) c - mp F c (f S S' ψ) = v S' c - v S (G.map ψ ≫ c) := fun T ↦
      (h T).one _ (fun S S' ψ c ↦ z.1 _ _ _ (G.map ψ) c - mp F c (f S S' ψ)) fun S S' S'' φ ψ c ↦ by
        have e := z.2 (G.map φ) (G.map ψ) c
        simp only [hf, mp_comp, map_add, map_sub, Functor.map_comp] at e ⊢
        linear_combination e
    choose v hv using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ m : F.obj T', ∀ S (c : G.obj S ⟶ T),
        z.1 _ _ _ c φ - mp F φ (v T S c) + v T' S (c ≫ φ) = m := fun T T' φ ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e := z.2 (G.map ψ) c φ
        have e1 := hv T' S S' ψ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hv T S S' ψ c)
        simp only [mp_comp, map_sub, Category.assoc] at e1 e2 ⊢
        linear_combination e + e1 - e2
    choose m hm using ex
    refine H2.mk_eq_zero.2 ⟨m, ?_⟩
    funext T T' T'' φ ψ
    obtain ⟨a⟩ := (h T).1
    let c : G.obj a.left ⟶ T := a.hom
    have e := z.2 c φ ψ
    rw [d1_apply, ← hm T T'' _ _ c, ← hm T T' _ _ c, ← hm T' T'' _ _ (c ≫ φ)]
    simp only [mp_comp, map_sub, map_add, Category.assoc]
    linear_combination e
  · intro c
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    let y : ∀ S S' S'', (S ⟶ S') → (S' ⟶ S'') → F.obj (G.obj S'') := z.1
    have hy : ∀ S S' S'' S''' (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S'' ⟶ S'''),
        mp F (G.map χ) (y _ _ _ φ ψ) + y _ _ _ (φ ≫ ψ) χ = y _ _ _ φ (ψ ≫ χ) + y _ _ _ ψ χ :=
      fun S S' S'' S''' φ ψ χ ↦ z.2 φ ψ χ
    have ex : ∀ T, ∃ w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → F.obj T,
        ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
          mp F c (y _ _ _ φ ψ) = w S S' φ (G.map ψ ≫ c) - w S S'' (φ ≫ ψ) c + w S' S'' ψ c := fun T ↦
      (h T).two _ (fun S S' S'' φ ψ c ↦ mp F c (y _ _ _ φ ψ)) fun S S' S'' S''' φ ψ χ c ↦ by
        simp only [mp_comp, ← map_add, hy]
    choose w hw using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ x : ∀ S, (G.obj S ⟶ T) → F.obj T', ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        mp F φ (w T S S' ψ c) - w T' S S' ψ (c ≫ φ) = x S' c - x S (G.map ψ ≫ c) := fun T T' φ ↦
      (h T).one _ (fun S S' ψ c ↦ mp F φ (w T S S' ψ c) - w T' S S' ψ (c ≫ φ)) fun S S' S'' ψ χ c ↦ by
        have e1 := hw T' S S' S'' ψ χ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hw T S S' S'' ψ χ c)
        simp only [mp_comp, map_sub, map_add, Category.assoc] at e1 e2 ⊢
        linear_combination e2 - e1
    choose x hx using ex
    have ex : ∀ T T' T'' (φ : T ⟶ T') (φ' : T' ⟶ T''), ∃ m : F.obj T'', ∀ S (c : G.obj S ⟶ T),
        mp F φ' (x T T' φ S c) + x T' T'' φ' S (c ≫ φ) - x T T'' (φ ≫ φ') S c = m := fun T T' T'' φ φ' ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e1 := congrArg (mp F φ') (hx T T' φ S S' ψ c)
        have e2 := hx T' T'' φ' S S' ψ (c ≫ φ)
        have e3 := hx T T'' (φ ≫ φ') S S' ψ c
        simp only [mp_comp, map_sub, Category.assoc] at e1 e2 e3 ⊢
        linear_combination e1 + e2 - e3
    choose m hm using ex
    refine ⟨H2.mk _ ⟨m, fun T T' T'' T''' φ ψ χ ↦ ?_⟩, ?_⟩
    · obtain ⟨a⟩ := (h T).1
      let c : G.obj a.left ⟶ T := a.hom
      rw [← hm T T' T'' _ _ _ c, ← hm T T'' T''' _ _ _ c, ← hm T T' T''' _ _ _ c, ← hm T' T'' T''' _ _ _ (c ≫ φ)]
      simp only [mp_comp, map_sub, map_add, Category.assoc]; ring
    · rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
      refine ⟨fun S S' ψ ↦ x _ _ (G.map ψ) S (𝟙 _) - w _ S S' ψ (𝟙 _), ?_⟩
      funext S S' S'' φ ψ
      have e1 := hm _ _ _ (G.map φ) (G.map ψ) S (𝟙 _)
      have e2 := hw _ S S' S'' φ ψ (𝟙 _)
      have e3 := hx _ _ (G.map ψ) S S' φ (𝟙 _)
      rw [Category.id_comp] at e1 e3
      rw [Category.comp_id] at e2 e3
      rw [mp_id] at e2
      change mp F (G.map ψ) (x _ _ (G.map φ) S (𝟙 _) - w _ S S' φ (𝟙 _)) -
        (x _ _ (G.map (φ ≫ ψ)) S (𝟙 _) - w _ S S'' (φ ≫ ψ) (𝟙 _)) + (x _ _ (G.map ψ) S' (𝟙 _) - w _ S' S'' ψ (𝟙 _)) =
        m _ _ _ (G.map φ) (G.map ψ) - y _ _ _ φ ψ
      rw [map_sub, G.map_comp]
      linear_combination e1 + e2 - e3

end QA

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

universe v u v' u' v'' u''

section General

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {C'' : Type u''} [Category.{v''} C'']

theorem restrict_pull1 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C'' ⥤ C') (c : GlobalTheory.CatCoh.H1 F) :
    (CoefMap.restrict (G ⋙ F) H).pull1 ((CoefMap.restrict F G).pull1 c) =
      (CoefMap.restrict F (H ⋙ G)).pull1 c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b => by simp [CoefMap.comp, CoefMap.restrict, mp] <;> rfl) c

theorem restrict_pull2 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C'' ⥤ C') (c : GlobalTheory.CatCoh.H2 F) :
    (CoefMap.restrict (G ⋙ F) H).pull2 ((CoefMap.restrict F G).pull2 c) =
      (CoefMap.restrict F (H ⋙ G)).pull2 c := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 _) (fun T b => by simp [CoefMap.comp, CoefMap.restrict, mp] <;> rfl) c

end General

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {γ : DividedPowers I} {s : X ⟶ Sp R} {K : Type} {U : K → X.Opens}

def toSmall (γ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) :
    Tag γ s U ⥤ (IsSmall γ s U).FullSubcategory where
  obj S := ⟨S.T, S.k, S.le⟩
  map f := ⟨f.f⟩

section Comma

variable {T : (IsSmall γ s U).FullSubcategory}

theorem comma_le (a : CostructuredArrow (toSmall γ s U) T) : ⊤ ≤ T.obj.x ⁻¹ᵁ U a.left.k :=
  Thick.Hom.le_preimage a.hom.hom a.left.le

def selfObj (k : K) (h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k) : CostructuredArrow (toSmall γ s U) T :=
  CostructuredArrow.mk (Y := (⟨T.obj, k, h⟩ : Tag γ s U)) (𝟙 T)

def toSelf (a : CostructuredArrow (toSmall γ s U) T) (k : K) (h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k)
    (e : U a.left.k ≤ U k) : a ⟶ selfObj k h :=
  CostructuredArrow.homMk (⟨a.hom.hom, e⟩ : Tag.Hom _ _) (Category.comp_id _)

theorem toSelf_unique {a : CostructuredArrow (toSmall γ s U) T} {k : K} {h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k}
    (f g : a ⟶ selfObj k h) : f = g := by
  have hf := CostructuredArrow.w f
  have hg := CostructuredArrow.w g
  apply CostructuredArrow.hom_ext
  revert hf hg
  rcases f with ⟨⟨f1, l1⟩, fr, fw⟩
  rcases g with ⟨⟨g1, l2⟩, gr, gw⟩
  intro hf hg
  simp [selfObj, toSmall] at hf hg ⊢
  have e : f1 = g1 := congrArg (fun q => q.hom) (hf.trans hg.symm)
  subst e
  rfl

def selfFun (m : CostructuredArrow (toSmall γ s U) T → K) (h : ∀ a, ⊤ ≤ T.obj.x ⁻¹ᵁ U (m a))
    (mono : ∀ a b, (a ⟶ b) → U (m a) ≤ U (m b)) :
    CostructuredArrow (toSmall γ s U) T ⥤ CostructuredArrow (toSmall γ s U) T where
  obj a := selfObj (m a) (h a)
  map {a b} f := toSelf _ _ _ (mono a b f)
  map_id _ := toSelf_unique _ _
  map_comp _ _ := toSelf_unique _ _

private theorem pull1_restrict_const_eq_of_natTrans {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (Φ Ψ : D ⥤ D)
    (θ : Φ ⟶ Ψ) (c : GlobalTheory.CatCoh.H1 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) Φ).pull1 c =
      (CoefMap.restrict ((Functor.const D).obj M) Ψ).pull1 c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.restrict ((Functor.const D).obj M) Φ)
    (CoefMap.restrict ((Functor.const D).obj M) Ψ :
      CoefMap (RingHom.id R) ((Functor.const D).obj M) (Φ ⋙ (Functor.const D).obj M))
    θ (fun _ _ => rfl) c

private theorem pull2_restrict_const_eq_of_natTrans {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (Φ Ψ : D ⥤ D)
    (θ : Φ ⟶ Ψ) (c : GlobalTheory.CatCoh.H2 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) Φ).pull2 c =
      (CoefMap.restrict ((Functor.const D).obj M) Ψ).pull2 c :=
  CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.restrict ((Functor.const D).obj M) Φ)
    (CoefMap.restrict ((Functor.const D).obj M) Ψ :
      CoefMap (RingHom.id R) ((Functor.const D).obj M) (Φ ⋙ (Functor.const D).obj M))
    θ (fun _ _ => rfl) c

private theorem pull1_restrict_id {D : Type u} [Category.{v} D] (F : D ⥤ CommAlgCat.{0} R)
    (c : GlobalTheory.CatCoh.H1 F) : (CoefMap.restrict F (𝟭 D)).pull1 c = c := by
  have e := CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.id F) (CoefMap.restrict F (𝟭 D)) (𝟙 _)
    (fun _ b => by simp [CoefMap.restrict, CoefMap.id, mp] <;> rfl) c
  rw [CoefMap.pullCohomologyOne_id] at e
  exact e.symm

private theorem pull2_restrict_id {D : Type u} [Category.{v} D] (F : D ⥤ CommAlgCat.{0} R)
    (c : GlobalTheory.CatCoh.H2 F) : (CoefMap.restrict F (𝟭 D)).pull2 c = c := by
  have e := CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.id F) (CoefMap.restrict F (𝟭 D)) (𝟙 _)
    (fun _ b => by simp [CoefMap.restrict, CoefMap.id, mp] <;> rfl) c
  rw [CoefMap.pullCohomologyTwo_id] at e
  exact e.symm

private theorem H2_discrete_punit_eq_zero (F : Discrete PUnit.{1} ⥤ CommAlgCat.{0} R) (c : GlobalTheory.CatCoh.H2 F) :
    c = 0 := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [H2.mk_eq_zero]
  refine ⟨fun a b φ => z.1 a b b φ (𝟙 b), ?_⟩
  funext a b d φ ψ
  rcases a with ⟨⟨⟩⟩
  rcases b with ⟨⟨⟩⟩
  rcases d with ⟨⟨⟩⟩
  obtain rfl : φ = 𝟙 _ := Subsingleton.elim _ _
  obtain rfl : ψ = 𝟙 _ := Subsingleton.elim _ _
  simp [d1_apply, mp]

private theorem pull1_restrict_const_const_eq_zero {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (x : D)
    (c : GlobalTheory.CatCoh.H1 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) ((Functor.const D).obj x)).pull1 c = 0 := by
  have e := restrict_pull1 ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)
    ((Functor.const D).obj ⟨⟨⟩⟩) c
  rw [H1.eq_zero_of_isInitial _ (T₀ := (⟨⟨⟩⟩ : Discrete PUnit.{1}))
    (Limits.IsInitial.ofUniqueHom (fun _ => Discrete.eqToHom (Subsingleton.elim _ _))
      (fun _ _ => Subsingleton.elim _ _))
    ((CoefMap.restrict ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)).pull1 c),
    map_zero] at e
  exact e.symm

private theorem pull2_restrict_const_const_eq_zero {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (x : D)
    (c : GlobalTheory.CatCoh.H2 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) ((Functor.const D).obj x)).pull2 c = 0 := by
  have e := restrict_pull2 ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)
    ((Functor.const D).obj ⟨⟨⟩⟩) c
  rw [H2_discrete_punit_eq_zero _
    ((CoefMap.restrict ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)).pull2 c),
    map_zero] at e
  exact e.symm

theorem acyc_toSmall (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) (T : (IsSmall γ s U).FullSubcategory) :
    Acyc R (CostructuredArrow (toSmall γ s U) T) := by
  obtain ⟨k0, h0⟩ := T.property
  choose m2 hm2 using fun (a : CostructuredArrow (toSmall γ s U) T) => hinf a.left.k k0
  have h2 : ∀ a, ⊤ ≤ T.obj.x ⁻¹ᵁ U (m2 a) := by
    intro a
    rw [hm2 a]
    intro p hp
    exact ⟨comma_le a hp, h0 hp⟩
  let S1 := selfFun (T := T) (fun a => a.left.k) comma_le (fun a b f => Tag.Hom.le f.left)
  let S2 := selfFun (T := T) m2 h2 (fun a b f => by
    rw [hm2 a, hm2 b]
    exact inf_le_inf_right _ (Tag.Hom.le f.left))
  let θ1 : 𝟭 _ ⟶ S1 :=
    { app := fun a => toSelf a _ (comma_le a) le_rfl
      naturality := fun _ _ _ => toSelf_unique _ _ }
  let θ2 : S2 ⟶ S1 :=
    { app := fun a => toSelf (selfObj (m2 a) (h2 a)) a.left.k (comma_le a)
        (show U (m2 a) ≤ U a.left.k by rw [hm2 a]; exact inf_le_left)
      naturality := fun _ _ _ => toSelf_unique _ _ }
  let θ3 : S2 ⟶ (Functor.const _).obj (selfObj k0 h0) :=
    { app := fun a => toSelf (selfObj (m2 a) (h2 a)) k0 h0
        (show U (m2 a) ≤ U k0 by rw [hm2 a]; exact inf_le_right)
      naturality := fun _ _ _ => toSelf_unique (k := k0) (h := h0) _ _ }
  refine ⟨⟨selfObj k0 h0⟩, fun M => ⟨?_, ?_, ?_⟩⟩
  · intro g hg
    have key : ∀ a, g a = g (selfObj k0 h0) := fun a =>
      (hg _ _ (θ1.app a)).symm.trans ((hg _ _ (θ2.app a)).trans (hg _ _ (θ3.app a)).symm)
    intro a b
    exact (key a).trans (key b).symm
  · intro c
    exact (pull1_restrict_id _ c).symm.trans ((pull1_restrict_const_eq_of_natTrans M _ _ θ1 c).trans
      ((pull1_restrict_const_eq_of_natTrans M _ _ θ2 c).symm.trans ((pull1_restrict_const_eq_of_natTrans M _ _ θ3 c).trans
        (pull1_restrict_const_const_eq_zero M _ c))))
  · intro c
    exact (pull2_restrict_id _ c).symm.trans ((pull2_restrict_const_eq_of_natTrans M _ _ θ1 c).trans
      ((pull2_restrict_const_eq_of_natTrans M _ _ θ2 c).symm.trans ((pull2_restrict_const_eq_of_natTrans M _ _ θ3 c).trans
        (pull2_restrict_const_const_eq_zero M _ c))))

end Comma

theorem tag_pull1 (hcov : ⨆ k, U k = ⊤) (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) :
    Function.Bijective (CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull1 := by
  have key : ⇑(CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull1 =
      ⇑(CoefMap.restrict ((IsSmall γ s U).ι ⋙ O γ s) (toSmall γ s U)).pull1 ∘
        ⇑(CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull1 :=
    funext fun c => (restrict_pull1 (O γ s) (IsSmall γ s U).ι (toSmall γ s U) c).symm
  rw [key]
  exact (qa1 _ _ (fun T => acyc_toSmall hinf T)).comp
    (SmallDescent.pull1_bijective R I γ X s K U hcov)

private theorem pull2_restrict_isSmall_bijective_of_cover (hcov : ⨆ k, U k = ⊤) :
    Function.Bijective (CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull2 := by
  apply Desc.pull2_bijective
  · intro T b
    obtain ⟨L, l, hl⟩ := SmallDescent.exists_isLoc T b
    obtain ⟨hu, hsurj, hker, hfac⟩ := hl
    refine ⟨L, l, hu, ?_, hker, ?_⟩
    · intro y
      obtain ⟨n, N, h⟩ := hsurj y
      exact ⟨N, n, h⟩
    · intro S u hu'
      obtain ⟨ψ, hψ⟩ := hfac S u hu'
      exact ⟨ψ, hψ, fun ψ' h' =>
        SmallDescent.IsLoc.hom_ext ⟨hu, hsurj, hker, hfac⟩ (h'.trans hψ.symm)⟩
  · intro S S' a hS
    exact SmallDescent.isSmall_of_hom a hS
  · intro T
    obtain ⟨σ, hσ, hσs⟩ := SmallDescent.exists_cover hcov T
    refine ⟨σ.card, fun i => (σ.equivFin.symm i : T.B), ?_, ?_⟩
    · have hr : Set.range (fun i => (σ.equivFin.symm i : T.B)) = (σ : Set T.B) := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact (σ.equivFin.symm i).2
        · intro hx
          exact ⟨σ.equivFin ⟨x, hx⟩, by simp⟩
      rw [hr]
      exact hσ
    · intro i S u hu
      exact hσs _ (σ.equivFin.symm i).2 S u hu

theorem tag_pull2 (hcov : ⨆ k, U k = ⊤) (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) :
    Function.Bijective (CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull2 := by
  have key : ⇑(CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull2 =
      ⇑(CoefMap.restrict ((IsSmall γ s U).ι ⋙ O γ s) (toSmall γ s U)).pull2 ∘
        ⇑(CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull2 :=
    funext fun c => (restrict_pull2 (O γ s) (IsSmall γ s U).ι (toSmall γ s U) c).symm
  rw [key]
  exact (qa2 _ _ (fun T => acyc_toSmall hinf T)).comp (pull2_restrict_isSmall_bijective_of_cover hcov)

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}}

def NT (κ : DividedPowers I) {s : X ⟶ Sp R} {K : Type} (U : K → X.Opens) : ObjectProperty (Tag (dp0 R) s U) :=
  fun S ↦ InN κ S.T

theorem isDPMorphism_id {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) :
    IsDPMorphism δ δ (RingHom.id B) := (DPMorphism.id δ).isDPMorphism

structure Red (κ : DividedPowers I) {R₀ : Type} [CommRing R₀] (π : R →+* R₀) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀)
    (i : X₀ ⟶ X) : Prop where
  nil : IsNilDP κ
  surj : Function.Surjective π
  ker : RingHom.ker π = I
  pb : IsPullback i s₀ s (spMap π)

variable {κ : DividedPowers I} {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {s : X ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀}
  {i : X₀ ⟶ X} (h : Red κ π s s₀ i)

namespace Red

include h

theorem mor : IsMor (dp0 R) s κ (s₀ ≫ spMap π) (RingHom.id R) i := by
  refine IsMor.of_dividedPowersZeroIdeal κ ?_
  rw [GlobalTheory.Cris.spMap_id, Category.comp_id]
  exact h.pb.w

theorem surjective : Function.Surjective i := by
  have hnil : ∀ x ∈ I, ∃ N : ℕ, x ^ N = 0 := by
    intro x hx
    obtain ⟨N, hN⟩ := h.nil
    refine ⟨N, ?_⟩
    have := hN (List.replicate N (1, x))
      (by
        intro p hp
        rw [List.eq_of_mem_replicate hp]
        exact hx)
      (by simp)
    simpa [List.map_replicate, List.prod_replicate, κ.dpow_one hx] using this
  have hsurj : Function.Surjective (spMap π) := by
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap π) := by
      open PrimeSpectrum in rw [range_comap_of_surjective _ π h.surj, h.ker]
      change (I : Set R) ⊆ (p : PrimeSpectrum R).asIdeal
      intro x hx
      obtain ⟨N, hN⟩ := hnil x hx
      exact p.isPrime.mem_of_pow_mem N (by rw [hN]; exact p.asIdeal.zero_mem)
    exact hp
  have hS : AlgebraicGeometry.Surjective (spMap π) := (AlgebraicGeometry.surjective_iff _).mpr hsurj
  exact (AlgebraicGeometry.surjective_iff i).mp
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) h.pb.flip hS)

theorem le_of_le {U V : X.Opens} (e : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ V) : U ≤ V := by
  intro x hx
  obtain ⟨y, rfl⟩ := h.surjective x
  exact (show y ∈ i ⁻¹ᵁ V from e (show y ∈ i ⁻¹ᵁ U from hx))

theorem inN_obj (T : Thick κ (s₀ ≫ spMap π)) : InN κ (h.mor.obj T) := by
  show ∃ δ' : DividedPowers (T.J ⊔ Ideal.map (algebraMap R T.B) I),
    T.δ.IsDPMorphism δ' (RingHom.id T.B) ∧ κ.IsDPMorphism δ' (algebraMap R T.B)
  rw [sup_eq_left.mpr T.dp.ideal_comp]
  exact ⟨T.δ, isDPMorphism_id T.δ, T.dp⟩

end Red

section Up

variable (S : Thick (dp0 R) s)

abbrev big (I : Ideal R) : Ideal S.B := S.J ⊔ I.map (algebraMap R S.B)

def rho (I : Ideal R) : S.B₀ →+* S.B ⧸ big S I :=
  RingHom.liftOfSurjective S.π S.surj ⟨Ideal.Quotient.mk _, fun b hb ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left ((S.ker b).1 hb))⟩

theorem rho_π (I : Ideal R) (b : S.B) : rho S I (S.π b) = Ideal.Quotient.mk _ b :=
  RingHom.liftOfSurjective_comp_apply _ _ _ b

def Red.sig : R₀ →+* S.B ⧸ big S I :=
  RingHom.liftOfSurjective π h.surj ⟨(Ideal.Quotient.mk _).comp (algebraMap R S.B), fun r hr ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (h.ker ▸ hr)))⟩

theorem Red.sig_π (r : R) : h.sig S (π r) = Ideal.Quotient.mk _ (algebraMap R S.B r) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ r

def Red.pt : Sp (S.B ⧸ big S I) ⟶ X₀ :=
  h.pb.lift (spMap (rho S I) ≫ S.x) (spMap (h.sig S)) (by
    rw [Category.assoc, S.w, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ (rho_π S I _).trans (h.sig_π S r).symm)

theorem Red.pt_i : h.pt S ≫ i = spMap (rho S I) ≫ S.x := h.pb.lift_fst _ _ _

theorem Red.pt_s : h.pt S ≫ s₀ = spMap (h.sig S) := h.pb.lift_snd _ _ _

@[reducible] def Red.up (hS : InN κ S) : Thick κ (s₀ ≫ spMap π) where
  B := S.B
  J := big S I
  δ := hS.choose
  nil := nil_sup κ S.δ _ _ rfl hS.choose_spec.1 hS.choose_spec.2 h.nil S.nil
  dp := hS.choose_spec.2
  B₀ := S.B ⧸ big S I
  π := Ideal.Quotient.mk _
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := h.pt S
  w := by
    rw [← Category.assoc, h.pt_s, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ h.sig_π S r

variable {S}

def Red.rh {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) : S.B →+* T.B :=
  (f.φ : S.B →+* (h.mor.obj T).B)

theorem Red.rh_algebraMap {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) (r : R) :
    h.rh f (algebraMap R S.B r) = algebraMap R T.B r := f.φ.commutes r

def Red.upTo (hS : InN κ S) {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) : h.up S hS ⟶ T where
  φ := { (h.rh f) with commutes' := h.rh_algebraMap f }
  φ₀ := Ideal.Quotient.lift _ (T.π.comp (h.rh f)) fun b hb ↦ (T.ker _).2 (by
    have : big S I ≤ T.J.comap (h.rh f) := sup_le (fun b hb ↦ f.mem hb)
      (Ideal.map_le_iff_le_comap.2 fun r hr ↦ by
        change h.rh f (algebraMap R S.B r) ∈ T.J
        rw [h.rh_algebraMap]
        exact T.dp.1 (Ideal.mem_map_of_mem _ hr))
    exact this hb)
  comm _ := rfl
  dp := isDPMorphism_sup κ S.δ _ _ rfl hS.choose_spec.1 hS.choose_spec.2 T.δ _ f.dp (by
    change IsDPMorphism κ T.δ ((h.rh f).comp (algebraMap R S.B))
    rw [show (h.rh f).comp (algebraMap R S.B) = algebraMap R T.B from RingHom.ext (h.rh_algebraMap f)]
    exact T.dp)
  pt := by
    refine h.pb.hom_ext ?_ ?_
    · change (_ ≫ h.pt S) ≫ i = _
      rw [Category.assoc, h.pt_i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp]
      refine Eq.trans ?_ f.pt
      congr 2
      refine RingHom.ext fun b ↦ ?_
      obtain ⟨b, rfl⟩ := S.surj b
      rw [RingHom.comp_apply, rho_π]
      exact (f.comm b).symm
    · change (_ ≫ h.pt S) ≫ s₀ = _
      have : Mono (spMap π) := by
        have : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ h.surj
        infer_instance
      rw [← cancel_mono (spMap π), Category.assoc, Category.assoc, ← Category.assoc (h.pt S), h.pt_s,
        Category.assoc, T.w, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
      congr 1
      refine RingHom.ext fun r ↦ ?_
      simp only [RingHom.comp_apply]
      rw [h.sig_π]
      exact congrArg T.π (h.rh_algebraMap f r)

def Red.unit (hS : InN κ S) : S ⟶ h.mor.obj (h.up S hS) where
  φ := { RingHom.id S.B with commutes' := fun _ ↦ rfl }
  φ₀ := rho S I
  comm := rho_π S I
  dp := hS.choose_spec.1
  pt := (h.pt_i S).symm

end Up

variable {K : Type} (U : K → X.Opens)

abbrev redOpen (i : X₀ ⟶ X) : K → X₀.Opens := fun k ↦ i ⁻¹ᵁ U k

def Red.G : Tag κ (s₀ ≫ spMap π) (redOpen U i) ⥤ (NT κ U (s := s)).FullSubcategory where
  obj T := ⟨⟨h.mor.obj T.T, T.k, T.le⟩, h.inN_obj T.T⟩
  map f := ObjectProperty.homMk (⟨h.mor.functor.map (Tag.Hom.f f), h.le_of_le (Tag.Hom.le f)⟩ : Tag.Hom _ _)
  map_id _ := ObjectProperty.hom_ext _ (Tag.hom_ext (Thick.hom_ext fun _ ↦ rfl))
  map_comp _ _ := ObjectProperty.hom_ext _ (Tag.hom_ext (Thick.hom_ext fun _ ↦ rfl))

def Red.H : (NT κ U (s := s)).FullSubcategory ⥤ Tag κ (s₀ ≫ spMap π) (redOpen U i) where
  obj S := ⟨h.up S.obj.T S.property, S.obj.k, (h.unit S.property).le_preimage S.obj.le⟩
  map {S S'} f := ⟨h.upTo S.property (Tag.Hom.f f.hom ≫ h.unit S'.property),
    fun _ hp ↦ Tag.Hom.le f.hom hp⟩
  map_id _ := Tag.hom_ext (Thick.hom_ext fun _ ↦ rfl)
  map_comp f g := by
    refine Tag.hom_ext (Thick.hom_ext fun b ↦ ?_)
    exact (rfl : (Tag.Hom.f g.hom).φ ((Tag.Hom.f f.hom).φ b) = (Tag.Hom.f g.hom).φ ((Tag.Hom.f f.hom).φ b))

abbrev FN (κ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) :
    (NT κ U (s := s)).FullSubcategory ⥤ CommAlgCat.{0} R :=
  (NT κ U).ι ⋙ Tag.forget (dp0 R) s U ⋙ O (dp0 R) s

def Red.cG : CoefMap (RingHom.id R) (FN κ s U) (Tag.forget κ _ (redOpen U i) ⋙ O κ (s₀ ≫ spMap π)) where
  G := h.G U
  α T := RingHom.id T.T.B
  naturality _ _ := rfl
  smul T r b := (Algebra.smul_def (A := T.T.B) r b).symm

def Red.cH : CoefMap (RingHom.id R) (Tag.forget κ _ (redOpen U i) ⋙ O κ (s₀ ≫ spMap π)) (FN κ s U) where
  G := h.H U
  α S := RingHom.id S.obj.T.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

def Red.η : 𝟭 _ ⟶ h.H U ⋙ h.G U where
  app S := ObjectProperty.homMk
    (⟨h.unit S.property, le_rfl⟩ : Tag.Hom S.obj ((h.G U).obj ((h.H U).obj S)).obj)
  naturality S S' f := by
    refine ObjectProperty.hom_ext _ (Tag.hom_ext (Thick.hom_ext fun b ↦ ?_))
    exact (rfl : (Tag.Hom.f f.hom).φ b = (Tag.Hom.f f.hom).φ b)

def Red.ε : h.G U ⋙ h.H U ⟶ 𝟭 _ where
  app T := (⟨h.upTo (h.inN_obj T.T) (𝟙 _), le_rfl⟩ : Tag.Hom ((h.H U).obj ((h.G U).obj T)) T)
  naturality S S' f := by
    refine Tag.hom_ext (Thick.hom_ext fun b ↦ ?_)
    exact (rfl : (Tag.Hom.f f).φ b = (Tag.Hom.f f).φ b)

theorem Red.cG_pull1 : Function.Bijective (h.cG U).pull1 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(h.cH U).pull1, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact ((CoefMap.id _).pullCohomologyOne_eq_of_natTrans ((h.cG U).comp (h.cH U)) (h.η U) (fun _ b ↦ (rfl : b = b)) c).symm.trans
      (CoefMap.pullCohomologyOne_id c)
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact (((h.cH U).comp (h.cG U)).pullCohomologyOne_eq_of_natTrans (CoefMap.id _) (h.ε U) (fun _ b ↦ (rfl : b = b)) c).trans
      (CoefMap.pullCohomologyOne_id c)

theorem Red.cG_pull2 : Function.Bijective (h.cG U).pull2 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(h.cH U).pull2, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact ((CoefMap.id _).pullCohomologyTwo_eq_of_natTrans ((h.cG U).comp (h.cH U)) (h.η U) (fun _ b ↦ (rfl : b = b)) c).symm.trans
      (CoefMap.pullCohomologyTwo_id c)
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact (((h.cH U).comp (h.cG U)).pullCohomologyTwo_eq_of_natTrans (CoefMap.id _) (h.ε U) (fun _ b ↦ (rfl : b = b)) c).trans
      (CoefMap.pullCohomologyTwo_id c)

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}

abbrev chartOpen (s : X ⟶ Sp R) : Chart s → X.Opens := fun U ↦ U.1.1

theorem exists_lev {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) :
    ∃ n, 1 ≤ n ∧ IsLev δ n := by
  obtain ⟨N, h⟩ := h
  refine ⟨N + 1, by omega, Ideal.span_eq_bot.2 ?_⟩
  rintro _ ⟨l, hl, hN, rfl⟩
  exact h l hl (by omega)

variable {κ : DividedPowers I} {s : X ⟶ Sp R}

theorem acyc_NT (T : Tag (dp0 R) s (chartOpen s)) :
    Acyc R (CostructuredArrow (NT κ (chartOpen s)).ι T) := by
  obtain ⟨n, hn, hT⟩ := exists_lev T.T.nil
  obtain ⟨a₀⟩ := exists_lift T.k T.T T.le
  let D := CostructuredArrow (NT κ (chartOpen s)).ι T
  let mk : ∀ (S : Thick (dp0 R) s) (_ : InN κ S) (_ : ⊤ ≤ S.x ⁻¹ᵁ T.k.1.1) (_ : S ⟶ T.T), D := fun S hS h c ↦
    CostructuredArrow.mk (Y := (⟨⟨S, T.k, h⟩, hS⟩ : (NT κ (chartOpen s)).FullSubcategory))
      (⟨c, le_rfl⟩ : Tag.Hom (⟨S, T.k, h⟩ : Tag (dp0 R) s (chartOpen s)) T)
  let c : ∀ a : D, a.left.obj.T ⟶ T.T := fun a ↦ Tag.Hom.f a.hom
  have hk : ∀ a : D, chartOpen s a.left.obj.k ≤ chartOpen s T.k := fun a ↦ Tag.Hom.le a.hom
  have hle : ∀ a : D, ⊤ ≤ a.left.obj.T.x ⁻¹ᵁ T.k.1.1 := fun a p hp ↦ hk a (a.left.obj.le hp)
  let u : ∀ {a b : D}, (a ⟶ b) → (a.left.obj.T ⟶ b.left.obj.T) := fun f ↦ Tag.Hom.f f.left.hom
  have hu : ∀ {a b : D} (f : a ⟶ b), u f ≫ c b = c a := fun f ↦
    congrArg Tag.Hom.f (CostructuredArrow.w f)
  have ext : ∀ {a b : D} (f g : a ⟶ b), u f = u g → f = g := fun f g h ↦
    CostructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _ (Tag.hom_ext h))
  let hom : ∀ (a b : D) (φ : a.left.obj.T ⟶ b.left.obj.T) (_ : chartOpen s a.left.obj.k ≤ chartOpen s b.left.obj.k)
      (_ : φ ≫ c b = c a), a ⟶ b := fun a b φ h e ↦
    CostructuredArrow.homMk (ObjectProperty.homMk (⟨φ, h⟩ : Tag.Hom _ _)) (Tag.hom_ext e)
  choose P i j hP hl hun using fun a : D ↦ exists_coprod T.k a.left.obj.T a.left.property (hle a) n hn
  choose q hq using fun a : D ↦ (hun a T.T hT (c a) a₀).exists
  let d : D := mk _ (bas_inN T.k) (bas_le T.k.1) a₀
  let Q : D → D := fun a ↦ mk (P a) (hP a) ((i a).le_preimage (hle a)) (q a)
  refine acyc_of_coprod d Q (fun a ↦ hom a (Q a) (i a) (hk a) (hq a).1)
    (fun a ↦ hom d (Q a) (j a) le_rfl (hq a).2) fun a b φ ↦ ?_
  obtain ⟨ψ, hψ, hψ'⟩ := hun a (P b) (hl b) (u φ) (j b)
  have e : ψ ≫ q b = q a := by
    refine (hun a T.T hT (c a) a₀).unique ⟨?_, ?_⟩ (hq a)
    · rw [← Category.assoc, hψ.1]; exact hu φ
    · rw [← Category.assoc, hψ.2]; exact (hq b).2
  refine ⟨hom (Q a) (Q b) ψ le_rfl e, ⟨ext _ _ hψ.1, ext _ _ hψ.2⟩, fun χ hχ ↦ ext _ _ ?_⟩
  exact hψ' (u χ) ⟨congrArg u hχ.1, congrArg u hχ.2⟩

section Final

variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {i : X₀ ⟶ X}

theorem red_cover (hs : Smooth s) (i : X₀ ⟶ X) : ⨆ k, redOpen (chartOpen s) i k = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, chart_cover hs, Scheme.Hom.preimage_top]

theorem red_inf (hs : IsSeparated s) (i : X₀ ⟶ X) (k l : Chart s) :
    ∃ m, redOpen (chartOpen s) i m = redOpen (chartOpen s) i k ⊓ redOpen (chartOpen s) i l := by
  obtain ⟨m, hm⟩ := chart_inf hs k l
  exact ⟨m, by change i ⁻¹ᵁ m.1.1 = _; rw [hm]; rfl⟩

theorem Red.pull1 (h : Red κ π s s₀ i) (hs : Smooth s) (hs' : IsSeparated s) : Function.Bijective h.mor.pull1 := by
  have a := tag_pull1 (γ := dp0 R) (s := s) (chart_cover hs) (chart_inf hs')
  have b := qa1 (Tag.forget (dp0 R) s (chartOpen s) ⋙ O (dp0 R) s) (NT κ (chartOpen s)).ι acyc_NT
  have c := h.cG_pull1 (chartOpen s)
  have d := tag_pull1 (γ := κ) (s := s₀ ≫ spMap π) (red_cover hs i) (red_inf hs' i)
  refine (Function.Bijective.of_comp_iff' d _).1 ?_
  convert c.comp (b.comp a) using 1
  funext z
  obtain ⟨z, rfl⟩ := H1.mk_surjective _ z
  rfl

theorem Red.pull2 (h : Red κ π s s₀ i) (hs : Smooth s) (hs' : IsSeparated s) : Function.Bijective h.mor.pull2 := by
  have a := tag_pull2 (γ := dp0 R) (s := s) (chart_cover hs) (chart_inf hs')
  have b := qa2 (Tag.forget (dp0 R) s (chartOpen s) ⋙ O (dp0 R) s) (NT κ (chartOpen s)).ι acyc_NT
  have c := h.cG_pull2 (chartOpen s)
  have d := tag_pull2 (γ := κ) (s := s₀ ≫ spMap π) (red_cover hs i) (red_inf hs' i)
  refine (Function.Bijective.of_comp_iff' d _).1 ?_
  convert c.comp (b.comp a) using 1
  funext z
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ z
  rfl

end Final

theorem crystallineDeRham : GlobalTheory.Published.CrystallineDeRham := fun _ _ _ _ hκ _ _ _ hπ hI _ _ _ _ _ hs hs' _ hp _ ↦
  ⟨Red.pull1 ⟨hκ, hπ, hI, hp⟩ hs hs', Red.pull2 ⟨hκ, hπ, hI, hp⟩ hs hs'⟩

end FubiniStudyChowHeightFormula₂.Adr
end
end
