import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq

section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.TopStep

section Cong

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

variable (P) in

def CongQ (a b : E) : Prop := IntAt P a ∧ IntAt P b ∧ IntAt P ((a - b) / (qOf P : E))

omit [StarRing E] in
theorem CongQ.red {a b : E} (h : CongQ P a b) : redP P a = redP P b := by
  have := redP_eq_zero_of_div h.2.2
  rwa [reduction_sub h.1 h.2.1, sub_eq_zero] at this

omit [StarRing E] in
theorem CongQ.div_iff {a b : E} (h : CongQ P a b) : IntAt P (a / (qOf P : E)) ↔ IntAt P (b / (qOf P : E)) := by
  constructor
  · intro ha
    have := intAt_sub ha h.2.2
    rwa [← sub_div, sub_sub_cancel] at this
  · intro hb
    have := h.2.2.add hb
    rwa [← add_div, sub_add_cancel] at this

omit [StarRing E] in
theorem congQ_zero : CongQ P (0 : E) 0 := ⟨intAt_zero, intAt_zero, by simpa using intAt_zero⟩

omit [StarRing E] in
theorem unitV_congr (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) : LocE.unitV χ a = LocE.unitV χ b := by
  classical
  exact congrArg (fun c : 𝓞 E ⧸ P.asIdeal => if h : IsUnit c then ((χ h.unit : Kˣ) : K) else 0) h

omit [StarRing E] in
theorem unitV_det_congr (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {s : ℕ} {A B : Fin s → Fin s → E} (h : ∀ i j, CongQ P (A i j) (B i j)) :
    LocE.unitV χ (Matrix.det (Matrix.of A)) = LocE.unitV χ (Matrix.det (Matrix.of B)) := by
  apply unitV_congr
  rw [(det_int (A := Matrix.of A) fun i j => (h i j).1).2, (det_int (A := Matrix.of B) fun i j => (h i j).2.1).2]
  congr 1
  ext i j
  exact (h i j).red

omit [StarRing E] in
theorem reduction_sum_congr (s : Finset ℕ) {f g : ℕ → E} (h : ∀ i, CongQ P (f i) (g i)) :
    redP P (∑ i ∈ s, f i) = redP P (∑ i ∈ s, g i) := by
  rw [reduction_sum₂ _ fun i _ => (h i).1, reduction_sum₂ _ fun i _ => (h i).2.1]
  exact Finset.sum_congr rfl fun i _ => (h i).red

variable (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

theorem PhiG_congr (sharp : Bool) (k₀ r t j c' n' c n : ℕ) {x y : HomE E (n' + c') (n + c)}
    (h : ∀ p p', CongQ P (LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p')
      (LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p p')) :
    LocE.PhiG (qOf P) ψ₀ χ sharp k₀ r t j c' n' c n x = LocE.PhiG (qOf P) ψ₀ χ sharp k₀ r t j c' n' c n y := by
  unfold LocE.PhiG LocE.lamGv
  dsimp only
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ ?_ rfl
  · simp only [(h _ _).1, (h _ _).2.1, (h _ _).div_iff, (h _ _).red]
  · rw [reduction_sum_congr _ fun i => h i (i + 1), unitV_det_congr _ fun s s' => h s.1 s'.1]
    congr 2
    exact Finset.prod_congr rfl fun i _ => unitV_det_congr _ fun s s' => h _ _

theorem PhiGS_congr (k₀ rS r t j c' n' c n : ℕ) {x y : HomE E (n' + c') (n + c)}
    (h : ∀ p p', CongQ P (LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p')
      (LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p p')) :
    LocE.PhiGS (qOf P) ψ₀ χ k₀ rS r t j c' n' c n x = LocE.PhiGS (qOf P) ψ₀ χ k₀ rS r t j c' n' c n y := by
  unfold LocE.PhiGS LocE.lamGvS
  dsimp only
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ ?_ rfl
  · simp only [(h _ _).1, (h _ _).2.1, (h _ _).div_iff, (h _ _).red]
  · rw [reduction_add (intAt_sum _ fun i _ => (h _ _).1) (intAt_sum _ fun i _ => (h _ _).1),
      reduction_add (intAt_sum _ fun i _ => (h _ _).2.1) (intAt_sum _ fun i _ => (h _ _).2.1),
      reduction_sum_congr _ fun i => h i (i + 1), reduction_sum_congr _ fun i => h (k₀ + i) (k₀ + i + 1),
      unitV_det_congr _ fun s s' => h s.1 s'.1]
    congr 2
    exact Finset.prod_congr rfl fun i _ => unitV_det_congr _ fun s s' => h _ _

omit [NumberField E] [StarRing E] in

theorem entB_zero (q k₀ c' n' n : ℕ) (hc : c' = 0) (ex : ℕ → ℕ) (x : HomE E (n' + c') (n + 0)) (p p' : ℕ) :
    LocE.entB q k₀ c' n' 0 n ex ex x p p' =
      if h : p < n ∧ p' < n' then x (Pi.single ⟨p', by omega⟩ 1) ⟨p, h.1⟩ else 0 := by
  subst hc
  have e : ∀ m s, LocE.fIdx k₀ 0 m s = s := fun m s => by
    unfold LocE.fIdx
    split_ifs <;> omega
  unfold LocE.entB
  rw [e, e]
  by_cases h1 : p < n
  · by_cases h2 : p' < n'
    · have : Loc.eN E (n' + 0) p' = Pi.single ⟨p', h2⟩ 1 := by
        funext l
        simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
      rw [dif_pos ⟨h1, h2⟩, this]
      simp [LocE.scE, Loc.atN, h1, h2]
    · have : Loc.eN E (n' + 0) p' = 0 := by
        funext l
        have := l.2
        simp only [Loc.eN, Pi.zero_apply]
        rw [if_neg (by omega)]
      rw [dif_neg fun h => h2 h.2, this]
      simp [Loc.atN]
  · rw [dif_neg fun h => h1 h.1]
    simp [Loc.atN, h1]

omit [StarRing E] in

theorem locChar_mul (q : ℕ) (cq : K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {u : E} (hu : ∀ a, redP P (a * u) = redP P a) (a : E) :
    LocE.locChar q cq ξ (a * u) = LocE.locChar q cq ξ a := by
  have e : ∀ z : ℤ, redP P (a * u / (q : E) ^ z) = redP P (a / (q : E) ^ z) := fun z => by
    rw [mul_div_right_comm, hu]
  have ev : LocE.vP P q (a * u) = LocE.vP P q a := by
    unfold LocE.vP
    simp only [e]
  unfold LocE.locChar
  rw [ev, unitV_congr ξ (e _)]

end Cong

section Tame

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def TameFr (th : ThDist E K a b SB V V') : Prop :=
  ∀ (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' : Frs E b SB) (c : ℕ) (x : HomE E a b)
    (κ : GLQ E b SB), IsSdLat N → IsSdLat N' → (∀ P : SB, redGL b P.1 (κ P) = 1) →
    th N fr N' (fun P => fr' P * (κ P).1) c x = th N fr N' fr' c x

end Tame

section TameC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem tameFr_thDistC (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (cq : SB → X.K) (ξ : ∀ P : SB, (𝓞 X.E ⧸ P.1.asIdeal)ˣ →* X.Kˣ)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) :
    TameFr (thDistC A Sall SB D sel mU (fun P => LocE.locChar (qOf P.1) (cq P) (ξ P)) lam lam' n) := by
  intro N fr N' fr' c x κ _ _ hκ
  have e : muInvDet sel SB mU (fun P => LocE.locChar (qOf P.1) (cq P) (ξ P)) N' (fun P => fr' P * (κ P).1) =
      muInvDet sel SB mU (fun P => LocE.locChar (qOf P.1) (cq P) (ξ P)) N' fr' := by
    unfold muInvDet
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_mul, Units.val_mul]
    exact locChar_mul _ _ _ (redP_mul_det (κ P) (hκ P)) _
  unfold thDistC
  rw [e]

theorem tameFr_chTh (A : Amb X) (u : Pr.Word) (m2 : ℕ) : TameFr (chTh W Ch sel mu cst A u m2).top :=
  tameFr_thDistC sel A _ _ _ _ _ _ _ _ _

end TameC

section Unif

variable {X : Fields} {Pr : Primes X}

theorem qOf_notMem_sq (hX : X.Ok) (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    ((qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w ∈ Pr.vG i := (Finset.mem_union.1 hw).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
  have hg0 : (Pr.g i : 𝓞 X.E) ≠ 0 := by exact_mod_cast (hPr.g_prime i).ne_zero
  set b := X.conjO (Pr.piG i) with hb
  have h0 : b ≠ 0 := fun h => hg0 (by rw [← hPr.piG_norm i, ← hb, h, mul_zero])
  have hnorm : Ideal.absNorm (Ideal.span {b}) = Pr.g i ^ X.f := by
    have h1 : Ideal.absNorm (Ideal.span {Pr.piG i}) * Ideal.absNorm (Ideal.span {b}) = Pr.g i ^ (2 * X.f) := by
      rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hPr.piG_norm, X.absNorm_nat, hX.rankQ]
    rw [← X.absNorm_conjO] at h1
    have h2 : Ideal.absNorm (Ideal.span {b}) ^ 2 = (Pr.g i ^ X.f) ^ 2 := by
      rw [sq, h1, ← pow_mul, mul_comm]
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2
  intro hT
  rw [qOf, hPr.vG_norm i w hi] at hT
  have hbw : b ∈ w.asIdeal := decoFin_mem_of_mem_divs hi
  have hmem : b ∈ w.asIdeal ^ 2 := by
    obtain ⟨s, t, e⟩ := hPr.piG_cop i
    have e1 : b = s * (Pr.g i : 𝓞 X.E) + t * (b * b) := by
      rw [← hPr.piG_norm i]
      calc b = (s * Pr.piG i + t * b) * b := by rw [e, one_mul]
        _ = _ := by ring
    rw [e1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hT) (Ideal.mul_mem_left _ _ ?_)
    rw [sq]
    exact Ideal.mul_mem_mul hbw hbw
  have hdvd : (∏ Q ∈ Pr.vG i, Q.asIdeal ^ (if Q = w then 2 else 1)) ∣ Ideal.span {b} := by
    refine Finset.prod_dvd_of_coprime (fun Q _ Q' _ hne => ?_) fun Q hQ => ?_
    · refine IsCoprime.pow ?_
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal fun h => hne (HeightOneSpectrum.ext h)
    · rw [Ideal.dvd_span_singleton]
      split_ifs with h
      · rw [h]; exact hmem
      · rw [pow_one]; exact decoFin_mem_of_mem_divs hQ
  have hN : Ideal.absNorm (∏ Q ∈ Pr.vG i, Q.asIdeal ^ (if Q = w then 2 else 1)) = Pr.g i ^ (X.f + 1) := by
    rw [map_prod]
    have h1 : ∀ Q ∈ Pr.vG i, Ideal.absNorm (Q.asIdeal ^ (if Q = w then 2 else 1)) = Pr.g i * (if Q = w then Pr.g i else 1) := by
      intro Q hQ
      rw [map_pow, hPr.vG_norm i Q hQ]
      split_ifs
      · rw [sq]
      · rw [pow_one, mul_one]
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, hPr.vG_card, Finset.prod_ite_eq', if_pos hi, pow_succ]
  have h3 := map_dvd Ideal.absNorm hdvd
  rw [hN, hnorm] at h3
  have := (Nat.pow_dvd_pow_iff_le_right (hPr.g_prime i).one_lt).1 h3
  omega

end Unif

end GlobalTheory.TopStep
end
end

section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.TopStep

section Index

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in

theorem exists_int_approx (c : ℕ) {a : E} (ha : IntAt P a) :
    ∃ r : 𝓞 E, IntAt P (((qOf P : E) ^ c)⁻¹ * (a - algebraMap (𝓞 E) E r)) := by
  obtain ⟨r, s, hs, h⟩ := ha
  have hq := qOf_ne_zero (P := P)
  have hq' : (((qOf P : ℕ) : 𝓞 E) ^ c) ≠ 0 := pow_ne_zero _ fun h0 => hq (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have := P.isMaximal
  obtain ⟨I, k, hI, e⟩ : ∃ (I : Ideal (𝓞 E)) (k : ℕ), P.asIdeal ⊔ I = ⊤ ∧
      Ideal.span {((qOf P : ℕ) : 𝓞 E) ^ c} = P.asIdeal ^ k * I := by
    obtain ⟨I, hI, e⟩ := Ideal.eq_prime_pow_mul_coprime (Ideal.span_singleton_eq_bot.not.2 hq') P.asIdeal
    exact ⟨I, _, hI, e⟩
  have hIP : ¬ I ≤ P.asIdeal := fun hle => P.isPrime.ne_top (by rw [← hI, sup_of_le_left hle])
  obtain ⟨s', hs'I, hs'⟩ := Set.not_subset.1 hIP
  have hcop : IsCoprime (Ideal.span {s}) (P.asIdeal ^ k) := by
    refine IsCoprime.pow_right ?_
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
    exact this.out.2 _ (left_lt_sup.2 fun hle => hs (hle (Ideal.mem_span_singleton_self s)))
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (e ▸ Ideal.mul_mem_mul hy hs'I : y * s' ∈ Ideal.span {((qOf P : ℕ) : 𝓞 E) ^ c})
  refine ⟨r * t, r * z, s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  have e1 := congrArg (algebraMap (𝓞 E) E) hxy
  have e2 := congrArg (algebraMap (𝓞 E) E) hz
  simp only [map_mul, map_add, map_one, map_pow, map_natCast] at e1 e2 ⊢
  field_simp
  linear_combination (algebraMap (𝓞 E) E s') * h - (algebraMap (𝓞 E) E r) * e2 -
    (algebraMap (𝓞 E) E r) * (algebraMap (𝓞 E) E s') * e1

instance prinCong_finiteIndex (c : ℕ) : (prinCong n P c).FiniteIndex := by
  have hq := qOf_ne_zero (P := P)
  have hq' : (((qOf P : ℕ) : 𝓞 E) ^ c) ≠ 0 := pow_ne_zero _ fun h0 => hq (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have : Finite (𝓞 E ⧸ Ideal.span {((qOf P : ℕ) : 𝓞 E) ^ c}) :=
    (Ideal.absNorm_ne_zero_iff _).1 fun h => hq' (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h))
  choose r hr using fun (k : GLint E n P) (i j : Fin n) => exists_int_approx c (glint_entry k i j)
  have : Finite (GLint E n P ⧸ prinCong n P c) := by
    refine Finite.of_injective (fun (x : GLint E n P ⧸ prinCong n P c) (i j : Fin n) =>
      Ideal.Quotient.mk (Ideal.span {((qOf P : ℕ) : 𝓞 E) ^ c}) (r x.out i j)) fun x y h => ?_
    rw [← x.out_eq', ← y.out_eq', QuotientGroup.eq]
    intro v hv
    have e : (x.out⁻¹ * y.out).1 v - v = (x.out⁻¹).1 (y.out.1 v - x.out.1 v) := by
      have : (x.out⁻¹).1 (x.out.1 v) = v := LinearEquiv.symm_apply_apply x.out.1 v
      rw [map_sub, this]
      rfl
    rw [e, ← map_smul]
    refine glint_mem _ (mem_stdAt.2 fun i => ?_)
    have e1 := apply_eq_sum (y.out.1 : Sp E n →ₗ[E] Sp E n) v i
    have e2 := apply_eq_sum (x.out.1 : Sp E n →ₗ[E] Sp E n) v i
    rw [LinearEquiv.coe_coe] at e1 e2
    rw [Pi.smul_apply, Pi.sub_apply, e1, e2, ← Finset.sum_sub_distrib, smul_eq_mul, Finset.mul_sum]
    refine intAt_sum _ fun j _ => ?_
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun h i) j))
    have hz' := congrArg (algebraMap (𝓞 E) E) hz
    simp only [map_mul, map_sub, map_pow, map_natCast] at hz'
    have h3 := (mem_stdAt.1 hv j).mul (intAt_sub (intAt_sub (hr y.out i j) (hr x.out i j)) (IntAt.coe P z))
    convert h3 using 1
    field_simp
    linear_combination (v j) * hz'
  exact Subgroup.finiteIndex_of_finite_quotient

end Index

section Lev

variable {κ K : Type} [CommRing κ] [Field K] {n N : ℕ} (h : n ≤ N) (l : Lev κ K n)

def levExt : Lev κ K N :=
  ⟨l.H.map (diagEmb κ h), l.lam.comp (l.H.equivMapOfInjective _ (diagEmb_injective h)).symm.toMonoidHom⟩

theorem mem_levExt {g : GL (Fin N) κ} : g ∈ (levExt h l).H ↔ ∃ j ∈ l.H, diagEmb κ h j = g := Subgroup.mem_map

theorem diagEmb_mem_levExt {j : GL (Fin n) κ} : diagEmb κ h j ∈ (levExt h l).H ↔ j ∈ l.H :=
  Subgroup.mem_map_iff_mem (diagEmb_injective h)

theorem levExt_lam {g : GL (Fin N) κ} (hg : g ∈ (levExt h l).H) {j : GL (Fin n) κ} (hj : j ∈ l.H) (e : g = diagEmb κ h j) :
    (levExt h l).lam ⟨g, hg⟩ = l.lam ⟨j, hj⟩ := by
  subst e
  show l.lam ((l.H.equivMapOfInjective _ (diagEmb_injective h)).symm _) = _
  congr 1
  exact (MulEquiv.symm_apply_eq _).2 rfl

theorem lev_lam_congr {l l' : Lev κ K n} (e : l = l') {g g' : GL (Fin n) κ} (e' : g = g') (hg : g ∈ l.H) (hg' : g' ∈ l'.H) :
    l.lam ⟨g, hg⟩ = l'.lam ⟨g', hg'⟩ := by
  subst e e'
  rfl

end Lev

section K1

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n N : ℕ} (hN : N = n + 1) {P : HeightOneSpectrum (𝓞 E)}
  (l : Lev (𝓞 E ⧸ P.asIdeal) K n) (c : ℕ)

def levJ : Subgroup (GLint E n P) := l.H.comap (redGL n P)

def K1 : Subgroup (GLint E N P) := (levJ l).map (extI hN P) ⊔ prinCong N P c

theorem mem_parahoricTimesPrincipalCongruence_iff {k : GLint E N P} : k ∈ K1 hN l c ↔ ∃ j ∈ levJ l, ∃ κ ∈ prinCong N P c, k = extI hN P j * κ := by
  rw [K1, Subgroup.mem_sup_of_normal_right]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, κ, hκ, rfl⟩
    exact ⟨j, hj, κ, hκ, rfl⟩
  · rintro ⟨j, hj, κ, hκ, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, κ, hκ, rfl⟩

theorem integralGLSuccEmbedding_mem_parahoricTimesPrincipalCongruence {j : GLint E n P} (hj : j ∈ levJ l) : extI hN P j ∈ K1 hN l c :=
  (mem_parahoricTimesPrincipalCongruence_iff hN l c).2 ⟨j, hj, 1, one_mem _, (mul_one _).symm⟩

theorem principalCongruence_le_levelGroup : prinCong N P c ≤ K1 hN l c := le_sup_right

variable {c} (hc : 0 < c)
include hc

theorem reductionModPrime_mem_levelExtendDiagonal_of_parahoric {k : GLint E N P} (hk : k ∈ K1 hN l c) : redGL N P k ∈ (levExt (by omega : n ≤ N) l).H := by
  obtain ⟨j, hj, κ, hκ, rfl⟩ := (mem_parahoricTimesPrincipalCongruence_iff hN l c).1 hk
  rw [map_mul, redGL_of_prinCong hc hκ, mul_one, redGL_extI, diagEmb_mem_levExt]
  exact hj

def levelParahoricTimesPrincipalCongruence : LevI E K N P where
  H := K1 hN l c
  lam := (levExt (by omega : n ≤ N) l).lam.comp
    (((redGL N P).comp (K1 hN l c).subtype).codRestrict _ fun k => reductionModPrime_mem_levelExtendDiagonal_of_parahoric hN l hc k.2)

theorem parahoricTimesPrincipalCongruence_character_eq {j : GLint E n P} (hj : j ∈ levJ l) {κ : GLint E N P} (hκ : κ ∈ prinCong N P c) {k : GLint E N P}
    (hk : k ∈ (levelParahoricTimesPrincipalCongruence hN l hc).H) (e : k = extI hN P j * κ) : (levelParahoricTimesPrincipalCongruence hN l hc).lam ⟨k, hk⟩ = l.lam ⟨redGL n P j, hj⟩ := by
  refine levExt_lam _ l (reductionModPrime_mem_levelExtendDiagonal_of_parahoric hN l hc hk) hj ?_
  show redGL N P k = _
  rw [e, map_mul, redGL_of_prinCong hc hκ, mul_one, redGL_extI]

theorem levelGroup_character_isOfFinOrder (k : (levelParahoricTimesPrincipalCongruence hN l hc).H) : IsOfFinOrder ((levelParahoricTimesPrincipalCongruence hN l hc).lam k) :=
  MonoidHom.isOfFinOrder (levExt (by omega : n ≤ N) l).lam (isOfFinOrder_of_finite _)

end K1

def TopDepth (R : Ranks) (M : ℕ) : Type := {c : ℕ // max (4 * R.m + 1) (2 * R.m + 2 * M) ≤ c}

instance (R : Ranks) (M : ℕ) : Inhabited (TopDepth R M) := ⟨⟨max (4 * R.m + 1) (2 * R.m + 2 * M), le_rfl⟩⟩

theorem TopDepth.pos {R : Ranks} {M : ℕ} (c : TopDepth R M) : 0 < c.1 :=
  lt_of_lt_of_le (Nat.succ_pos _) ((le_max_left _ _).trans c.2)

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

variable (R) in

abbrev TopPt (u : Pr.Word) : Type := ChPt (R := R) sel mu u R.m

def topLevG (P : LevFam X.E X.K R.r Pr.vGs) : LevFam X.E X.K (R.N R.m) Pr.vGs := fun w =>
  levExt (Nat.sub_le _ 1) (rowTyG Ch P w)

variable (R) in

def topLevQ {c : ℕ} (hc : 0 < c) : LevQFam X.E X.K (R.N R.m) (QE sel (mu : Chr X.F X.E X.K)) := fun P =>
  levelParahoricTimesPrincipalCongruence (N_m_succ R) (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) P) hc

@[reducible] def topGSD (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) {M : ℕ} (c : TopDepth R M) : GSD X.K :=
  frmGSD (colValF W sel mu u R.m) (topLevG Ch P) (topLevQ R sel mu c.pos)

theorem topGSD_ok (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) {M : ℕ} (c : TopDepth R M) :
    (topGSD W Ch sel mu P u c).Ok := by
  refine GlobalTheory.FramedForms.main hX (W.lamTrue u R.m) (topLevG Ch P) (topLevQ R sel mu c.pos)
    (fun Q => Subgroup.finiteIndex_of_le (principalCongruence_le_levelGroup _ _ _)) fun g => isOfFinOrder_iff_pow_eq_one.1 ?_
  have e : (topLevQ R sel mu c.pos).chr g = _ :=
    piChar_apply (fun w => (topLevQ R sel mu c.pos w).H) (fun w => (topLevQ R sel mu c.pos w).lam) g
  rw [e]
  exact Finset.prod_induction _ IsOfFinOrder (fun a b => IsOfFinOrder.mul) IsOfFinOrder.one fun w _ =>
    levelGroup_character_isOfFinOrder _ _ c.pos _

open Classical in

abbrev inG (w : Pr.vGs) : rowSG Pr sel mu := ⟨w.1, Finset.mem_union_left _ w.2⟩

open Classical in
variable (Pr) in

abbrev inQ (w : QE sel (mu : Chr X.F X.E X.K)) : rowSG Pr sel mu := ⟨w.1, Finset.mem_union_right _ w.2⟩

variable (Pr) in

def TilOk (u : Pr.Word) : Prop :=
  (∀ P : Pr.vT u, cO X.E (Pr.piT u) ∉ P.1.asIdeal) ∧ (∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal) ∧
    Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))

variable {sel mu}

theorem tilOk_of (hPr : Pr.Ok) (u : Pr.Word)
    (hQ : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ P.asIdeal ∧ ∀ i, (Pr.g i : 𝓞 X.E) ∉ P.asIdeal) :
    TilOk Pr sel mu u := by
  classical
  refine ⟨conj_piT_notMem hPr u, fun w => ?_, Finset.disjoint_left.2 fun w hw hw' => ?_⟩
  · rcases Finset.mem_union.1 w.2 with h | h
    · exact piT_notMem_vGs hPr u ⟨w.1, h⟩
    · intro hm
      apply (hQ w.1 h).1
      rw [← hPr.piT_norm u]
      exact Ideal.mul_mem_right _ _ hm
  · obtain ⟨i, hi⟩ := exists_g_mem hPr ⟨w, hw⟩
    exact (hQ w hw').2 i hi

theorem tilOk_of_avoid (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S) : TilOk Pr sel mu u := by
  classical
  have key : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), ∀ p : ℕ, p.Prime → p ∈ S → (p : 𝓞 X.E) ∉ P.asIdeal := by
    intro P hP p hp hpS hm
    unfold QE at hP
    split_ifs at hP with hf
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
      have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := hf.mem_toFinset.1 hv
      have hg : GoodPl X.E S v := by
        by_contra hng
        exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 mu.2.2 v) hng)
      apply hg.2.2
      have hpv : (p : 𝓞 X.F) ∈ v.asIdeal := by
        rw [← hsel v, Ideal.under, Ideal.mem_comap, map_natCast]
        exact hm
      have h0 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hpv
      have : Formalism.EigenvalueLevelCeiling.plc v = p := by
        have := v.isPrime
        exact CharP.ringChar_of_prime_eq_zero hp h0
      rw [this]
      exact hpS
    · simp at hP
  exact tilOk_of hPr u fun P hP => ⟨key P hP _ (hPr.T_prime u) hS.1, fun i => key P hP _ (hPr.g_prime i) (hS.2 i)⟩

variable {u : Pr.Word}

def piU (H : TilOk Pr sel mu u) (P : rowSG Pr sel mu) : X.Eˣ :=
  Units.mk0 ((Pr.piT u : 𝓞 X.E) : X.E) fun h => H.2.1 P (by
    rw [RingOfIntegers.coe_eq_zero_iff.1 h]
    exact Ideal.zero_mem _)

def tilFr (H : TilOk Pr sel mu u) (d : RowPt Pr R sel mu) (P : rowSG Pr sel mu) : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m) :=
  sumE (N_m_succ R) (d.1.liftFr P) (piU H P)

theorem tilFr_isLiftFr (H : TilOk Pr sel mu u) (d : RowPt Pr R sel mu) (P : rowSG Pr sel mu) :
    IsLiftFr (tilQ sel mu u d).1 P (tilFr H d P) :=
  isLiftFr_tilH (N_m_succ R) d H.1 H.2.1 P (liftFr_spec d.2 P) _ rfl

open Classical in

def tilTop (H : TilOk Pr sel mu u) (d : RowPt Pr R sel mu) : TopPt R sel mu u :=
  ⟨((tilQ sel mu u d).res Finset.subset_union_left, fun P => tilFr H d (inQ Pr sel mu P)),
    fun P => (tilFr_isLiftFr H d (inQ Pr sel mu P)).1⟩

theorem frsF_tilTop_g (H : TilOk Pr sel mu u) (d : RowPt Pr R sel mu) (P : rowSG Pr sel mu) (h : P.1 ∈ Pr.vGs) :
    frsF sel mu (tilTop H d) P = frsT sel mu u d P := dif_pos h

theorem frsF_tilTop_Q (H : TilOk Pr sel mu u) (d : RowPt Pr R sel mu) (P : rowSG Pr sel mu) (h : P.1 ∉ Pr.vGs) :
    frsF sel mu (tilTop H d) P = tilFr H d P := dif_neg h

theorem frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · exact (liftFr_spec p.deco.2 ⟨P.1, h⟩).1 x
  · exact p.2 ⟨P.1, _⟩ x

variable {Ch} {P : LevFam X.E X.K R.r Pr.vGs}

theorem rowTy_inG (w : Pr.vGs) : rowTy Ch sel mu P (inG sel mu w) = rowTyG Ch P w := LevFam.glue_of_mem _ _ (inG sel mu w) w.2

theorem rowTy_inQ (H : TilOk Pr sel mu u) (w : QE sel (mu : Chr X.F X.E X.K)) :
    rowTy Ch sel mu P (inQ Pr sel mu w) = rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) w :=
  LevFam.glue_of_not _ _ (inQ Pr sel mu w) (Finset.disjoint_right.1 H.2.2 w.2)

theorem row_mem_g (g : (rowTy Ch sel mu P).inv.grp) (w : Pr.vGs) :
    g.1 (inG sel mu w) ∈ (rowTyG Ch P w).H := by
  rw [← rowTy_inG (sel := sel) (mu := mu)]
  exact g.2 (inG sel mu w) (Set.mem_univ _)

theorem row_mem_Q (H : TilOk Pr sel mu u) (g : (rowTy Ch sel mu P).inv.grp) (w : QE sel (mu : Chr X.F X.E X.K)) :
    g.1 (inQ Pr sel mu w) ∈ (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) w).H := by
  rw [← rowTy_inQ (Ch := Ch) (P := P) H]
  exact g.2 (inQ Pr sel mu w) (Set.mem_univ _)

def rowPass (g : FormG (rowTy Ch sel mu P).inv) (d : RowPt Pr R sel mu) (w : rowSG Pr sel mu) : GLint X.E (R.N R.m - 1) w.1 :=
  passFr g.1.1 g.2.1 (liftFr_spec d.2 w) (liftFr_spec (g • d).2 w)

theorem redGL_rowPass (g : FormG (rowTy Ch sel mu P).inv) (d : RowPt Pr R sel mu) (w : rowSG Pr sel mu) :
    redGL _ w.1 (rowPass g d w) = g.2.1 w := redGL_passFr _ _ _ _

theorem rowPass_mem (H : TilOk Pr sel mu u) (g : FormG (rowTy Ch sel mu P).inv) (d : RowPt Pr R sel mu)
    (w : QE sel (mu : Chr X.F X.E X.K)) : rowPass g d (inQ Pr sel mu w) ∈
      levJ (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) w) := by
  have h := row_mem_Q H g.2 w
  rw [← redGL_rowPass g d] at h
  exact h

def tilEl (H : TilOk Pr sel mu u) {c : ℕ} (hc : 0 < c) (g : FormG (rowTy Ch sel mu P).inv) (d : RowPt Pr R sel mu) :
    FrmG (topLevG Ch P) (topLevQ R sel mu hc) :=
  (extUH (N_m_succ R) g.1,
    ⟨fun w => diagEmb _ (Nat.sub_le _ 1) (g.2.1 (inG sel mu w)),
      fun w _ => (diagEmb_mem_levExt _ _).2 (row_mem_g g.2 w)⟩,
    ⟨fun w => extI (N_m_succ R) w.1 (rowPass g d (inQ Pr sel mu w)),
      fun w _ => integralGLSuccEmbedding_mem_parahoricTimesPrincipalCongruence _ _ _ (rowPass_mem H g d w)⟩)

theorem tilEl_smul (H : TilOk Pr sel mu u) {c : ℕ} (hc : 0 < c) (g : FormG (rowTy Ch sel mu P).inv) (d : RowPt Pr R sel mu) :
    tilEl H hc g d • tilTop H d = tilTop H (g • d) := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · have h := DecoSet.tilH_smul (ST := Pr.vT u) (N_m_succ R) (FormG.incl _ g) d H.1 H.2.1
    apply Subtype.ext
    have h' := congrArg (fun x => Deco.res (Finset.subset_union_left (s₁ := Pr.vGs)) x.1) h
    refine Eq.trans ?_ h'.symm
    ext1
    · rfl
    · rfl
    · funext w x
      exact congrArg (fun A : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal) => A.1.mulVec
        ((tilQ sel mu u d).1.be (inG sel mu w) ((extUH (N_m_succ R) g.1).1.symm x)))
        (extGH_apply (N_m_succ R) g.2.1 (inG sel mu w)).symm
  · funext w
    show (extUH (N_m_succ R) g.1).1 * tilFr H d (inQ Pr sel mu w) *
      ((extI (N_m_succ R) w.1 (rowPass g d (inQ Pr sel mu w)))⁻¹).1 = tilFr H (g • d) (inQ Pr sel mu w)
    rw [← map_inv, extI_val, extUH_val, tilFr, tilFr, ← sumE_mul, ← sumE_mul, one_mul, mul_one]
    have e : g.1.1 * d.1.liftFr (inQ Pr sel mu w) * ((rowPass g d (inQ Pr sel mu w))⁻¹).1 = (g • d).1.liftFr (inQ Pr sel mu w) := by
      show g.1.1 * d.1.liftFr (inQ Pr sel mu w) *
        (((g • d).1.liftFr (inQ Pr sel mu w))⁻¹ * g.1.1 * d.1.liftFr (inQ Pr sel mu w))⁻¹ = _
      group
    rw [e]

theorem tilEl_chr (H : TilOk Pr sel mu u) {c : ℕ} (hc : 0 < c) (g : FormG (rowTy Ch sel mu P).inv) (d : RowPt Pr R sel mu) :
    (topLevG Ch P).chr (tilEl H hc g d).2.1 * (topLevQ R sel mu hc).chr (tilEl H hc g d).2.2 =
      ((rowTy Ch sel mu P).inv.chr g.2)⁻¹ := by
  classical
  have e1 := LevFam.chr_apply (topLevG Ch P) (tilEl H hc g d).2.1
  have e2 : (topLevQ R sel mu hc).chr (tilEl H hc g d).2.2 = _ :=
    piChar_apply (fun w => (topLevQ R sel mu hc w).H) (fun w => (topLevQ R sel mu hc w).lam) (tilEl H hc g d).2.2
  have e3 := LevFam.chr_apply (rowTy Ch sel mu P).inv g.2
  rw [e1, e2, e3, ← Finset.prod_inv_distrib]
  refine Eq.trans ?_ ((Equiv.Finset.union _ _ H.2.2).prod_comp _)
  rw [Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl fun w _ => ?_
    refine (levExt_lam _ _ _ (row_mem_g g.2 w) rfl).trans ?_
    exact (lev_lam_congr (rowTy_inG w).symm rfl (row_mem_g g.2 w) (g.2.2 (inG sel mu w) (Set.mem_univ _))).trans (inv_inv _).symm
  · refine Finset.prod_congr rfl fun w _ => ?_
    refine (parahoricTimesPrincipalCongruence_character_eq _ _ hc (rowPass_mem H g d w) (one_mem _) _ (mul_one _).symm).trans ?_
    exact (lev_lam_congr (rowTy_inQ H w).symm (redGL_rowPass g d (inQ Pr sel mu w)) (rowPass_mem H g d w)
      (g.2.2 (inQ Pr sel mu w) (Set.mem_univ _))).trans (inv_inv _).symm

theorem tilEl_rho (H : TilOk Pr sel mu u) {M : ℕ} (c : TopDepth R M) (g : FormG (rowTy Ch sel mu P).inv) (d : RowPt Pr R sel mu) :
    (topGSD W Ch sel mu P u c).ρ (tilEl H c.pos g d) = evRho W Ch sel mu P u g := by
  exact congrArg (fun z : X.Kˣ => (z : X.K) • (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) g.1))
    (tilEl_chr H c.pos g d)

variable (Ch P) in

def evTop (H : TilOk Pr sel mu u) {M : ℕ} (c : TopDepth R M) :
    (topGSD W Ch sel mu P u c).EqFun →ₗ[X.K] (evGSD W Ch sel mu P u).EqFun where
  toFun φ := ⟨fun d => φ.1 (tilTop H d), fun g d => by
    have h := φ.2 (tilEl H c.pos g d) (tilTop H d)
    rw [tilEl_rho] at h
    exact (congrArg φ.1 (tilEl_smul H c.pos g d).symm).trans h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Top

section Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def locTop (m2 : ℕ) (P : rowSG Pr sel mu) (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (y' : Sp X.E (R.N (m2 + 1))) : X.K :=
  PhiTop Ch mu cst.sharp m2 P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
    ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y'

def XiTop {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : TopPt R sel mu u)
    (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  phiT X.K p.deco.1 p'.deco.1 x *
    ∏ P : rowSG Pr sel mu,
      locTop Ch sel mu cst m2 P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))

variable {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2)

open Classical in

def topDegreeKTwo (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : TopPt R sel mu u) :
    (colValF W sel mu u (m2 + 1)).V →ₗ[X.K] (colValF W sel mu u R.m).V :=
  if Y ∈ ybSet sel mu cst p.deco.1.N then
    kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
      p'.deco.1.N (frsF sel mu p') (XiTop Ch sel mu cst m2 p Y p')
  else 0

theorem atNL_last (x : Sp X.E (R.N R.m)) : atNL X.E (R.N R.m) (R.N R.m - 1) x = x (Br.iL (N_m_succ R)) := by
  unfold atNL
  rw [dif_pos (show R.N R.m - 1 < R.N R.m from (Br.iL (N_m_succ R)).2)]
  rfl

theorem cond_of_ite_ne_zero {c : Prop} {i : Decidable c} {a : X.K} (h : @ite _ c i a 0 ≠ 0) : c := by
  by_contra hc
  exact h (if_neg hc)

theorem castAdd_single {n' c' : ℕ} (i : Fin n') :
    LinearMap.funLeft X.E X.E (Fin.castAdd c') (Pi.single (Fin.castAdd c' i) 1) = (Pi.single i 1 : Sp X.E n') := by
  funext l
  simp [LinearMap.funLeft_apply, Pi.single_apply]

theorem entB_top (hm : R.m = m2 + 2) (q : ℕ) (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (p p' : ℕ) :
    LocE.entB q R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1)
        (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p' =
      if h : p < R.N R.m - 1 ∧ p' < R.N (m2 + 1) then y (Pi.single ⟨p', h.2⟩ 1) (Br.iC (N_m_succ R) ⟨p, h.1⟩) else 0 := by
  rw [entB_zero _ _ _ _ _ (by unfold cOf; omega)]
  split_ifs with h
  · exact congrArg (fun v => y v (Br.iC (N_m_succ R) ⟨p, h.1⟩)) (castAdd_single (c' := cOf R (m2 + 1)) ⟨p', h.2⟩)
  · rfl

theorem rank_add_mul_eq_penultimate_rank (hm : R.m = m2 + 2) : R.r + (R.m - 1) * R.t = R.N (m2 + 1) := by
  unfold Ranks.r Ranks.N
  rw [hm]
  have : m2 + 2 - 1 = m2 + 1 := rfl
  rw [this, Nat.mul_add, Nat.mul_one]
  omega

variable {Ch sel mu cst}

theorem locTop_supp (hm : R.m = m2 + 2) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) {y : HomE X.E (R.N (m2 + 1)) (R.N R.m)}
    {y' : Sp X.E (R.N (m2 + 1))} (h : locTop Ch sel mu cst m2 P y y' ≠ 0) (s : Fin (R.N (m2 + 1))) :
    y (Pi.single s 1) ∈ stdAt X.E (R.N R.m) P.1 := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  refine (mem_stdAt_succ (N_m_succ R)).2 ⟨mem_stdAt.2 fun i => ?_, ?_⟩
  · have key : IntAt P.1 (LocE.entB (qOf P.1) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1)
        (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) i.1 s.1) := by
      unfold PhiTop at h1
      rw [if_pos hP] at h1
      split_ifs at h1
      · exact (cond_of_ite_ne_zero h1).1 i.1 s.1 i.2 (by rw [rank_add_mul_eq_penultimate_rank hm]; exact s.2)
      · exact (cond_of_ite_ne_zero h1).1 i.1 s.1 i.2 (by rw [rank_add_mul_eq_penultimate_rank hm]; exact s.2)
    rw [entB_top hm, dif_pos ⟨i.2, s.2⟩] at key
    exact key
  · unfold ftY at h2
    rw [if_pos hP] at h2
    have := cond_of_ite_ne_zero h2 s
    rwa [LinearMap.comp_apply, atNL_last] at this

theorem locTop_congr (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    {y z : HomE X.E (R.N (m2 + 1)) (R.N R.m)} {y' : Sp X.E (R.N (m2 + 1))} (hy' : ∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i))
    (h : ∀ s l, CongQ P.1 (y (Pi.single s 1) l) (z (Pi.single s 1) l)) :
    locTop Ch sel mu cst m2 P y y' = locTop Ch sel mu cst m2 P z y' := by
  unfold locTop
  refine congrArg₂ (· * ·) ?_ ?_
  · have he : ∀ p p', CongQ P.1
        (LocE.entB (qOf P.1) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1)
          (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p')
        (LocE.entB (qOf P.1) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1)
          (prXp X.E R ∘ₗ z ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p') := fun p p' => by
      rw [entB_top hm, entB_top hm]
      split_ifs
      · exact h _ _
      · exact congQ_zero
    unfold PhiTop
    rw [if_pos hP]
    split_ifs
    · exact PhiGS_congr _ _ _ _ _ _ _ _ _ _ _ he
    · exact PhiG_congr _ _ _ _ _ _ _ _ _ _ _ he
  · unfold ftY
    have hq := qOf_ne_zero (P := P.1)
    have ev : ∀ w : HomE X.E (R.N (m2 + 1)) (R.N R.m), (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ w) y' =
        ∑ j, y' j * w (Pi.single j 1) (Br.iL (N_m_succ R)) := fun w => by
      rw [LinearMap.comp_apply, atNL_last, apply_eq_sum]
    have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
    rw [if_pos hP, if_pos hP, if_pos (fun i => by rw [LinearMap.comp_apply, atNL_last]; exact (h _ _).1),
      if_pos (fun i => by rw [LinearMap.comp_apply, atNL_last]; exact (h _ _).2.1), ev, ev]
    have hd : IntAt P.1 ((epsSg : X.E) * ∑ j, ((qOf P.1 : X.E) * y' j) *
        ((y (Pi.single j 1) (Br.iL (N_m_succ R)) - z (Pi.single j 1) (Br.iL (N_m_succ R))) / (qOf P.1 : X.E))) :=
      he.mul (intAt_sum _ fun j _ => (hy' j).mul (h _ _).2.2)
    have hz : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * ∑ j, y' j * z (Pi.single j 1) (Br.iL (N_m_succ R)))) := by
      obtain ⟨D, hD⟩ : ∃ D, cst.D P = D + 1 := ⟨cst.D P - 1, by have := hc.D_pos P; omega⟩
      have := (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) D).mul
        (he.mul (intAt_sum Finset.univ fun j _ => (hy' j).mul (h j (Br.iL (N_m_succ R))).2.1))
      convert this using 1
      rw [hD, pow_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := hc.psi_add P _ _ hz ((intAt_pow (intAt_nat (P := P.1) (qOf P.1)) _).mul hd)
    rw [hc.psi_int P _ hd, mul_one] at this
    rw [← this]
    congr 1
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
    ring

theorem locTop_inv (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2) (κ : GLint X.E (R.N R.m) P.1) (hκ : redGL _ P.1 κ = 1)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {y' : Sp X.E (R.N (m2 + 1))} (hy' : ∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) :
    locTop Ch sel mu cst m2 P (κ.1.toLinearMap ∘ₗ y) y' = locTop Ch sel mu cst m2 P y y' := by
  by_cases hy : ∀ s, y (Pi.single s 1) ∈ stdAt X.E (R.N R.m) P.1
  · refine locTop_congr hm hc hP hy' fun s l => ?_
    have h1 := mem_stdAt.1 (glint_mem κ (hy s)) l
    have h2 := mem_stdAt.1 (hy s) l
    refine ⟨h1, h2, intAt_div_of_redP hq (intAt_sub h1 h2) ?_⟩
    have h3 := congrFun (redV_redGL κ (hy s)) l
    rw [hκ, Units.val_one, Matrix.one_mulVec] at h3
    exact (reduction_sub h1 h2).trans (sub_eq_zero.2 h3)
  · have h1 : locTop Ch sel mu cst m2 P y y' = 0 := by
      by_contra h
      exact hy (locTop_supp hm hP h)
    have h2 : locTop Ch sel mu cst m2 P (κ.1.toLinearMap ∘ₗ y) y' = 0 := by
      by_contra h
      exact hy fun s => (κ.2 _).1 (locTop_supp hm hP h s)
    rw [h1, h2]

theorem repY_int {j : ℕ} (p : ChPt (R := R) sel mu u j) {Y : Set (Sp X.E (R.N j))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N)
    {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) (i : Fin (R.N j)) :
    IntAt P.1 ((qOf P.1 : X.E) * (frsF sel mu p P).symm (repY Y) i) := by
  obtain ⟨y, hy, hY⟩ := hY
  have hne : ∃ z, z ∈ Y := ⟨y, by rw [hY, Set.mem_ofPred_eq, sub_self]; exact zero_mem _⟩
  have h1 : repY Y ∈ Y := Classical.epsilon_spec hne
  have h1' : repY Y - y ∈ locLat (rowSG Pr sel mu) p.deco.1.N _ := (Set.ext_iff.1 hY _).1 h1
  have h2 := (mem_locLat _ _ _ _).1 h1' P
  have h3 := (mem_locLat _ _ _ _).1 hy P
  simp only [if_pos hP, zpow_zero, inv_one, one_smul, zpow_neg, zpow_one, inv_inv] at h2 h3
  have h4 : (qOf P.1 : X.E) • repY Y ∈ p.deco.1.at P.1 := by
    have := add_mem (smul_mem_locP (intAt_nat (P := P.1) (qOf P.1)) h2) h3
    rwa [← smul_add, sub_add_cancel] at this
  have h5 := (frsF_mem p P ((frsF sel mu p P).symm ((qOf P.1 : X.E) • repY Y))).1 (by rwa [LinearEquiv.apply_symm_apply])
  rw [map_smul] at h5
  exact mem_stdAt.1 h5 i

theorem locTop_tilFr (H : TilOk Pr sel mu u) (d : RowPt Pr R sel mu) (P : rowSG Pr sel mu)
    (f : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (y' : Sp X.E (R.N (m2 + 1))) :
    locTop Ch sel mu cst m2 P (inFr f (tilFr H d P) x) y' =
      PhiTop Ch mu cst.sharp m2 P.1 ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ f.toLinearMap ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
        ftY sel mu cst P ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ f.toLinearMap) y' := by
  unfold locTop
  congr 2
  · exact LinearMap.ext fun v => prH_sumE_symm (N_m_succ R) _ _ _
  · refine LinearMap.ext fun v => (atNL_last _).trans ((sumE_symm_last (N_m_succ R) _ _ _).trans ?_)
    exact congrArg (fun t => ((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * t) (atNL_last (x (f v))).symm

theorem XiTop_tilTop (hX : X.Ok) (hPr : Pr.Ok) (hm : R.m = m2 + 2) (hc : cst.Ok) (H : TilOk Pr sel mu u)
    (p : ChPt (R := R) sel mu u (m2 + 1)) {Y : Set (Sp X.E (R.N (m2 + 1)))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N)
    (d : RowPt Pr R sel mu) : XiTop Ch sel mu cst m2 p Y (tilTop H d) = XiCpl2 Ch sel mu cst m2 p Y d := by
  funext x
  unfold XiTop XiCpl2
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun P _ => ?_)
  rw [← locTop_tilFr H]
  by_cases hP : P.1 ∈ Pr.vGs
  · obtain ⟨κ, hκ, e⟩ := exists_of_isLiftFr (tilFr_isLiftFr H d P) (liftFr_spec (tilQ sel mu u d).2 P)
    rw [frsF_tilTop_g H d P hP, ← locTop_inv hm hc hP (qOf_notMem_sq hX hPr hP) κ hκ (inFr _ (tilFr H d P) x) (repY_int p hY hP), e]
    congr 1
    refine LinearMap.ext fun v => ?_
    show _ = κ.1 (κ.1.symm _)
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · rw [frsF_tilTop_Q H d P hP]

variable {W} in

theorem k2top_tilTop (hX : X.Ok) (hPr : Pr.Ok) (hm : R.m = m2 + 2) (hc : cst.Ok) (H : TilOk Pr sel mu u) {T : ChTh W sel mu u m2}
    (hT : TameFr T.top) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu) :
    topDegreeKTwo W Ch sel mu cst T p Y (tilTop H d) = cp2K W Ch sel mu cst T p Y d := by
  unfold topDegreeKTwo cp2K
  split_ifs with hY
  · have hκ : ∀ P : rowSG Pr sel mu, ∃ κ : GLint X.E (R.N R.m) P.1, redGL _ P.1 κ = 1 ∧
        frsF sel mu (tilTop H d) P = frsT sel mu u d P * κ.1 := fun P => by
      by_cases hP : P.1 ∈ Pr.vGs
      · exact ⟨1, map_one _, (frsF_tilTop_g H d P hP).trans (mul_one _).symm⟩
      · rw [frsF_tilTop_Q H d P hP]
        exact exists_of_isLiftFr (tilFr_isLiftFr H d P) (liftFr_spec (tilQ sel mu u d).2 P)
    choose κ hκ e using hκ
    rw [XiTop_tilTop hX hPr hm hc H p hY, funext e]
    unfold kerOf
    refine congrArg (latSum _ _) (funext fun x => congrArg _ ?_)
    exact hT _ _ _ _ _ _ κ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ hκ
  · rfl

end Ker

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (P : LevFam X.E X.K R.r Pr.vGs) (c : TopDepth R cst.M)

def TopEquiv : Prop :=
  CplEq2 (S := midGSD W sel mu L u m2 b) (S₁ := topGSD W Ch sel mu P u c) (ybCpl W sel mu cst L u m2 b hY) (topDegreeKTwo W Ch sel mu cst T)

def TopEquivOn : Prop :=
  CplEq2On (S := midGSD W sel mu L u m2 b) (S₁ := topGSD W Ch sel mu P u c) (ybCpl W sel mu cst L u m2 b hY) (topDegreeKTwo W Ch sel mu cst T)

variable {W Ch sel mu cst L T b hY P c}

theorem topEquiv_iff_on : TopEquiv W Ch sel mu cst L T b hY P c ↔ TopEquivOn W Ch sel mu cst L T b hY P c := by
  refine ⟨fun h g g₁ p Y p' _ => h g g₁ p Y p', fun h g g₁ p Y p' => ?_⟩
  by_cases hp : Y ∈ (ybCpl W sel mu cst L u m2 b hY).ys p
  · exact h g g₁ p Y p' hp
  · have h1 : topDegreeKTwo W Ch sel mu cst T p Y p' = 0 := if_neg hp
    have h2 : topDegreeKTwo W Ch sel mu cst T (g • p) ((fun v => g.1.1 v) '' Y) (g₁ • p') = 0 :=
      if_neg fun hh => hp (((ybCpl W sel mu cst L u m2 b hY).equiv g p Y).1 hh)
    refine h2.trans ?_
    rw [h1, LinearMap.zero_comp, LinearMap.comp_zero]

theorem TopEquiv.cp2Equiv (h : TopEquiv W Ch sel mu cst L T b hY P c) (hX : X.Ok) (hPr : Pr.Ok) (hm : R.m = m2 + 2) (hc : cst.Ok)
    (H : TilOk Pr sel mu u) (hT : TameFr T.top) : Cp2Equiv W Ch sel mu cst L T b hY P := by
  intro g g₁ p Y d
  have h1 := h g (tilEl H c.pos g₁ d) p Y (tilTop H d)
  rw [tilEl_rho] at h1
  have e1 := k2top_tilTop (Ch := Ch) hX hPr hm hc H hT p Y d
  have e2 := k2top_tilTop (Ch := Ch) hX hPr hm hc H hT (g • p) ((fun v => g.1.1 v) '' Y) (g₁ • d)
  rw [← tilEl_smul H c.pos g₁ d] at e2
  refine e2.symm.trans (h1.trans ?_)
  rw [e1]
  rfl

def topCpl (h1 : Cp1Equiv W Ch sel mu cst L T b hY) (h2 : TopEquiv W Ch sel mu cst L T b hY P c) (al : L.β m2) :
    CplKer ((chF W sel mu L u m2).mem al) (midGSD W sel mu L u m2 b) (topGSD W Ch sel mu P u c) (ybCpl W sel mu cst L u m2 b hY) :=
  CplKer.mk (cp1K W Ch sel mu cst L T al) (topDegreeKTwo W Ch sel mu cst T) (h1 al) h2

open Classical in

def matFam (hM : MatEquiv W Ch sel mu cst L T) : KerFam (chF W sel mu L u) := fun i al be =>
  if h : i < m2 then ClsKer.mk (matK W Ch sel mu cst L T i al be) (hM i h al be) else zeroKer _ _

def colTop (hM : MatEquiv W Ch sel mu cst L T) (h1 : Cp1Equiv W Ch sel mu cst L T b hY) (h2 : TopEquiv W Ch sel mu cst L T b hY P c)
    (hF : ∀ j, (chF W sel mu L u j).Ok) {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) :
    MfV W Ch u →ₗ[X.K] (topGSD W Ch sel mu P u c).EqFun :=
  colCpl (matFam hM) hF m2 (topCpl h1 h2) (hF (m2 + 1) b) ∘ₗ startC hL u

end Col

section Checks

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

instance (u : Pr.Word) : Nonempty (TopPt R sel mu u) :=
  haveI : NeZero (R.N R.m) := ⟨(R.N_pos _).ne'⟩
  ⟨DecoF.base _ _ _ _ _⟩

example (hPr : Pr.Ok) (u : Pr.Word) : TilOk Pr sel (mu0 X.F X.E X.K S) u :=
  tilOk_of hPr u fun P hP => by
    rw [twistPrimes_trivialTuple_empty] at hP
    simp at hP


example (R : Ranks) (h : R.m = 2) : (default : TopDepth R 1).1 = 9 ∧ (default : TopDepth R 5).1 = 14 := by
  constructor
  · show max (4 * R.m + 1) (2 * R.m + 2 * 1) = 9
    rw [h]; rfl
  · show max (4 * R.m + 1) (2 * R.m + 2 * 5) = 14
    rw [h]; rfl

end Checks

end GlobalTheory.TopStep
end
end
