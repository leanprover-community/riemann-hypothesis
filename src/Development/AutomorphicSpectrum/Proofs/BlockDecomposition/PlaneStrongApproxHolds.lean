import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemSupp
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneApproxOfQuaternionApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrongApproxClosureMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportProductOverPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionNeighbourhood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDense
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDenseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjClosure

section
noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Ring

variable {S : Type} [CommRing S] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def emb0 (V : Matrix m n S) (P : Matrix n m S) (x : Matrix n n S) : Matrix m m S :=
  1 + V * (x - 1) * P

structure IsFrame (c : S →+* S) (J : Matrix m m S) (K : Matrix n n S) (a : S) (V : Matrix m n S)
    (P : Matrix n m S) : Prop where
  pv : P * V = 1
  jv : J * V = a • (cT c P * K)
  vj : cT c V * J = a • (K * P)

theorem cT_add (c : S →+* S) {p q : Type} (X Y : Matrix p q S) : cT c (X + Y) = cT c X + cT c Y := by
  ext i j; simp [cT]

theorem cT_sub (c : S →+* S) {p q : Type} (X Y : Matrix p q S) : cT c (X - Y) = cT c X - cT c Y := by
  ext i j; simp [cT]

theorem frame_embedding_one (V : Matrix m n S) (P : Matrix n m S) : emb0 V P 1 = 1 := by simp [emb0]

theorem embed_mul {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x y : Matrix n n S) :
    emb0 V P (x * y) = emb0 V P x * emb0 V P y := by
  have e : V * (x - 1) * P * (V * (y - 1) * P) = V * ((x - 1) * (y - 1)) * P := by
    calc V * (x - 1) * P * (V * (y - 1) * P) = V * (x - 1) * (P * V) * (y - 1) * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [emb0, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e]
  have e2 : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by noncomm_ring
  rw [e2]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

def embHom {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) : Matrix n n S →* Matrix m m S where
  toFun := emb0 V P
  map_one' := frame_embedding_one V P
  map_mul' := embed_mul h

theorem det_frame_embedding {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x : Matrix n n S) :
    (emb0 V P x).det = x.det := by
  have e : emb0 V P x = 1 + V * ((x - 1) * P) := by rw [emb0, Matrix.mul_assoc]
  rw [e, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]
  simp

theorem projection_frame_embedding {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x : Matrix n n S) :
    P * emb0 V P x * V = x := by
  have e : P * (1 + V * (x - 1) * P) * V = P * V + (P * V) * (x - 1) * (P * V) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [emb0, e, h]
  simp

theorem conj_transpose_frame_embedding (c : S →+* S) (V : Matrix m n S) (P : Matrix n m S) (x : Matrix n n S) :
    cT c (emb0 V P x) = 1 + cT c P * (cT c x - 1) * cT c V := by
  rw [emb0, cT_add, cT_one, cT_mul, cT_mul, cT_sub, cT_one, Matrix.mul_assoc]

theorem frame_embedding_form_defect {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) (x : Matrix n n S) :
    cT c (emb0 V P x) * J * emb0 V P x = J + a • (cT c P * (cT c x * K * x - K) * P) := by
  have hvjv : cT c V * J * V = a • K := by
    rw [h.vj, Matrix.smul_mul, Matrix.mul_assoc, h.pv, Matrix.mul_one]
  set A := x - 1 with hA
  set B := cT c x - 1 with hB
  have hx : x = A + 1 := by rw [hA]; abel
  have hcx : cT c x = B + 1 := by rw [hB]; abel
  have e1 : cT c x * K * x - K = K * A + B * K + B * K * A := by
    rw [hcx, hx]; noncomm_ring
  have t1 : J * (V * A * P) = a • (cT c P * (K * A) * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.jv]
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  have t2 : cT c P * B * cT c V * J = a • (cT c P * (B * K) * P) := by
    rw [Matrix.mul_assoc _ (cT c V) J, h.vj]
    simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have t3 : cT c P * B * cT c V * J * (V * A * P) = a • (cT c P * (B * K * A) * P) := by
    calc cT c P * B * cT c V * J * (V * A * P) = cT c P * B * (cT c V * J * V) * A * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hvjv]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [conj_transpose_frame_embedding, ← hB, emb0, ← hA, e1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_add]
  rw [t3, t2, t1]
  abel

theorem frame_embedding_unitary {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) {x : Matrix n n S} (hx : cT c x * K * x = K) :
    cT c (emb0 V P x) * J * emb0 V P x = J := by
  rw [frame_embedding_form_defect h, hx]; simp

theorem unitary_of_frame_embedding {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a b : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) (hab : b * a = 1) {x : Matrix n n S}
    (hx : cT c (emb0 V P x) * J * emb0 V P x = J) : cT c x * K * x = K := by
  rw [frame_embedding_form_defect h] at hx
  have h0 : a • (cT c P * (cT c x * K * x - K) * P) = 0 := by simpa using hx
  have hvp : cT c V * cT c P = 1 := by rw [← cT_mul, h.pv, cT_one]
  have h1 : a • (cT c x * K * x - K) = 0 := by
    have := congrArg (fun Y => cT c V * Y * V) h0
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_zero, Matrix.zero_mul] at this
    have e : cT c V * (cT c P * (cT c x * K * x - K) * P) * V =
        (cT c V * cT c P) * (cT c x * K * x - K) * (P * V) := by simp only [Matrix.mul_assoc]
    rwa [e, hvp, h.pv, Matrix.one_mul, Matrix.mul_one] at this
  have h2 : cT c x * K * x - K = 0 := by
    have := congrArg (fun Y => b • Y) h1
    simpa [smul_smul, hab] using this
  exact sub_eq_zero.1 h2

theorem fix_left {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) {L : Matrix m m S} (hL : L * J = 1) {g : Matrix m m S}
    (hg : cT c g * J * g = J) (hq : g * (1 - V * P) = 1 - V * P) : (1 - V * P) * g = 1 - V * P := by
  set q := 1 - V * P with hqd
  have hsym : cT c q * J = J * q := by
    have e1 : cT c q = 1 - cT c P * cT c V := by rw [hqd, cT_sub, cT_one, cT_mul]
    rw [e1, Matrix.sub_mul, Matrix.one_mul, hqd, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, h.vj,
      ← Matrix.mul_assoc J, h.jv]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hstar : cT c q * cT c g = cT c q := by rw [← cT_mul, hq]
  have h1 : J * q * g = J * q := by
    rw [← hsym]
    calc cT c q * J * g = cT c q * cT c g * J * g := by rw [hstar]
      _ = cT c q * (cT c g * J * g) := by simp only [Matrix.mul_assoc]
      _ = cT c q * J := by rw [hg]
  calc q * g = L * (J * q * g) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    _ = q := by rw [h1, ← Matrix.mul_assoc, hL, Matrix.one_mul]

theorem frame_embedding_projection {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) {g : Matrix m m S}
    (h1 : g * (1 - V * P) = 1 - V * P) (h2 : (1 - V * P) * g = 1 - V * P) :
    emb0 V P (P * g * V) = g := by
  set p := V * P with hp
  have hpp : p * p = p := by
    calc p * p = V * (P * V) * P := by simp only [hp, Matrix.mul_assoc]
      _ = p := by rw [h, Matrix.mul_one]
  have a1 : g * p = g - 1 + p := by
    have : g - g * p = 1 - p := by rw [← h1, Matrix.mul_sub, Matrix.mul_one]
    rw [show g * p = g - (g - g * p) by abel, this]; abel
  have a2 : p * g = g - 1 + p := by
    have : g - p * g = 1 - p := by rw [← h2, Matrix.sub_mul, Matrix.one_mul]
    rw [show p * g = g - (g - p * g) by abel, this]; abel
  have e : V * (P * g * V - 1) * P = p * g * p - p := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hp]
    simp only [Matrix.mul_assoc]
  rw [emb0, e, a2, Matrix.add_mul, Matrix.sub_mul, a1, hpp, Matrix.one_mul]
  abel

theorem IsFrame.map {S' : Type} [CommRing S'] {c : S →+* S} {c' : S' →+* S'} (f : S →+* S')
    (hf : ∀ s, f (c s) = c' (f s)) {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) :
    IsFrame c' (J.map f) (K.map f) (f a) (V.map f) (P.map f) := by
  have hc : ∀ {p q : Type} (X : Matrix p q S), cT c' (X.map f) = (cT c X).map f := by
    intro p q X; ext i j; simp [cT, hf]
  have hm : ∀ {p q r : Type} [Fintype q] (X : Matrix p q S) (Y : Matrix q r S),
      X.map f * Y.map f = (X * Y).map f := fun X Y => (Matrix.map_mul (f := f)).symm
  have hs : ∀ {p q : Type} (X : Matrix p q S), f a • X.map f = (a • X).map f := by
    intro p q X; ext i j; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, h.pv]; simp [Matrix.map_one]
  · rw [hm, h.jv, hc, hm, hs]
  · rw [hc, hm, h.vj, hm, hs]

theorem frame_embedding_map {S' : Type} [CommRing S'] (f : S →+* S') (V : Matrix m n S) (P : Matrix n m S)
    (x : Matrix n n S) : (emb0 V P x).map f = emb0 (V.map f) (P.map f) (x.map f) := by
  have h1 : ∀ {k : Type} [DecidableEq k], (1 : Matrix k k S).map f = 1 := fun {k} _ =>
    Matrix.map_one f (map_zero f) (map_one f)
  have hm : ∀ {p q r : Type} [Fintype q] (X : Matrix p q S) (Y : Matrix q r S),
      (X * Y).map f = X.map f * Y.map f := fun X Y => Matrix.map_mul (f := f)
  have hs : (x - 1).map f = x.map f - 1 := by
    have : (x - 1).map f = x.map f - (1 : Matrix n n S).map f := by
      ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
    rw [this, h1]
  have ha : ∀ X Y : Matrix m m S, (X + Y).map f = X.map f + Y.map f := fun X Y => by
    ext i j; simp
  rw [emb0, emb0, ha, h1, hm, hm, hs]

end Ring

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
end

section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Formalism.UG Sa2 Matrix

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Group

variable {S : Type} [CommRing S] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S} {P : Matrix n m S}

def uHom (h : IsFrame c J K a V P) : UJ c K →* UJ c J where
  toFun g := ⟨Units.map (embHom h.pv) g.1, frame_embedding_unitary h g.2⟩
  map_one' := Subtype.ext (map_one (Units.map (embHom h.pv)))
  map_mul' g g' := Subtype.ext (map_mul (Units.map (embHom h.pv)) g.1 g'.1)

theorem exists_preimage (h : IsFrame c J K a V P) {b : S} (hab : b * a = 1) {L : Matrix m m S}
    (hL : L * J = 1) (g : UJ c J) (hq : (g.1 : Matrix m m S) * (1 - V * P) = 1 - V * P) :
    ∃ y : UJ c K, uHom h y = g ∧ (y.1 : Matrix n n S) = P * (g.1 : Matrix m m S) * V := by
  set G : Matrix m m S := (g.1 : Matrix m m S) with hG
  set H : Matrix m m S := ((g⁻¹).1 : Matrix m m S) with hH
  have hHG : H * G = 1 := by
    have e : ((g⁻¹ * g).1 : GL m S) = 1 := by rw [inv_mul_cancel]; rfl
    exact congrArg Units.val e
  have hGH : G * H = 1 := by
    have e : ((g * g⁻¹).1 : GL m S) = 1 := by rw [mul_inv_cancel]; rfl
    exact congrArg Units.val e
  have h1 : (1 - V * P) * G = 1 - V * P := fix_left h hL g.2 hq
  have hq' : H * (1 - V * P) = 1 - V * P := by
    calc H * (1 - V * P) = H * (G * (1 - V * P)) := by rw [hq]
      _ = 1 - V * P := by rw [← Matrix.mul_assoc, hHG, Matrix.one_mul]
  have h1' : (1 - V * P) * H = 1 - V * P := by
    calc (1 - V * P) * H = (1 - V * P) * G * H := by rw [h1]
      _ = 1 - V * P := by rw [Matrix.mul_assoc, hGH, Matrix.mul_one]
  have eG : emb0 V P (P * G * V) = G := frame_embedding_projection h.pv hq h1
  have eH : emb0 V P (P * H * V) = H := frame_embedding_projection h.pv hq' h1'
  have hxy : (P * G * V) * (P * H * V) = 1 := by
    have := projection_frame_embedding h.pv ((P * G * V) * (P * H * V))
    rw [embed_mul h.pv, eG, eH, hGH, Matrix.mul_one, h.pv] at this
    exact this.symm
  have hyx : (P * H * V) * (P * G * V) = 1 := by
    have := projection_frame_embedding h.pv ((P * H * V) * (P * G * V))
    rw [embed_mul h.pv, eG, eH, hHG, Matrix.mul_one, h.pv] at this
    exact this.symm
  let x : GL n S := ⟨P * G * V, P * H * V, hxy, hyx⟩
  have hb : IsFrame c J K a V P := h
  have hu : cT c (x : Matrix n n S) * K * (x : Matrix n n S) = K := by
    refine unitary_of_frame_embedding h hab ?_
    change cT c (emb0 V P (P * G * V)) * J * emb0 V P (P * G * V) = J
    rw [eG]
    exact g.2
  refine ⟨⟨x, hu⟩, Subtype.ext (Units.ext eG), rfl⟩

end Group

section Basis

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem conj_conj [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_of_conj_eq [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ t : F, algebraMap F E t = x := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  haveI := h.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h1 | h1
  · have : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
    rw [h1] at this
    exact Algebra.mem_bot.1 this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := h1 ▸ Algebra.mem_top
    have hy' : σ y = y := hy
    have := h.2.2.2 τ y
    rw [hy'] at this
    exact this.symm

variable {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem hf_add_right (x y z : Fin M → E) : hf σ J x (y + z) = hf σ J x y + hf σ J x z := by
  simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (t : E) (x y : Fin M → E) : hf σ J x (t • y) = t * hf σ J x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_add_left (x y z : Fin M → E) : hf σ J (x + y) z = hf σ J x z + hf σ J y z := by
  simp only [hf, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left (t : E) (x y : Fin M → E) : hf σ J (t • x) y = σ t * hf σ J x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_conj (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → E) :
    σ (hf σ J x y) = hf σ J y x := by
  simp only [hf, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem orth_of_ne (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (hfix : ∀ x : E, σ x = x → ∃ t : F, algebraMap F E t = x) {w₀ w₁ : Fin M → E}
    (hp : hf σ J w₀ w₀ ≠ 0) (hd : PlaneND σ J w₀ w₁) :
    ∃ (v₀ v₁ : Fin M → E) (a b : F), a ≠ 0 ∧ b ≠ 0 ∧ hf σ J v₀ v₀ = algebraMap F E a ∧
      hf σ J v₁ v₁ = algebraMap F E b ∧ hf σ J v₀ v₁ = 0 ∧ hf σ J v₁ v₀ = 0 ∧
      ∀ x, (hf σ J w₀ x = 0 ∧ hf σ J w₁ x = 0) ↔ (hf σ J v₀ x = 0 ∧ hf σ J v₁ x = 0) := by
  set p := hf σ J w₀ w₀ with hpd
  set q := hf σ J w₀ w₁ with hqd
  set t := q / p with ht
  have hσp : σ p = p := hf_conj hσ hJ w₀ w₀
  have hσq : σ q = hf σ J w₁ w₀ := hf_conj hσ hJ w₀ w₁
  set v₁ : Fin M → E := w₁ + (-t) • w₀ with hv₁
  have h01 : hf σ J w₀ v₁ = 0 := by
    rw [hv₁, hf_add_right, hf_smul_right, ← hqd, ← hpd, ht]
    field_simp
    ring
  have h10 : hf σ J v₁ w₀ = 0 := by
    rw [← hf_conj hσ hJ w₀ v₁, h01, map_zero]
  have h11 : hf σ J v₁ v₁ = (p * hf σ J w₁ w₁ - q * σ q) / p := by
    have e : hf σ J v₁ v₁ = hf σ J w₁ v₁ := by
      conv_lhs => rw [hv₁, hf_add_left, hf_smul_left]
      rw [← hv₁, h01, mul_zero, add_zero]
    rw [e, hv₁, hf_add_right, hf_smul_right, ← hσq, ht]
    field_simp
    ring
  have hb : hf σ J v₁ v₁ ≠ 0 := by
    rw [h11]
    refine div_ne_zero ?_ hp
    rw [hσq]
    exact hd
  obtain ⟨a, ha⟩ := hfix p hσp
  obtain ⟨b, hb'⟩ := hfix _ (hf_conj hσ hJ v₁ v₁)
  refine ⟨w₀, v₁, a, b, ?_, ?_, ha.symm, hb'.symm, h01, h10, fun x => ?_⟩
  · rintro rfl; exact hp (by rw [← ha, map_zero])
  · rintro rfl; exact hb (by rw [← hb', map_zero])
  · have e : hf σ J v₁ x = hf σ J w₁ x + σ (-t) * hf σ J w₀ x := by
      rw [hv₁, hf_add_left, hf_smul_left]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0, by rw [e, h0, h1]; simp⟩
    · rintro ⟨h0, h1⟩
      refine ⟨h0, ?_⟩
      rw [e, h0] at h1
      simpa using h1

theorem exists_orth (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (hfix : ∀ x : E, σ x = x → ∃ t : F, algebraMap F E t = x) {u₀ u₁ : Fin M → E}
    (hd : PlaneND σ J u₀ u₁) :
    ∃ (v₀ v₁ : Fin M → E) (a b : F), a ≠ 0 ∧ b ≠ 0 ∧ hf σ J v₀ v₀ = algebraMap F E a ∧
      hf σ J v₁ v₁ = algebraMap F E b ∧ hf σ J v₀ v₁ = 0 ∧ hf σ J v₁ v₀ = 0 ∧
      ∀ x, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ (hf σ J v₀ x = 0 ∧ hf σ J v₁ x = 0) := by
  by_cases hp : hf σ J u₀ u₀ = 0
  · by_cases hr : hf σ J u₁ u₁ = 0
    ·
      set q := hf σ J u₀ u₁ with hqd
      have hσq : σ q = hf σ J u₁ u₀ := hf_conj hσ hJ u₀ u₁
      have hq : q * σ q ≠ 0 := by
        intro h0
        apply hd
        rw [hp, hr, ← hσq, ← hqd, h0]; simp
      set w₀ : Fin M → E := u₀ + σ q • u₁ with hw
      have e1 : hf σ J w₀ u₁ = q := by
        rw [hw, hf_add_left, hf_smul_left, hr, mul_zero, add_zero]
      have e2 : hf σ J u₁ w₀ = σ q := by
        rw [hw, hf_add_right, hf_smul_right, hr, mul_zero, add_zero, hσq]
      have e3 : hf σ J w₀ w₀ = 2 * (q * σ q) := by
        conv_lhs => rw [hw, hf_add_right, hf_smul_right]
        rw [← hw, e1, hw, hf_add_left, hf_smul_left, hp, ← hσq, hσ, zero_add]
        ring
      have hw0 : hf σ J w₀ w₀ ≠ 0 := by
        haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
        rw [e3]; exact mul_ne_zero two_ne_zero hq
      have hnd : PlaneND σ J w₀ u₁ := by
        change hf σ J w₀ w₀ * hf σ J u₁ u₁ - hf σ J w₀ u₁ * hf σ J u₁ w₀ ≠ 0
        rw [hr, e1, e2, mul_zero, zero_sub]
        exact neg_ne_zero.2 hq
      obtain ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, h5⟩ := orth_of_ne hσ hJ hfix hw0 hnd
      refine ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, fun x => Iff.trans ?_ (h5 x)⟩
      have e : hf σ J w₀ x = hf σ J u₀ x + σ (σ q) * hf σ J u₁ x := by
        rw [hw, hf_add_left, hf_smul_left]
      constructor
      · rintro ⟨h0, h1⟩
        exact ⟨by rw [e, h0, h1]; simp, h1⟩
      · rintro ⟨h0, h1⟩
        refine ⟨?_, h1⟩
        rw [e, h1] at h0
        simpa using h0
    · have hnd : PlaneND σ J u₁ u₀ := by
        have : hf σ J u₁ u₁ * hf σ J u₀ u₀ - hf σ J u₁ u₀ * hf σ J u₀ u₁ =
            hf σ J u₀ u₀ * hf σ J u₁ u₁ - hf σ J u₀ u₁ * hf σ J u₁ u₀ := by ring
        change hf σ J u₁ u₁ * hf σ J u₀ u₀ - hf σ J u₁ u₀ * hf σ J u₀ u₁ ≠ 0
        rw [this]
        exact hd
      obtain ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, h5⟩ := orth_of_ne hσ hJ hfix hr hnd
      exact ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, fun x => Iff.trans and_comm (h5 x)⟩
  · exact orth_of_ne hσ hJ hfix hp hd

end Basis

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

def rowJ (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (v : Fin M → E) (j : Fin M) : E :=
  ∑ i, σ (v i) * J i j

theorem sum_row (t : E) (x y : Fin M → E) : ∑ j, (t * rowJ σ J x j) * y j = t * hf σ J x y := by
  simp only [hf, rowJ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem conj_row (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (v : Fin M → E) (i : Fin M) :
    σ (rowJ σ J v i) = ∑ j, J i j * v j := by
  simp only [rowJ, map_sum, map_mul, hσ, hJ]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_frame (hcm : IsCMExt F E σ) (hJ : IsHermND σ J) {u₀ u₁ : Fin M → E} (hd : PlaneND σ J u₀ u₁) :
    ∃ (β : F) (a : E) (V : Matrix (Fin M) (Fin 2) E) (P : Matrix (Fin 2) (Fin M) E),
      β ≠ 0 ∧ a ≠ 0 ∧ IsFrame (σ : E →+* E) J (J2 E β) a V P ∧
      ∀ x : Fin M → E, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ P.mulVec x = 0 := by
  have hσ := conj_conj hcm
  obtain ⟨v₀, v₁, a, b, ha, hb, h1, h2, h3, h4, h5⟩ :=
    exists_orth hσ hJ.1 (fun x hx => exists_of_conj_eq hcm hx) hd
  set A := algebraMap F E a with hAd
  set B := algebraMap F E b with hBd
  have hA : A ≠ 0 := by rw [hAd]; exact (map_ne_zero _).2 ha
  have hB : B ≠ 0 := by rw [hBd]; exact (map_ne_zero _).2 hb
  have hσA : σ A = A := σ.commutes a
  have hσB : σ B = B := σ.commutes b
  let V : Matrix (Fin M) (Fin 2) E := fun i k => ![v₀ i, v₁ i] k
  let P : Matrix (Fin 2) (Fin M) E := fun k j => ![A⁻¹ * rowJ σ J v₀ j, B⁻¹ * rowJ σ J v₁ j] k
  have hK : J2 E (-b / a) = !![1, 0; 0, B / A] := by
    simp [J2, map_div₀, map_neg, hAd, hBd, neg_div]
  refine ⟨-b / a, A, V, P, div_ne_zero (neg_ne_zero.2 hb) ha, hA, ⟨?_, ?_, ?_⟩, fun x => (h5 x).trans ?_⟩
  · rw [Matrix.one_fin_two]
    refine Matrix.ext fun k l => ?_
    rw [Matrix.mul_apply]
    fin_cases k <;> fin_cases l
    · change ∑ j, (A⁻¹ * rowJ σ J v₀ j) * v₀ j = 1
      rw [sum_row, h1, inv_mul_cancel₀ hA]
    · change ∑ j, (A⁻¹ * rowJ σ J v₀ j) * v₁ j = 0
      rw [sum_row, h3, mul_zero]
    · change ∑ j, (B⁻¹ * rowJ σ J v₁ j) * v₀ j = 0
      rw [sum_row, h4, mul_zero]
    · change ∑ j, (B⁻¹ * rowJ σ J v₁ j) * v₁ j = 1
      rw [sum_row, h2, inv_mul_cancel₀ hB]
  · rw [hK]
    refine Matrix.ext fun i k => ?_
    rw [Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases k
    · change ∑ j, J i j * v₀ j = A • (σ (A⁻¹ * rowJ σ J v₀ i) * 1 + σ (B⁻¹ * rowJ σ J v₁ i) * 0)
      simp only [map_mul, map_inv₀, RingHom.coe_coe, hσA, conj_row hσ hJ.1, smul_eq_mul]
      field_simp
      simp
    · change ∑ j, J i j * v₁ j = A • (σ (A⁻¹ * rowJ σ J v₀ i) * 0 + σ (B⁻¹ * rowJ σ J v₁ i) * (B / A))
      simp only [map_mul, map_inv₀, hσB, conj_row hσ hJ.1, smul_eq_mul]
      field_simp
      simp
  · rw [hK]
    refine Matrix.ext fun k j => ?_
    rw [Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases k
    · change ∑ i, σ (v₀ i) * J i j = A • (1 * (A⁻¹ * rowJ σ J v₀ j) + 0 * (B⁻¹ * rowJ σ J v₁ j))
      change rowJ σ J v₀ j = _
      simp only [smul_eq_mul]
      field_simp
      simp
    · change ∑ i, σ (v₁ i) * J i j = A • (0 * (A⁻¹ * rowJ σ J v₀ j) + (B / A) * (B⁻¹ * rowJ σ J v₁ j))
      change rowJ σ J v₁ j = _
      simp only [smul_eq_mul]
      field_simp
      simp
  · have e0 : P.mulVec x 0 = A⁻¹ * hf σ J v₀ x := sum_row _ _ _
    have e1 : P.mulVec x 1 = B⁻¹ * hf σ J v₁ x := sum_row _ _ _
    constructor
    · rintro ⟨g0, g1⟩
      funext k
      fin_cases k
      · change P.mulVec x 0 = 0
        rw [e0, g0, mul_zero]
      · change P.mulVec x 1 = 0
        rw [e1, g1, mul_zero]
    · intro g
      have g0 := congrFun g 0
      have g1 := congrFun g 1
      rw [e0] at g0
      rw [e1] at g1
      exact ⟨by simpa [hA] using g0, by simpa [hB] using g1⟩

end Frame

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology Sa2 Matrix
  GlobalTheory.CompanionTheory.StrongApproxSub
open Formalism.UG (UJ bc)
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {K : Matrix (Fin 2) (Fin 2) E} {a : E}
  {V : Matrix (Fin M) (Fin 2) E} {P : Matrix (Fin 2) (Fin M) E}

theorem sig_incl (e : E) :
    inclR (F := F) (E := E) (AF F) ((σ : E →+* E) e) = sigR (AF F) σ (inclR (F := F) (E := E) (AF F) e) := by
  simp [sigR, inclR]

theorem frameA (h : IsFrame (σ : E →+* E) J K a V P) :
    IsFrame (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) K) (inclR (F := F) (E := E) (AF F) a) (V.map (inclR (F := F) (E := E) (AF F)))
      (P.map (inclR (F := F) (E := E) (AF F))) :=
  h.map (inclR (F := F) (E := E) (AF F)) sig_incl

def iota (h : IsFrame (σ : E →+* E) J K a V P) : HA (AF F) σ K →* HA (AF F) σ J :=
  uHom (frameA h)

theorem mt_iota (h : IsFrame (σ : E →+* E) J K a V P) (g : HA (AF F) σ K) :
    mt (iota h g) = emb0 (V.map (inclR (F := F) (E := E) (AF F))) (P.map (inclR (F := F) (E := E) (AF F))) (mt g) := rfl

theorem continuous_iota (h : IsFrame (σ : E →+* E) J K a V P) :
    Continuous (iota (F := F) h) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous (embHom (frameA (F := F) h).pv) :=
    continuous_const.add (((continuous_const.matrix_mul
      (continuous_id.sub continuous_const))).matrix_mul continuous_const)
  have hu := Continuous.units_map _ hm
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

theorem iota_adelic (h : IsFrame (σ : E →+* E) J K a V P) {g : HA (AF F) σ K}
    (hg : g ∈ SUAdelic σ K) : iota h g ∈ SUAdelic σ J := by
  refine StrongApprox.mem_SUAdelic.2 ?_
  have := StrongApprox.mem_SUAdelic.1 hg
  change (mt (iota h g)).det = 1
  rw [mt_iota, det_frame_embedding (frameA h).pv]
  exact this

theorem iota_rat (h : IsFrame (σ : E →+* E) J K a V P) {γ : HA (AF F) σ K}
    (hγ : γ ∈ SURat σ K) : iota h γ ∈ SURat σ J := by
  refine ⟨iota_adelic h hγ.1, ?_⟩
  obtain ⟨u, hu, e⟩ : (γ : HR (AF F) σ K).1 ∈ (UJ (σ : E →+* E) K).map (bc (inclR (F := F) (E := E) (AF F))) := hγ.2
  change (iota h γ : HR (AF F) σ J).1 ∈ (UJ (σ : E →+* E) J).map (bc (inclR (F := F) (E := E) (AF F)))
  refine ⟨(uHom h ⟨u, hu⟩).1, (uHom h ⟨u, hu⟩).2, Units.ext ?_⟩
  have e' : ((γ : HR (AF F) σ K).1 : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) =
      (u : Matrix (Fin 2) (Fin 2) E).map (inclR (F := F) (E := E) (AF F)) := by
    rw [← e]; rfl
  change (emb0 V P (u : Matrix (Fin 2) (Fin 2) E)).map (inclR (F := F) (E := E) (AF F)) =
    emb0 (V.map (inclR (F := F) (E := E) (AF F))) (P.map (inclR (F := F) (E := E) (AF F)))
      ((γ : HR (AF F) σ K).1 : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E))
  rw [e']
  exact frame_embedding_map _ _ _ _

theorem iota_supp (h : IsFrame (σ : E →+* E) J K a V P) {u₀ u₁ : Fin M → E}
    (hP : ∀ x : Fin M → E, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ P.mulVec x = 0) {ε : AF F}
    {g : HA (AF F) σ K} (hg : g ∈ SUSupp σ K ε) : iota h g ∈ PlaneSupp σ J ε u₀ u₁ := by
  obtain ⟨g1, g2⟩ := mem_SUSupp.1 hg
  refine ⟨mem_SUSupp.2 ⟨iota_adelic h g1, ?_⟩, fun x h0 h1 => ?_⟩
  · have e : mt (iota h g) - 1 =
        V.map (inclR (F := F) (E := E) (AF F)) * (mt g - 1) * P.map (inclR (F := F) (E := E) (AF F)) := by
      rw [mt_iota, emb0, add_sub_cancel_left]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, g2]
  · have hx : P.mulVec x = 0 := (hP x).1 ⟨h0, h1⟩
    have hv : (P.map (inclR (F := F) (E := E) (AF F))).mulVec (vA x) = 0 := by
      funext k
      have := RingHom.map_mulVec (inclR (F := F) (E := E) (AF F)) P x k
      rw [hx] at this
      have e : vA (F := F) x = (inclR (F := F) (E := E) (AF F)) ∘ x := rfl
      rw [e]
      simpa using this.symm
    change (mt (iota h g)).mulVec (vA x) = vA x
    rw [mt_iota, emb0, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_zero, add_zero]

theorem iota_surj (h : IsFrame (σ : E →+* E) J K a V P) (ha : a ≠ 0) (hJ : J.det ≠ 0) {u₀ u₁ : Fin M → E}
    (hP : ∀ x : Fin M → E, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ P.mulVec x = 0) {δ : AF F}
    {g : HA (AF F) σ J} (hg : g ∈ PlaneSupp σ J δ u₀ u₁) : ∃ y ∈ SUSupp σ K δ, iota h y = g := by
  obtain ⟨g1, g2⟩ := hg
  obtain ⟨g1a, g1b⟩ := mem_SUSupp.1 g1
  have hq0 : P * (1 - V * P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h.pv, Matrix.one_mul, sub_self]
  have hmap : 1 - V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F)) = (1 - V * P).map (inclR (F := F) (E := E) (AF F)) := by
    have h1 : (1 : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (E := E) (AF F)) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    have h2 : (V * P).map (inclR (F := F) (E := E) (AF F)) = V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F)) :=
      Matrix.map_mul
    rw [← h1, ← h2]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hq : mt g * (1 - V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F))) =
      1 - V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F)) := by
    rw [hmap]
    ext i j
    have hx : P.mulVec (fun l => (1 - V * P : Matrix (Fin M) (Fin M) E) l j) = 0 := by
      funext k
      exact congrFun (congrFun hq0 k) j
    have := g2 _ ((hP _).2 hx).1 ((hP _).2 hx).2
    exact congrFun this i
  have hab : inclR (F := F) (E := E) (AF F) a⁻¹ * inclR (F := F) (E := E) (AF F) a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have hL : (J⁻¹).map (inclR (F := F) (E := E) (AF F)) * JR (AF F) J = 1 := by
    have e : (J⁻¹).map (inclR (F := F) (E := E) (AF F)) * J.map (inclR (F := F) (E := E) (AF F)) = (J⁻¹ * J).map (inclR (F := F) (E := E) (AF F)) :=
      Matrix.map_mul.symm
    change (J⁻¹).map (inclR (F := F) (E := E) (AF F)) * J.map (inclR (F := F) (E := E) (AF F)) = 1
    rw [e, Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hJ)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨y, hy1', hy2'⟩ : ∃ y : HA (AF F) σ K, iota h y = g ∧
      mt y = P.map (inclR (F := F) (E := E) (AF F)) * mt g * V.map (inclR (F := F) (E := E) (AF F)) :=
    exists_preimage (frameA (F := F) h) hab hL g hq
  refine ⟨y, mem_SUSupp.2 ⟨StrongApprox.mem_SUAdelic.2 ?_, ?_⟩, hy1'⟩
  · have h1 : (mt g).det = 1 := StrongApprox.mem_SUAdelic.1 g1a
    rw [← hy1', mt_iota, det_frame_embedding (frameA h).pv] at h1
    exact h1
  · have e : mt y - 1 =
        P.map (inclR (F := F) (E := E) (AF F)) * (mt g - 1) * V.map (inclR (F := F) (E := E) (AF F)) := by
      rw [hy2', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, (frameA (F := F) h).pv]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, g1b]

end Adelic

theorem plane_prop_of_strong_approx : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ β : F, β ≠ 0 → HermitianPlaneStrongApprox σ β) → Sa2.PropPlane := by
  intro hSA F E _ _ _ _ _ σ hcm M J _ hJ S₁ S₂ ε hε u₀ u₁ hnd hnc T₁ T₂ δ hδ
  obtain ⟨β, a, V, P, hβ, ha, h, hP⟩ := exists_frame hcm hJ hnd
  have img : ∀ η : AF F, PlaneSupp σ J η u₀ u₁ = iota h '' SUSupp σ (J2 E β) η := by
    intro η
    ext g
    constructor
    · intro hg
      obtain ⟨y, hy, e⟩ := iota_surj h ha hJ.2 hP hg
      exact ⟨y, hy, e⟩
    · rintro ⟨y, hy, rfl⟩
      exact iota_supp h hP hy
  have hnc2 : ¬ IsCompact (SUSupp σ (J2 E β) ε) := fun hc =>
    hnc (by rw [img ε]; exact hc.image (continuous_iota h))
  have hcl := hSA F E σ hcm β hβ S₁ S₂ ε hε hnc2 T₁ T₂ δ hδ
  rw [img δ]
  rintro _ ⟨g, hg, rfl⟩
  refine closure_mono ?_ (image_closure_subset_closure_image (continuous_iota h) ⟨g, hcl hg, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, k, hk, rfl⟩, rfl⟩
  exact ⟨iota h γ, iota_rat h hγ, iota h k, (iota_supp h hP hk).1, map_mul _ _ _⟩

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_prop_of_all_strong_approx : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ β : F, β ≠ 0 → HermitianPlaneStrongApprox σ β) → Sa2.PropPlane := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.OfTwo.plane_prop_of_strong_approx
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem cm_exists_sqrt_nonsquare : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∃ d : F, (∀ r : F, r ^ 2 ≠ d) ∧ ∃ ξ : E, ξ ^ 2 = algebraMap F E d ∧ σ ξ = -ξ := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨-, hC, h2, hconj⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)

  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  set τ : E →+* ℂ := w.embedding with hτ

  have hne : ∃ e : E, σ e ≠ e := by
    by_contra hall
    push_neg at hall
    have hreal : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have := hconj τ x
      rw [hall x] at this
      simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex w))
      (InfinitePlace.isReal_iff.mpr hreal)

  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hconj, hconj, star_star]
  obtain ⟨e, he⟩ := hne
  set ξ : E := e - σ e with hξ
  have hξ0 : ξ ≠ 0 := fun h0 => he (sub_eq_zero.mp h0).symm
  have hσξ : σ ξ = -ξ := by
    simp only [hξ, map_sub, hinv, neg_sub]
  have h2E : (2 : E) ≠ 0 := two_ne_zero

  have hli : LinearIndependent F ![(1 : E), ξ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hst' : algebraMap F E s + algebraMap F E t * ξ = 0 := by
      simpa [Algebra.smul_def] using hst
    have hσ' : algebraMap F E s - algebraMap F E t * ξ = 0 := by
      have := congrArg σ hst'
      simpa [map_add, map_mul, AlgHom.commutes, hσξ, sub_eq_add_neg] using this
    have hs : algebraMap F E s = 0 := by
      have : 2 * algebraMap F E s = 0 := by linear_combination hst' + hσ'
      exact (mul_eq_zero.mp this).resolve_left h2E
    have ht : algebraMap F E t * ξ = 0 := by
      have : 2 * (algebraMap F E t * ξ) = 0 := by linear_combination hst' - hσ'
      exact (mul_eq_zero.mp this).resolve_left h2E
    refine ⟨(map_eq_zero _).mp hs, (map_eq_zero _).mp ((mul_eq_zero.mp ht).resolve_right hξ0)⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  have hmem : ξ ^ 2 ∈ Submodule.span F (Set.range ![(1 : E), ξ]) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
  rw [Fin.sum_univ_two] at hc
  have hc' : algebraMap F E (c 0) + algebraMap F E (c 1) * ξ = ξ ^ 2 := by
    simpa [Algebra.smul_def] using hc
  have hc'' : algebraMap F E (c 0) - algebraMap F E (c 1) * ξ = ξ ^ 2 := by
    have := congrArg σ hc'
    simpa [map_add, map_mul, map_pow, AlgHom.commutes, hσξ, sub_eq_add_neg] using this
  have hb : algebraMap F E (c 1) * ξ = 0 := by
    have : 2 * (algebraMap F E (c 1) * ξ) = 0 := by linear_combination hc' - hc''
    exact (mul_eq_zero.mp this).resolve_left h2E
  have hsq : ξ ^ 2 = algebraMap F E (c 0) := by
    rw [← hc', hb, add_zero]
  refine ⟨c 0, ?_, ξ, hsq, hσξ⟩
  intro r hr
  have hfix : ∀ x : F, σ (algebraMap F E x) = algebraMap F E x := σ.commutes
  have hprod : (ξ - algebraMap F E r) * (ξ + algebraMap F E r) = 0 := by
    have : algebraMap F E (c 0) = algebraMap F E r ^ 2 := by rw [← hr, map_pow]
    linear_combination hsq + this
  have hcontra : ξ = -ξ := by
    rcases mul_eq_zero.mp hprod with h0 | h0
    · have hx : ξ = algebraMap F E r := sub_eq_zero.mp h0
      rw [← hσξ, hx, hfix]
    · have hx : ξ = -algebraMap F E r := eq_neg_of_add_eq_zero_left h0
      rw [← hσξ, hx, map_neg, hfix]
  have : 2 * ξ = 0 := by linear_combination hcontra
  exact hξ0 ((mul_eq_zero.mp this).resolve_left h2E)

end GlobalTheory.CompanionTheory.PlaneSA
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_extension_imaginary_generator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∃ d : F, (∀ r : F, r ^ 2 ≠ d) ∧ ∃ ξ : E, ξ ^ 2 = algebraMap F E d ∧ σ ξ = -ξ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.cm_exists_sqrt_nonsquare
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.Split

section Elementary

variable {K : Type*} [Field K]

def nP (D A C B : K) : ℍ[K, D, 0, B] := ⟨0, (2 * D)⁻¹, -C / (2 * B), -A / (2 * D * B)⟩

def nM (D A C B : K) : ℍ[K, D, 0, B] := ⟨0, 2⁻¹, D * C / (2 * B), A / (2 * B)⟩

def toM (D A C B : K) (x : ℍ[K, D, 0, B]) : Matrix (Fin 2) (Fin 2) K :=
  !![x.re + A * x.imJ - D * C * x.imK, D * x.imI + D * C * x.imJ - D * A * x.imK;
     x.imI - C * x.imJ + A * x.imK, x.re - A * x.imJ + D * C * x.imK]

variable {D A C B : K}

theorem toM_mul (hB : B = A ^ 2 - D * C ^ 2) (x y : ℍ[K, D, 0, B]) :
    toM D A C B (x * y) = toM D A C B x * toM D A C B y := by
  subst hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem toM_injective (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0)
    {x y : ℍ[K, D, 0, B]} (h : toM D A C B x = toM D A C B y) : x = y := by
  have h11 : _ = _ := congrFun (congrFun h 0) 0
  have h12 : _ = _ := congrFun (congrFun h 0) 1
  have h21 : _ = _ := congrFun (congrFun h 1) 0
  have h22 : _ = _ := congrFun (congrFun h 1) 1
  simp only [toM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h11 h12 h21 h22
  have hne : 2 * D * B ≠ 0 := mul_ne_zero (mul_ne_zero h2 hD) hB0
  subst hB
  have e1 : x.re = y.re := by
    apply mul_left_cancel₀ h2
    linear_combination h11 + h22
  have e2 : x.imI = y.imI := by
    apply mul_left_cancel₀ (mul_ne_zero h2 hD)
    linear_combination h12 + D * h21
  have e3 : x.imJ = y.imJ := by
    apply mul_left_cancel₀ hne
    linear_combination D * A * (h11 - h22) - D * C * (h12 - D * h21)
  have e4 : x.imK = y.imK := by
    apply mul_left_cancel₀ hne
    linear_combination D * C * (h11 - h22) - A * (h12 - D * h21)
  exact QuaternionAlgebra.ext e1 e2 e3 e4

theorem det_toM (hB : B = A ^ 2 - D * C ^ 2) (x : ℍ[K, D, 0, B]) :
    (toM D A C B x).det = x.re ^ 2 - D * x.imI ^ 2 - B * x.imJ ^ 2 + D * B * x.imK ^ 2 := by
  subst hB
  simp [toM, Matrix.det_fin_two]
  ring

theorem toM_one : toM D A C B (1 : ℍ[K, D, 0, B]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM]

theorem toM_zero : toM D A C B (0 : ℍ[K, D, 0, B]) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM]

theorem toM_nP (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    toM D A C B (nP D A C B) = !![0, 1; 0, 0] := by
  subst hB
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM, nP] <;> field_simp <;> ring

theorem toM_nM (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    toM D A C B (nM D A C B) = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM, nM] <;> field_simp <;> rw [hB] <;> ring

theorem toM_add (x y : ℍ[K, D, 0, B]) : toM D A C B (x + y) = toM D A C B x + toM D A C B y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM] <;> ring

theorem toM_smul (c : K) (x : ℍ[K, D, 0, B]) : toM D A C B (c • x) = c • toM D A C B x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM] <;> ring

theorem toM_uP (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) (c : K) :
    toM D A C B (1 + c • nP D A C B) = !![1, c; 0, 1] := by
  rw [toM_add, toM_smul, toM_nP hB hD hB0 h2, toM_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem toM_uM (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) (c : K) :
    toM D A C B (1 + c • nM D A C B) = !![1, 0; c, 1] := by
  rw [toM_add, toM_smul, toM_nM hB hD hB0 h2, toM_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem nP_mul_self_eq_zero (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    nP D A C B * nP D A C B = 0 := by
  apply toM_injective hB hD hB0 h2
  rw [toM_mul hB, toM_nP hB hD hB0 h2, toM_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem nM_mul_self (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    nM D A C B * nM D A C B = 0 := by
  apply toM_injective hB hD hB0 h2
  rw [toM_mul hB, toM_nM hB hD hB0 h2, toM_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem normSq_nP_eq_zero (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    (nP D A C B).re ^ 2 - D * (nP D A C B).imI ^ 2 - B * (nP D A C B).imJ ^ 2 +
      D * B * (nP D A C B).imK ^ 2 = 0 := by
  rw [← det_toM hB, toM_nP hB hD hB0 h2, Matrix.det_fin_two_of]
  ring

theorem nM_norm (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    (nM D A C B).re ^ 2 - D * (nM D A C B).imI ^ 2 - B * (nM D A C B).imJ ^ 2 +
      D * B * (nM D A C B).imK ^ 2 = 0 := by
  rw [← det_toM hB, toM_nM hB hD hB0 h2, Matrix.det_fin_two_of]
  ring

theorem matrix_det_one_eq_three_elementary (p q r t : K) (hM : p * t - q * r = 1) (h : r ≠ 0) :
    !![p, q; r, t] = !![1, (p - 1) / r; 0, 1] * !![1, 0; r, 1] * !![1, (t - 1) / r; 0, 1] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
    first | ring1 | linear_combination hM | linear_combination (-1 : K) * hM

theorem mem_of_unipotent (hB : B = A ^ 2 - D * C ^ 2) (hD : D ≠ 0) (hB0 : B ≠ 0) (h2 : (2 : K) ≠ 0)
    (P : Set ℍ[K, D, 0, B]) (hmul : ∀ x ∈ P, ∀ y ∈ P, x * y ∈ P)
    (hP : ∀ c : K, 1 + c • nP D A C B ∈ P) (hM : ∀ c : K, 1 + c • nM D A C B ∈ P)
    {g : ℍ[K, D, 0, B]} (hg : g.re ^ 2 - D * g.imI ^ 2 - B * g.imJ ^ 2 + D * B * g.imK ^ 2 = 1) :
    g ∈ P := by
  have key : ∀ g : ℍ[K, D, 0, B], (toM D A C B g).det = 1 → toM D A C B g 1 0 ≠ 0 → g ∈ P := by
    intro g h1 hr
    have e : g = (1 + ((toM D A C B g 0 0 - 1) / toM D A C B g 1 0) • nP D A C B) *
        (1 + (toM D A C B g 1 0) • nM D A C B) *
        (1 + ((toM D A C B g 1 1 - 1) / toM D A C B g 1 0) • nP D A C B) := by
      apply toM_injective hB hD hB0 h2
      rw [toM_mul hB, toM_mul hB, toM_uP hB hD hB0 h2, toM_uM hB hD hB0 h2, toM_uP hB hD hB0 h2,
        ← matrix_det_one_eq_three_elementary _ (toM D A C B g 0 1) _ _ (by rw [← Matrix.det_fin_two]; exact h1) hr]
      exact Matrix.eta_fin_two _
    rw [e]
    exact hmul _ (hmul _ (hP _) _ (hM _)) _ (hP _)
  have hdet : (toM D A C B g).det = 1 := by rw [det_toM hB, hg]
  by_cases h : toM D A C B g 1 0 = 0
  · have hp : toM D A C B g 0 0 ≠ 0 := by
      intro h0
      rw [Matrix.det_fin_two, h, h0] at hdet
      simp at hdet
    have hu : toM D A C B (1 + (1 : K) • nM D A C B) = !![1, 0; 1, 1] := toM_uM hB hD hB0 h2 1
    have hg' : (1 + (1 : K) • nM D A C B) * g ∈ P := by
      apply key
      · rw [toM_mul hB, Matrix.det_mul, hdet, hu, Matrix.det_fin_two_of]
        ring
      · rw [toM_mul hB, hu]
        simpa [Matrix.mul_apply, Fin.sum_univ_two, h] using hp
    have e : g = (1 + (-1 : K) • nM D A C B) * ((1 + (1 : K) • nM D A C B) * g) := by
      rw [← mul_assoc]
      have : (1 + (-1 : K) • nM D A C B) * (1 + (1 : K) • nM D A C B) = 1 := by
        apply toM_injective hB hD hB0 h2
        rw [toM_mul hB, toM_uM hB hD hB0 h2, hu, toM_one, Matrix.mul_fin_two,
          Matrix.one_fin_two]
        simp
      rw [this, one_mul]
    rw [e]
    exact hmul _ (hM _) _ hg'
  · exact key g hdet h

end Elementary

section Adelic

variable {F : Type} [Field F] {d β : F} {R R' : Type} [CommRing R] [Algebra F R] [CommRing R']
  [Algebra F R']

def un (n : Q d β F) (c : R) : Q d β R := 1 + c • rat n

theorem qmap_un (f : R →ₐ[F] R') (n : Q d β F) (c : R) : qmap f (un n c) = un n (f c) := by
  ext <;> simp [un, rat, qmap]

theorem un_zero (n : Q d β F) : un n (0 : R) = 1 := by simp [un]

theorem qn_un (n : Q d β F) (h0 : n.re = 0) (hn : qn n = 0) (c : R) : qn (un n c) = 1 := by
  have h := congrArg (algebraMap F R) hn
  simp only [qn, h0, map_add, map_sub, map_mul, map_pow, map_zero, Algebra.algebraMap_self,
    RingHom.id_apply] at h
  have h0' : algebraMap F R n.re = 0 := by rw [h0, map_zero]
  simp only [qn, un, rat, qmap]
  simp [h0']
  linear_combination c ^ 2 * h

theorem un_add (n : Q d β F) (hn : n * n = 0) (c c' : R) : un n (c + c') = un n c * un n c' := by
  have h : (rat n : Q d β R) * rat n = 0 := by rw [← map_mul, hn, map_zero]
  simp only [un, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, h, smul_zero, add_smul,
    add_zero]
  abel

theorem continuous_un [TopologicalSpace R] [IsTopologicalRing R] (n : Q d β F) :
    Continuous (fun c : R => (un n c : Q d β R)) := by
  rw [continuous_q_iff]
  simp only [un, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
    QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> fun_prop

theorem rat_nP {K : Type} [Field K] [Algebra F K] (a b : F) :
    (rat (nP (algebraMap F F d) (algebraMap F F a) (algebraMap F F b) (algebraMap F F β)) : Q d β K) =
      nP (algebraMap F K d) (algebraMap F K a) (algebraMap F K b) (algebraMap F K β) := by
  have h2 : algebraMap F K 2 = 2 := map_ofNat _ 2
  ext <;> simp [rat, qmap, nP, h2]

theorem rat_nM {K : Type} [Field K] [Algebra F K] (a b : F) :
    (rat (nM (algebraMap F F d) (algebraMap F F a) (algebraMap F F b) (algebraMap F F β)) : Q d β K) =
      nM (algebraMap F K d) (algebraMap F K a) (algebraMap F K b) (algebraMap F K β) := by
  have h2 : algebraMap F K 2 = 2 := map_ofNat _ 2
  ext <;> simp [rat, qmap, nM, h2]

theorem exists_norm_form (hd : ∀ r : F, r ^ 2 ≠ d) {x : Q d β F} (hx : x ≠ 0) (hq : qn x = 0) :
    ∃ a b : F, β = a ^ 2 - d * b ^ 2 := by
  have hm : ∀ u v : F, u ^ 2 - d * v ^ 2 = 0 → u = 0 ∧ v = 0 := by
    intro u v h
    have hv : v = 0 := by
      by_contra hv
      apply hd (u / v)
      field_simp
      linear_combination h
    subst hv
    refine ⟨?_, rfl⟩
    simpa using h
  simp only [qn, Algebra.algebraMap_self, RingHom.id_apply] at hq
  by_cases m0 : x.imJ ^ 2 - d * x.imK ^ 2 = 0
  · obtain ⟨hj, hk⟩ := hm _ _ m0
    rw [hj, hk] at hq
    obtain ⟨hr, hi⟩ := hm x.re x.imI (by linear_combination hq)
    exact absurd (QuaternionAlgebra.ext hr hi hj hk) hx
  · refine ⟨(x.re * x.imJ - d * x.imI * x.imK) / (x.imJ ^ 2 - d * x.imK ^ 2),
      (x.imI * x.imJ - x.re * x.imK) / (x.imJ ^ 2 - d * x.imK ^ 2), ?_⟩
    rw [div_pow, div_pow, mul_div_assoc', div_sub_div_same, eq_div_iff (pow_ne_zero 2 m0)]
    linear_combination (-(x.imJ ^ 2 - d * x.imK ^ 2)) * hq

end Adelic

section Lift

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem q_ext {x y : Q d β (AF F)} (h : ∀ u : Pl F, qmap (proj u) x = qmap (proj u) y) : x = y := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> refine adele_ext fun u => ?_
  · exact congrArg (fun z : Q d β (Kp u) => z.re) (h u)
  · exact congrArg (fun z : Q d β (Kp u) => z.imI) (h u)
  · exact congrArg (fun z : Q d β (Kp u) => z.imJ) (h u)
  · exact congrArg (fun z : Q d β (Kp u) => z.imK) (h u)

def lift (u : Pl F) (x : Q d β (Kp u)) : Q d β (AF F) :=
  ⟨1 + inc u (x.re - 1), inc u x.imI, inc u x.imJ, inc u x.imK⟩

theorem qmap_lift_same (u : Pl F) (x : Q d β (Kp u)) : qmap (proj u) (lift u x) = x := by
  ext <;> simp [lift, qmap, proj_inc_same]

theorem qmap_lift_ne {u u' : Pl F} (h : u' ≠ u) (x : Q d β (Kp u)) :
    qmap (proj u') (lift u x) = 1 := by
  ext <;> simp [lift, qmap, proj_inc_ne h]

theorem lift_mul (u : Pl F) (x y : Q d β (Kp u)) : lift u (x * y) = lift u x * lift u y := by
  refine q_ext fun u' => ?_
  rw [map_mul]
  by_cases h : u' = u
  · subst h
    simp only [qmap_lift_same]
  · simp only [qmap_lift_ne h, mul_one]

theorem lift_qmap {u : Pl F} {g : Q d β (AF F)} (hg : g ∈ SuppAt d β {u}) :
    lift u (qmap (proj u) g) = g := by
  refine q_ext fun u' => ?_
  by_cases h : u' = u
  · subst h
    exact qmap_lift_same _ _
  · rw [qmap_lift_ne h, hg.2 u' (by simpa using h)]

theorem lift_un (u : Pl F) (n : Q d β F) (c : Kp u) : lift u (un n c) = un n (inc u c) := by
  refine q_ext fun u' => ?_
  rw [qmap_un]
  by_cases h : u' = u
  · subst h
    rw [qmap_lift_same, proj_inc_same]
  · rw [qmap_lift_ne h, proj_inc_ne h, un_zero]

theorem dense_add (s : Pl F) :
    Dense {c : AF F | ∃ (t : F) (y : Kp s), c = algebraMap F (AF F) t + inc s y} := by
  classical
  intro c
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨T, U, hU, -, hO, hy⟩ := Box.adele_box c W hW
  obtain ⟨t, ht, hint⟩ := additive_strong_approx_away s (T.erase s) (by simp) (fun u => interior (U u))
    (fun u _ => ⟨isOpen_interior, ⟨proj u c, mem_interior_iff_mem_nhds.2 (hU u)⟩⟩)
  have hproj : ∀ u, u ≠ s → proj u (algebraMap F (AF F) t + inc s (proj s c - algebraMap F (Kp s) t)) =
      algebraMap F (Kp u) t := fun u hu => by
    rw [map_add, proj_inc_ne hu, add_zero, AlgHom.commutes]
  have hs : proj s (algebraMap F (AF F) t + inc s (proj s c - algebraMap F (Kp s) t)) = proj s c := by
    rw [map_add, proj_inc_same, AlgHom.commutes]
    ring
  refine ⟨algebraMap F (AF F) t + inc s (proj s c - algebraMap F (Kp s) t),
    hy _ (fun u hu => ?_) (fun v hv => ?_), ⟨t, _, rfl⟩⟩
  · by_cases h : u = s
    · subst h
      rw [hs]
      exact mem_of_mem_nhds (hU u)
    · rw [hproj u h]
      exact interior_subset (ht u (Finset.mem_erase.2 ⟨h, hu⟩))
  · by_cases h : (Sum.inr v : Pl F) = s
    · subst h
      rw [hs]
      exact hO v hv (mem_of_mem_nhds (hU _))
    · rw [hproj _ h]
      exact hint v (fun h' => hv (Finset.mem_of_mem_erase h')) h

theorem un_mem_closure (s : Pl F) (n : Q d β F) (h0 : n.re = 0) (hn : qn n = 0) (hnn : n * n = 0)
    (c : AF F) : un n c ∈ closure (SAQ d β s) := by
  refine map_mem_closure (continuous_un n) (dense_add s c) ?_
  rintro _ ⟨t, y, rfl⟩
  refine ⟨un n t, qn_un n h0 hn t, un n (inc s y), ⟨qn_un n h0 hn _, fun u hu => ?_⟩, ?_⟩
  · rw [qmap_un, proj_inc_ne (by simpa using hu), un_zero]
  · rw [un_add n hnn]
    congr 1
    exact (qmap_un (Algebra.ofId F (AF F)) n t).symm

theorem one_mem_SAQ (s : Pl F) : (1 : Q d β (AF F)) ∈ SAQ d β s :=
  ⟨1, qn_one, 1, ⟨qn_one, fun _ _ => map_one _⟩, by rw [map_one, one_mul]⟩

theorem supp_mem {a b : F} (hab : β = a ^ 2 - d * b ^ 2) (hd : d ≠ 0) (hβ : β ≠ 0) (s u : Pl F)
    {g : Q d β (AF F)} (hg : g ∈ SuppAt d β {u}) : g ∈ closure (SAQ d β s) := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have hBF : algebraMap F F β = algebraMap F F a ^ 2 - algebraMap F F d * algebraMap F F b ^ 2 := by
    simpa using hab
  have hdF : algebraMap F F d ≠ 0 := by simpa using hd
  have hβF : algebraMap F F β ≠ 0 := by simpa using hβ
  have hB : algebraMap F (Kp u) β =
      algebraMap F (Kp u) a ^ 2 - algebraMap F (Kp u) d * algebraMap F (Kp u) b ^ 2 := by
    rw [hab, map_sub, map_pow, map_mul, map_pow]
  have hD : algebraMap F (Kp u) d ≠ 0 := fun h => hd ((map_eq_zero _).1 h)
  have hB0 : algebraMap F (Kp u) β ≠ 0 := fun h => hβ ((map_eq_zero _).1 h)
  have h2 : (2 : Kp u) ≠ 0 := fun h => h2F ((map_eq_zero (algebraMap F (Kp u))).1 ((map_ofNat _ 2).trans h))
  have hnP : ∀ c : AF F, un (nP (algebraMap F F d) (algebraMap F F a) (algebraMap F F b)
      (algebraMap F F β) : Q d β F) c ∈ closure (SAQ d β s) :=
    un_mem_closure s _ rfl (normSq_nP_eq_zero hBF hdF hβF h2F) (nP_mul_self_eq_zero hBF hdF hβF h2F)
  have hnM : ∀ c : AF F, un (nM (algebraMap F F d) (algebraMap F F a) (algebraMap F F b)
      (algebraMap F F β) : Q d β F) c ∈ closure (SAQ d β s) :=
    un_mem_closure s _ rfl (nM_norm hBF hdF hβF h2F) (nM_mul_self hBF hdF hβF h2F)
  have key : qmap (proj u) g ∈ {x : Q d β (Kp u) | lift u x ∈ closure (SAQ d β s)} := by
    refine mem_of_unipotent hB hD hB0 h2 _ (fun x hx y hy => ?_) (fun c => ?_) (fun c => ?_) ?_
    · rw [Set.mem_setOf_eq, lift_mul]
      exact closure_SAQ_mul d β s _ hx _ hy
    · rw [Set.mem_setOf_eq, ← rat_nP a b]
      exact (lift_un u _ c).symm ▸ hnP _
    · rw [Set.mem_setOf_eq, ← rat_nM a b]
      exact (lift_un u _ c).symm ▸ hnM _
    · have h := qn_qmap (proj u) g
      rw [hg.1, map_one] at h
      exact h
  rw [Set.mem_setOf_eq, lift_qmap hg] at key
  exact key

end Lift

theorem strong_approx_split : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ r : F, r ^ 2 ≠ d) → β ≠ 0 →
    (∃ x : Q d β F, x ≠ 0 ∧ qn x = 0) → ∀ s : Pl F, QSA d β s := by
  intro F _ _ d β hd hβ ⟨x, hx0, hq⟩ s T
  obtain ⟨a, b, hab⟩ := exists_norm_form hd hx0 hq
  have hd0 : d ≠ 0 := fun h => hd 0 (by simp [h])
  exact ProdSupp.suppAt_subset_of_places d β (closure (SAQ d β s)) (subset_closure (one_mem_SAQ s))
    (closure_SAQ_mul d β s) (fun u g hg => supp_mem hab hd0 hβ s u hg) T

end GlobalTheory.CompanionTheory.PlaneSA.Split
end
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approx_closure_mul : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F), ∀ x ∈ closure (SAQ d β s), ∀ y ∈ closure (SAQ d β s),
  x * y ∈ closure (SAQ d β s) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.closure_SAQ_mul | exact GlobalTheory.CompanionTheory.PlaneSA.closure_SAQ_mul | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.closure_SAQ_mul <;> assumption)
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_product_over_places : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (N : Set (Q d β (AF F))), (1 : Q d β (AF F)) ∈ N →
  (∀ x ∈ N, ∀ y ∈ N, x * y ∈ N) → (∀ u : Pl F, SuppAt d β {u} ⊆ N) →
  ∀ T : Finset (Pl F), SuppAt d β (T : Set (Pl F)) ⊆ N := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places | exact GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places <;> assumption)
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_isotropic_split_all_places : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ r : F, r ^ 2 ≠ d) → β ≠ 0 →
  (∃ x : Q d β F, x ≠ 0 ∧ qn x = 0) → ∀ s : Pl F, QSA d β s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.Split.strong_approx_split
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.RegClosure

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem qmap_re {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).re = f x.re := rfl
theorem qmap_imI {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imI = f x.imI := rfl
theorem qmap_imJ {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imJ = f x.imJ := rfl
theorem qmap_imK {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imK = f x.imK := rfl

theorem nhdsNE_neBot_Kp : ∀ u : Pl F, (𝓝[≠] (0 : Kp u)).NeBot
  | .inl w => by
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
            (map_zero _) 2
          rw [← this, map_ofNat]; norm_num⟩ }
    exact NormedField.nhdsNE_neBot (0 : w.Completion)
  | .inr v => by
    letI := Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
    exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

theorem two_ne_zero_Kp (u : Pl F) : (2 : Kp u) ≠ 0 := by
  have h : algebraMap F (Kp u) 2 ≠ 0 := (map_ne_zero (algebraMap F (Kp u))).2 two_ne_zero
  rwa [map_ofNat] at h

def psi (w : Pl F) (e : Q d β (Kp w)) : Q d β (AF F) :=
  ⟨1 + inc w (e.re - 1), inc w e.imI, inc w e.imJ, inc w e.imK⟩

theorem qmap_proj_psi_same (w : Pl F) (e : Q d β (Kp w)) : qmap (proj w) (psi w e) = e := by
  ext <;> simp [qmap_re, qmap_imI, qmap_imJ, qmap_imK, psi, proj_inc_same]

theorem qmap_proj_psi_ne {u w : Pl F} (h : u ≠ w) (e : Q d β (Kp w)) :
    qmap (proj u) (psi w e) = 1 := by
  ext <;> simp [qmap_re, qmap_imI, qmap_imJ, qmap_imK, psi, proj_inc_ne h]

theorem eq_of_qmap_proj {x y : Q d β (AF F)} (h : ∀ u, qmap (proj u) x = qmap (proj u) y) : x = y := by
  ext
  · exact adele_ext fun u => by simpa [qmap_re] using congrArg QuaternionAlgebra.re (h u)
  · exact adele_ext fun u => by simpa [qmap_imI] using congrArg QuaternionAlgebra.imI (h u)
  · exact adele_ext fun u => by simpa [qmap_imJ] using congrArg QuaternionAlgebra.imJ (h u)
  · exact adele_ext fun u => by simpa [qmap_imK] using congrArg QuaternionAlgebra.imK (h u)

theorem continuous_psi (w : Pl F) : Continuous (psi (d := d) (β := β) w) := by
  refine continuous_q_iff.2 ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_const.add ((continuous_inc w).comp (continuous_re.sub continuous_const))
  · exact (continuous_inc w).comp continuous_imI
  · exact (continuous_inc w).comp continuous_imJ
  · exact (continuous_inc w).comp continuous_imK

theorem psi_mem {w : Pl F} {e : Q d β (Kp w)} (he : qn e = 1) : psi w e ∈ SuppAt d β {w} := by
  refine ⟨adele_ext fun u => ?_, fun u hu => qmap_proj_psi_ne (by simpa using hu) e⟩
  rw [← qn_qmap, map_one]
  by_cases h : u = w
  · subst h
    rw [qmap_proj_psi_same, he]
  · rw [qmap_proj_psi_ne h, qn_one]

theorem psi_proj {w : Pl F} {a : Q d β (AF F)} (ha : a ∈ SuppAt d β {w}) :
    a = psi w (qmap (proj w) a) := by
  refine eq_of_qmap_proj fun u => ?_
  by_cases h : u = w
  · subst h
    rw [qmap_proj_psi_same]
  · rw [qmap_proj_psi_ne h, ha.2 u (by simpa using h)]

theorem reg_closure : ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 → ∀ w : Pl F, ∀ a ∈ SuppAt d β {w},
  a ∈ closure {a' | a' ∈ SuppAt d β {w} ∧ (qmap (proj w) a').re ^ 2 ≠ 1} := by
  intro F _ _ d β hd hb w a ha
  rw [mem_closure_iff_nhds]
  intro U hU
  have hpa := psi_proj ha
  rw [hpa] at hU
  have hU' : psi w ⁻¹' U ∈ 𝓝 (qmap (proj w) a) := (continuous_psi w).continuousAt hU
  have hn : qn (qmap (proj w) a) = 1 := by rw [qn_qmap, ha.1, map_one]
  obtain ⟨b, hbU, hb1, hb2⟩ := RegDense.regular_dense d β (two_ne_zero_Kp w) hd hb
    (nhdsNE_neBot_Kp w) _ hn _ hU'
  exact ⟨psi w b, hbU, psi_mem hb1, by rw [qmap_proj_psi_same]; exact hb2⟩

end GlobalTheory.CompanionTheory.PlaneSA.RegClosure
end
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_closure_regular_trace : ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 → ∀ w : Pl F, ∀ a ∈ SuppAt d β {w},
  a ∈ closure {a' | a' ∈ SuppAt d β {w} ∧ (qmap (proj w) a').re ^ 2 ≠ 1} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.RegClosure.reg_closure
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.MemConj

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem denseRange_algebraMap_Kp (u : Pl F) : DenseRange (algebraMap F (Kp u)) := by
  cases u with
  | inl w =>
    exact (Function.surjective_eval w).denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F)
      (continuous_apply w)
  | inr v => exact HeightOneSpectrum.denseRange_algebraMap (K := F) v

def qinv {K : Type} [Field K] [Algebra F K] (e : Q d β K) : Q d β K :=
  algebraMap K (Q d β K) (qn e)⁻¹ * star e

theorem mul_qinv {K : Type} [Field K] [Algebra F K] {e : Q d β K} (h : qn e ≠ 0) :
    e * qinv e = 1 := by
  have h1 : e * algebraMap K (Q d β K) (qn e)⁻¹ = algebraMap K (Q d β K) (qn e)⁻¹ * e :=
    (Algebra.commutes _ _).symm
  rw [qinv, ← mul_assoc, h1, mul_assoc, mul_star_eq, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem qinv_mul {K : Type} [Field K] [Algebra F K] {e : Q d β K} (h : qn e ≠ 0) :
    qinv e * e = 1 := by
  rw [qinv, mul_assoc, star_mul_eq, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem qinv_unique {K : Type} [Field K] [Algebra F K] {e e' : Q d β K} (h : qn e ≠ 0)
    (h' : e' * e = 1) : qinv e = e' := by
  calc qinv e = (e' * e) * qinv e := by rw [h', one_mul]
    _ = e' := by rw [mul_assoc, mul_qinv h, mul_one]

theorem conj_mem_SuppAt {T : Set (Pl F)} {p q h : Q d β (AF F)} (hpq : p * q = 1)
    (hh : h ∈ SuppAt d β T) : p * h * q ∈ SuppAt d β T := by
  refine ⟨?_, fun u hu => ?_⟩
  · rw [qn_mul, qn_mul, hh.1, mul_one, ← qn_mul, hpq, qn_one]
  · rw [map_mul, map_mul, hh.2 u hu, mul_one, ← map_mul, hpq, map_one]

theorem conj_mem_SAQ (s : Pl F) {δ δ' : Q d β F} (h1 : δ * δ' = 1) (h2 : δ' * δ = 1)
    {x : Q d β (AF F)} (hx : x ∈ SAQ d β s) :
    (rat δ : Q d β (AF F)) * x * rat δ' ∈ SAQ d β s := by
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hx
  have r1 : (rat δ : Q d β (AF F)) * rat δ' = 1 := by rw [← map_mul, h1, map_one]
  have r2 : (rat δ' : Q d β (AF F)) * rat δ = 1 := by rw [← map_mul, h2, map_one]
  refine ⟨δ * γ * δ', ?_, rat δ * h * rat δ', conj_mem_SuppAt r1 hh, ?_⟩
  · rw [qn_mul, qn_mul, hγ, mul_one, ← qn_mul, h1, qn_one]
  · rw [map_mul, map_mul]
    calc (rat δ : Q d β (AF F)) * (rat γ * h) * rat δ'
        = rat δ * rat γ * (rat δ' * rat δ) * h * rat δ' := by
          rw [r2, mul_one]; simp only [mul_assoc]
      _ = rat δ * rat γ * rat δ' * (rat δ * h * rat δ') := by simp only [mul_assoc]

theorem conj_mem_closure (s : Pl F) {δ δ' : Q d β F} (h1 : δ * δ' = 1) (h2 : δ' * δ = 1)
    {x : Q d β (AF F)} (hx : x ∈ closure (SAQ d β s)) :
    (rat δ : Q d β (AF F)) * x * rat δ' ∈ closure (SAQ d β s) := by
  have hc : Continuous fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ' :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hsub : closure (SAQ d β s) ⊆
      (fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ') ⁻¹' closure (SAQ d β s) := by
    refine closure_minimal (fun y hy => subset_closure ?_) (isClosed_closure.preimage hc)
    exact conj_mem_SAQ s h1 h2 hy
  exact hsub hx

def psi (w : Pl F) (y : Q d β (Kp w)) : Q d β (AF F) :=
  ⟨1 + inc w (y.re - 1), inc w y.imI, inc w y.imJ, inc w y.imK⟩

theorem continuous_psi (w : Pl F) : Continuous (psi (d := d) (β := β) w) := by
  rw [continuous_q_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_const.add ((continuous_inc w).comp (continuous_re.sub continuous_const))
  · exact (continuous_inc w).comp continuous_imI
  · exact (continuous_inc w).comp continuous_imJ
  · exact (continuous_inc w).comp continuous_imK

theorem psi_proj {w : Pl F} {x : Q d β (AF F)} (hx : x ∈ SuppAt d β {w}) :
    psi w (qmap (proj w) x) = x := by
  have key : ∀ u, u ≠ w → qmap (proj u) x = 1 := fun u hu => hx.2 u (by simpa using hu)
  ext
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.re) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imI) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imJ) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imK) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm

theorem qmap_proj_rat (w : Pl F) (δ : Q d β F) :
    qmap (proj w) (rat δ : Q d β (AF F)) = rat δ := by
  ext <;> simp [rat, qmap]

theorem continuous_qn {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (qn : Q d β K → K) := by
  have h1 := continuous_re (d := d) (β := β) (R := K)
  have h2 := continuous_imI (d := d) (β := β) (R := K)
  have h3 := continuous_imJ (d := d) (β := β) (R := K)
  have h4 := continuous_imK (d := d) (β := β) (R := K)
  unfold qn
  fun_prop

theorem continuous_star_q {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (star : Q d β K → Q d β K) := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  have h1 := continuous_re (d := d) (β := β) (R := K)
  have h2 := continuous_imI (d := d) (β := β) (R := K)
  have h3 := continuous_imJ (d := d) (β := β) (R := K)
  have h4 := continuous_imK (d := d) (β := β) (R := K)
  exact ⟨h1.add (continuous_const.mul h2), h2.neg, h3.neg, h4.neg⟩

theorem continuous_algebraMap_q {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (algebraMap K (Q d β K)) := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.algebraMap_eq]
  exact ⟨continuous_id, continuous_const, continuous_const, continuous_const⟩

theorem continuousAt_qinv {K : Type} [Field K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] {e : Q d β K} (h : qn e ≠ 0) : ContinuousAt qinv e := by
  have h1 : ContinuousAt (fun x : Q d β K => (qn x)⁻¹) e :=
    continuous_qn.continuousAt.inv₀ h
  have h2 : ContinuousAt (fun x : Q d β K => algebraMap K (Q d β K) (qn x)⁻¹) e :=
    continuous_algebraMap_q.continuousAt.comp h1
  exact h2.mul continuous_star_q.continuousAt

theorem denseRange_rat (w : Pl F) : DenseRange (rat : Q d β F → Q d β (Kp w)) := by
  have D := denseRange_algebraMap_Kp (F := F) w
  have h := D.prodMap (D.prodMap (D.prodMap D))
  have h2 := ((qHomeo (d := d) (β := β) (R := Kp w)).symm.surjective.denseRange).comp h
    (qHomeo (d := d) (β := β) (R := Kp w)).symm.continuous
  refine Dense.mono ?_ h2
  rintro _ ⟨⟨a, b, c, e⟩, rfl⟩
  exact ⟨⟨a, b, c, e⟩, rfl⟩

theorem mem_closure_of_conj_mem : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
    ∀ s w : Pl F, ∀ a ∈ SuppAt d β {w}, ∀ c : (Q d β (AF F))ˣ,
      ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) →
      a ∈ closure (SAQ d β s) := by
  intro F _ _ d β _ s w a ha c hc
  have ha' : ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ SuppAt d β {w} :=
    conj_mem_SuppAt c.inv_mul ha
  obtain ⟨a', ea'⟩ : ∃ a' : Q d β (AF F),
      a' = ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) := ⟨_, rfl⟩
  rw [← ea'] at ha' hc
  obtain ⟨y, ey⟩ : ∃ y : Q d β (Kp w), y = qmap (proj w) a' := ⟨_, rfl⟩
  obtain ⟨cw, ecw⟩ : ∃ cw : Q d β (Kp w), cw = qmap (proj w) (c : Q d β (AF F)) := ⟨_, rfl⟩
  obtain ⟨cw', ecw'⟩ : ∃ cw' : Q d β (Kp w),
      cw' = qmap (proj w) ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) := ⟨_, rfl⟩
  have h1 : cw * cw' = 1 := by rw [ecw, ecw', ← map_mul, c.mul_inv, map_one]
  have h2 : cw' * cw = 1 := by rw [ecw, ecw', ← map_mul, c.inv_mul, map_one]
  have hq : qn cw ≠ 0 := by
    intro h0
    have := congrArg qn h1
    rw [qn_mul, h0, zero_mul, qn_one] at this
    exact zero_ne_one this
  have hinv : qinv cw = cw' := qinv_unique hq h2
  have hy : y = cw' * qmap (proj w) a * cw := by rw [ey, ea', map_mul, map_mul, ecw, ecw']
  have hga : psi w (cw * y * qinv cw) = a := by
    have : cw * y * qinv cw = qmap (proj w) a := by
      rw [hinv, hy]
      calc cw * (cw' * qmap (proj w) a * cw) * cw'
          = (cw * cw') * qmap (proj w) a * (cw * cw') := by simp only [mul_assoc]
        _ = qmap (proj w) a := by rw [h1, one_mul, mul_one]
    rw [this, psi_proj ha]
  have hcont : ContinuousAt (fun e : Q d β (Kp w) => psi w (e * y * qinv e)) cw :=
    (continuous_psi w).continuousAt.comp
      ((continuousAt_id.mul continuousAt_const).mul (continuousAt_qinv hq))
  have hcl : cw ∈ closure (Set.range (rat : Q d β F → Q d β (Kp w))) := denseRange_rat w cw
  haveI : (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hcl
  have htend : Filter.Tendsto (fun e : Q d β (Kp w) => psi w (e * y * qinv e))
      (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw) (𝓝 a) := by
    have := hcont.tendsto
    rw [hga] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hopen : IsOpen {e : Q d β (Kp w) | qn e ≠ 0} :=
    isOpen_ne.preimage continuous_qn
  rw [← closure_closure]
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hopen.mem_nhds hq)] with e he he0
  obtain ⟨δ, rfl⟩ := he
  have hδ : qn δ ≠ 0 := by
    intro h0
    apply he0
    rw [rat, qn_qmap, h0, map_zero]
  have i1 : δ * qinv δ = 1 := mul_qinv hδ
  have i2 : qinv δ * δ = 1 := qinv_mul hδ
  have r1 : (rat δ : Q d β (AF F)) * rat (qinv δ) = 1 := by rw [← map_mul, i1, map_one]
  have hmem := conj_mem_closure s i1 i2 hc
  have hsupp := conj_mem_SuppAt r1 ha'
  have hw : (qinv (rat δ : Q d β (Kp w))) = rat (qinv δ) :=
    qinv_unique he0 (by rw [← map_mul, i2, map_one])
  have : psi w ((rat δ : Q d β (Kp w)) * y * qinv (rat δ : Q d β (Kp w))) =
      (rat δ : Q d β (AF F)) * a' * rat (qinv δ) := by
    rw [hw, ey, ← qmap_proj_rat w δ, ← qmap_proj_rat w (qinv δ), ← map_mul, ← map_mul]
    exact psi_proj hsupp
  rw [this]
  exact hmem

end GlobalTheory.CompanionTheory.PlaneSA.MemConj
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_conjugation_invariant : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, ∀ a ∈ SuppAt d β {w}, ∀ c : (Q d β (AF F))ˣ,
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) →
    a ∈ closure (SAQ d β s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem aniso {F : Type} [Field F] [NumberField F] (d β : F) (hanis : ∀ x : Q d β F, qn x = 0 → x = 0)
    (s : Pl F) (hs : ∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) : QSA d β s := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    have := hanis ⟨0, 1, 0, 0⟩ (by simp [qn])
    simpa using congrArg QuaternionAlgebra.imI this
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have := hanis ⟨0, 0, 1, 0⟩ (by simp [qn])
    simpa using congrArg QuaternionAlgebra.imJ this
  have one_mem : (1 : Q d β (AF F)) ∈ SAQ d β s :=
    ⟨1, qn_one, 1, ⟨qn_one, fun u _ => map_one _⟩, by simp⟩
  intro T g hg
  refine GlobalTheory.T.support_product_over_places d β _ (subset_closure one_mem) (GlobalTheory.T.strong_approx_closure_mul d β s) (fun w a ha => ?_) T hg
  by_cases hw : w = s
  · subst hw
    exact subset_closure ⟨1, qn_one, a, ha, by simp⟩
  · have hreg := GlobalTheory.T.support_closure_regular_trace d β hd0 hβ0 w a ha
    refine closure_minimal (fun a' ha' => ?_) isClosed_closure hreg
    obtain ⟨c, hc⟩ := GlobalTheory.T.quaternion_norm_one_conj_closure d β hanis s w hs hw a' ha'.1 ha'.2
    exact GlobalTheory.T.closure_conjugation_invariant d β hanis s w a' ha'.1 c hc

theorem plane : Sa2.PropPlane := by
  refine GlobalTheory.T.plane_prop_of_all_strong_approx ?_
  intro F E _ _ _ _ _ σ hcm β hβ
  obtain ⟨d, hd, ξ, hξ, hσ⟩ := GlobalTheory.T.cm_extension_imaginary_generator σ hcm
  refine GlobalTheory.T.plane_approx_of_quaternion_approx σ hcm β hβ d hd ξ hξ hσ fun s hs => ?_
  by_cases hanis : ∀ x : Q d β F, qn x = 0 → x = 0
  · exact aniso d β hanis s hs
  · push Not at hanis
    obtain ⟨x, hx, hx0⟩ := hanis
    exact GlobalTheory.T.quaternion_isotropic_split_all_places d β hd hβ ⟨x, hx0, hx⟩ s

end GlobalTheory.CompanionTheory.PlaneSA
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_strong_approx_holds : Sa2.PropPlane := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.plane
end
