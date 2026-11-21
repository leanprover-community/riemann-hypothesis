import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GermConstantsEqAlongAffineSpaceSquare
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrameStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans

open GlobalTheory.CompanionTheory.SW.QuasiRefl Matrix

theorem carry {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {σ : A →+* A}
    {J : Matrix n n A} (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (y y' : n → A)
    (hy : hform σ J y y = 0) (hy' : hform σ J y' y' = 0) (hu : IsUnit (hform σ J y' y)) :
    ∃ g ∈ UJ σ J, (g : Matrix n n A) *ᵥ y = y' := by
  obtain ⟨ci, hci⟩ := hu.exists_right_inv
  set p := hform σ J y' y with hp
  have hyy' : hform σ J y y' = σ p := by rw [hp, hform_conj_symm hσ hJ]
  have hsc : σ p * σ ci = 1 := by rw [← map_mul, hci, map_one]
  set d : n → A := y - (1 : A) • y' with hd
  have hdy : hform σ J d y = -p := by
    rw [hd, hform_sub_left, hy, map_one, one_mul, ← hp]
    ring
  have hdy' : hform σ J d y' = σ p := by
    rw [hd, hform_sub_left, hyy', hy']
    ring
  have hdd : hform σ J d d = -p - σ p := by
    conv_lhs => rw [hd, hform_sub_right]
    rw [← hd, hdy, hdy']
    ring
  have hc : (-ci) + σ (-ci) = (-ci) * σ (-ci) * hform σ J d d := by
    rw [map_neg, hdd]
    linear_combination (σ ci) * hci + ci * hsc
  refine ⟨((qr hσ hJ d (-ci) hc : UJ σ J) : GL n A), SetLike.coe_mem _, ?_⟩
  show qrMat σ J d (-ci) *ᵥ y = y'
  rw [qrMat_mulVec, hdy]
  funext i
  simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  linear_combination (-(y i - y' i)) * hci

theorem hform_hyp {A : Type} [CommRing A] (σ : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin (M + 2) → A) :
    hform σ (hypOne J) x y = σ (x 0) * y 1 + σ (x 1) * y 0 +
      hform σ J (fun i => x i.succ.succ) (fun i => y i.succ.succ) := by
  simp only [hform, Fin.sum_univ_succ, Fin.succ_zero_eq_one, hypOne_zero_zero, hypOne_zero_one,
    hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero,
    hypOne_rest_one, hypOne_rest_rest]
  simp
  ring

theorem exists_u_local {A : Type} [CommRing A] (σ : A →+* A) {M : ℕ}
    (J Ji : Matrix (Fin M) (Fin M) A) (hJi : J * Ji = 1) (x : Fin (M + 2) → A) (P : Ideal A)
    (hprim : ∃ i, x i ∉ P) :
    ∃ u : Fin M → A, x 1 ∉ P ∨ x 0 + hform σ J u (fun i => x i.succ.succ) ∉ P := by
  by_cases h1 : x 1 ∈ P
  swap
  · exact ⟨0, Or.inl h1⟩
  by_cases h0 : x 0 ∈ P
  swap
  · exact ⟨0, Or.inr (by simpa [hform] using h0)⟩
  obtain ⟨i, hi⟩ := hprim
  obtain ⟨j, rfl⟩ : ∃ j : Fin M, i = j.succ.succ := by
    induction i using Fin.cases with
    | zero => exact absurd h0 hi
    | succ i =>
      induction i using Fin.cases with
      | zero => exact absurd h1 hi
      | succ j => exact ⟨j, rfl⟩
  set w : Fin M → A := fun i => x i.succ.succ with hw
  have hex : ∃ k, (J *ᵥ w) k ∉ P := by
    by_contra hc
    push_neg at hc
    have e : w = Ji *ᵥ (J *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hJi, one_mulVec]
    apply hi
    show w j ∈ P
    rw [e]
    simp only [mulVec, dotProduct]
    exact P.sum_mem fun k _ => P.mul_mem_left _ (hc k)
  obtain ⟨k, hk⟩ := hex
  refine ⟨Pi.single k 1, Or.inr fun hmem => hk ?_⟩
  have e : hform σ J (Pi.single k 1) w = (J *ᵥ w) k := by
    have : σ ∘ (Pi.single k 1 : Fin M → A) = Pi.single k 1 := by
      funext l
      by_cases h : l = k <;> simp [h]
    rw [hform_eq_dot, this]
    simp
  rw [e] at hmem
  exact (Ideal.add_mem_iff_right P h0).1 hmem

theorem hform_comb {A : Type} [CommRing A] (σ : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
    (c c' : A) (u v w : Fin M → A) :
    hform σ J (c • u + c' • v) w = σ c * hform σ J u w + σ c' * hform σ J v w := by
  simp [hform, Finset.mul_sum, add_mul, Finset.sum_add_distrib, mul_assoc]

theorem exists_u {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P₁ P₂ : Ideal A)
    (hmax : ∀ P : Ideal A, P.IsMaximal → P = P₁ ∨ P = P₂) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) A) (w : Fin M → A) (b a : A)
    (hloc : ∀ P : Ideal A, P.IsMaximal → ∃ u : Fin M → A, b ∉ P ∨ a + hform σ J u w ∉ P) :
    ∃ u : Fin M → A, ∀ P : Ideal A, P.IsMaximal → b ∉ P ∨ a + hform σ J u w ∉ P := by
  by_cases hdist : ∃ P Q : Ideal A, P.IsMaximal ∧ Q.IsMaximal ∧ P ≠ Q
  · obtain ⟨P, Q, hP, hQ, hne⟩ := hdist
    have hall : ∀ R : Ideal A, R.IsMaximal → R = P ∨ R = Q := by
      intro R hR
      rcases hmax R hR with h | h <;> rcases hmax P hP with h' | h' <;>
        rcases hmax Q hQ with h'' | h'' <;> simp_all
    have h1 : (1 : A) ∈ P ⊔ Q := by
      rw [Ideal.IsMaximal.coprime_of_ne hP hQ hne]
      trivial
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 h1
    obtain ⟨uP, huP⟩ := hloc P hP
    obtain ⟨uQ, huQ⟩ := hloc Q hQ
    have hval : a + hform σ J (σ q • uP + σ p • uQ) w =
        q * (a + hform σ J uP w) + p * (a + hform σ J uQ w) := by
      rw [hform_comb, hσ, hσ]
      linear_combination (-a) * hpq
    refine ⟨σ q • uP + σ p • uQ, fun R hR => ?_⟩
    have hq1 : q ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 (hpq ▸ P.add_mem hp h))
    have hp1 : p ∉ Q := fun h => hQ.ne_top ((Ideal.eq_top_iff_one _).2 (hpq ▸ Q.add_mem h hq))
    rcases hall R hR with rfl | rfl
    · rcases huP with h | h
      · exact Or.inl h
      · refine Or.inr fun hm => ?_
        rw [hval] at hm
        have h3 := (Ideal.add_mem_iff_left R (R.mul_mem_right _ hp)).1 hm
        rcases hP.isPrime.mem_or_mem h3 with h4 | h4
        · exact hq1 h4
        · exact h h4
    · rcases huQ with h | h
      · exact Or.inl h
      · refine Or.inr fun hm => ?_
        rw [hval] at hm
        have h3 := (Ideal.add_mem_iff_right R (R.mul_mem_right _ hq)).1 hm
        rcases hQ.isPrime.mem_or_mem h3 with h4 | h4
        · exact hp1 h4
        · exact h h4
  · push_neg at hdist
    by_cases hex : ∃ P : Ideal A, P.IsMaximal
    · obtain ⟨P, hP⟩ := hex
      obtain ⟨u, hu⟩ := hloc P hP
      exact ⟨u, fun R hR => by rw [hdist R P hR hP]; exact hu⟩
    · exact ⟨0, fun P hP => absurd ⟨P, hP⟩ hex⟩

theorem exists_mu {A : Type} [CommRing A] (P₁ P₂ : Ideal A)
    (hmax : ∀ P : Ideal A, P.IsMaximal → P = P₁ ∨ P = P₂) (h2 : IsUnit (2 : A)) (a b : A)
    (hab : ∀ P : Ideal A, P.IsMaximal → b ∉ P ∨ a ∉ P) : ∃ μ : ℤ, IsUnit (a - (μ : A) * b) := by
  by_contra hc
  push_neg at hc
  have pair : ∀ P : Ideal A, P.IsMaximal → ∀ m n : ℤ, IsUnit ((n : A) - m) →
      a - (m : A) * b ∈ P → a - (n : A) * b ∈ P → False := by
    intro P hP m n hu h1 h3
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have hb : b ∈ P := by
      have e : b = v * ((a - (m : A) * b) - (a - (n : A) * b)) := by
        linear_combination (-b) * hv
      rw [e]
      exact P.mul_mem_left _ (P.sub_mem h1 h3)
    have ha : a ∈ P := by
      have e : a = (a - (m : A) * b) + (m : A) * b := by ring
      rw [e]
      exact P.add_mem h1 (P.mul_mem_left _ hb)
    rcases hab P hP with h | h
    · exact h hb
    · exact h ha
  obtain ⟨Pa, ha, ha'⟩ := exists_max_ideal_of_mem_nonunits (show a - ((0 : ℤ) : A) * b ∈ nonunits A from hc 0)
  obtain ⟨Pb, hb, hb'⟩ := exists_max_ideal_of_mem_nonunits (show a - ((1 : ℤ) : A) * b ∈ nonunits A from hc 1)
  obtain ⟨Pc, hc₁, hc'⟩ := exists_max_ideal_of_mem_nonunits (show a - ((-1 : ℤ) : A) * b ∈ nonunits A from hc (-1))
  have u01 : IsUnit (((1 : ℤ) : A) - ((0 : ℤ) : A)) := by simp
  have u0m : IsUnit (((-1 : ℤ) : A) - ((0 : ℤ) : A)) := by simp
  have u1m : IsUnit (((1 : ℤ) : A) - ((-1 : ℤ) : A)) := by
    have : ((1 : ℤ) : A) - ((-1 : ℤ) : A) = 2 := by push_cast; ring
    rw [this]
    exact h2
  have hpig : Pa = Pb ∨ Pa = Pc ∨ Pb = Pc := by
    rcases hmax Pa ha with h | h <;> rcases hmax Pb hb with h' | h' <;>
      rcases hmax Pc hc₁ with h'' | h'' <;> simp_all
  rcases hpig with h | h | h
  · subst h
    exact pair Pa ha 0 1 u01 ha' hb'
  · subst h
    exact pair Pa ha 0 (-1) u0m ha' hc'
  · subst h
    exact pair Pb hb (-1) 1 u1m hc' hb'

theorem orbit_ring {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a)
    (h2 : IsUnit (2 : A)) (δ : A) (hδ : IsUnit δ) (hδs : σ δ = -δ) (P₁ P₂ : Ideal A)
    (hmax : ∀ P : Ideal A, P.IsMaximal → P = P₁ ∨ P = P₂) {M : ℕ}
    (J Ji : Matrix (Fin M) (Fin M) A) (hJi : J * Ji = 1) (hJ : ∀ i j, σ (J j i) = J i j)
    (x : Fin (M + 2) → A) (hprim : ∀ P : Ideal A, P.IsMaximal → ∃ i, x i ∉ P)
    (hiso : hform σ (hypOne J) x x = 0) :
    ∃ g ∈ UJ σ (hypOne J), (g : Matrix (Fin (M + 2)) (Fin (M + 2)) A) *ᵥ
      (Fin.cons 1 fun _ => 0 : Fin (M + 2) → A) = x := by
  have hH : ∀ i j, σ (hypOne J j i) = hypOne J i j := by
    intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp [hypOne_zero_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => exact (map_one σ).trans rfl
        | succ j => exact (map_zero σ).trans rfl
    | succ i =>
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (map_one σ).trans rfl
        | succ j =>
          induction j using Fin.cases with
          | zero => exact (map_zero σ).trans rfl
          | succ j => exact (map_zero σ).trans rfl
      | succ i =>
        induction j using Fin.cases with
        | zero => exact (map_zero σ).trans rfl
        | succ j =>
          induction j using Fin.cases with
          | zero => exact (map_zero σ).trans rfl
          | succ j => exact hJ i j
  set w : Fin M → A := fun i => x i.succ.succ with hw
  obtain ⟨u, hu⟩ := exists_u σ hσ P₁ P₂ hmax J w (x 1) (x 0)
    (fun P hP => exists_u_local σ J Ji hJi x P (hprim P hP))
  obtain ⟨i2, hi2⟩ := h2.exists_right_inv
  have hsi2 : σ i2 = i2 := by
    have h : 2 * σ i2 = 1 := by
      have := congrArg σ hi2
      rwa [map_mul, map_one, map_ofNat] at this
    linear_combination i2 * h - σ i2 * hi2
  set q := hform σ J u u with hq
  have hsq : σ q = q := hform_conj_symm hσ hJ u u
  set a := x 0 + hform σ J u w - q * i2 * x 1 with ha
  obtain ⟨di, hdi⟩ := hδ.exists_left_inv
  have hab : ∀ P : Ideal A, P.IsMaximal → δ * x 1 ∉ P ∨ a ∉ P := by
    intro P hP
    by_cases h1 : x 1 ∈ P
    · right
      intro hm
      rcases hu P hP with h | h
      · exact h h1
      · apply h
        have e : x 0 + hform σ J u w = a + q * i2 * x 1 := by rw [ha]; ring
        rw [e]
        exact P.add_mem hm (P.mul_mem_left _ h1)
    · left
      intro hm
      apply h1
      have e : x 1 = di * (δ * x 1) := by linear_combination (-x 1) * hdi
      rw [e]
      exact P.mul_mem_left _ hm
  obtain ⟨μ, hμ⟩ := exists_mu P₁ P₂ hmax h2 a (δ * x 1) hab
  set t : A := -(q * i2) + (μ : A) * δ with ht
  have hst : σ t = -(q * i2) - (μ : A) * δ := by
    rw [ht, map_add, map_neg, map_mul, map_mul, hsq, hsi2, hδs, map_intCast]
    ring
  let z : Fin (M + 2) → A := Fin.cons t (Fin.cons 1 u)
  let e : Fin (M + 2) → A := Fin.cons 1 fun _ => 0
  have z0 : z 0 = t := rfl
  have z1 : z 1 = 1 := rfl
  have zt : (fun i : Fin M => z i.succ.succ) = u := rfl
  have e0' : e 0 = 1 := rfl
  have e1' : e 1 = 0 := rfl
  have et : (fun i : Fin M => e i.succ.succ) = 0 := rfl
  have hzz : hform σ (hypOne J) z z = 0 := by
    rw [hform_hyp, z0, z1, zt, hst, map_one, ← hq, ht]
    linear_combination (-q) * hi2
  have hee : hform σ (hypOne J) e e = 0 := by
    rw [hform_hyp, e0', e1', et]
    simp [hform]
  have hze : hform σ (hypOne J) z e = 1 := by
    rw [hform_hyp, z1, e0', e1', zt, et]
    simp [hform]
  have hzx : hform σ (hypOne J) z x = a - (μ : A) * (δ * x 1) := by
    rw [hform_hyp, z0, z1, zt, hst, map_one, ← hw, ha]
    ring
  have hxz : IsUnit (hform σ (hypOne J) x z) := by
    rw [← hform_conj_symm hσ hH z x, hzx]
    exact hμ.map σ
  obtain ⟨g₁, hg₁, h₁⟩ := carry hσ hH e z hee hzz (by rw [hze]; exact isUnit_one)
  obtain ⟨g₂, hg₂, h₂⟩ := carry hσ hH z x hzz hiso hxz
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  show ((g₂ * g₁ : GL (Fin (M + 2)) A) : Matrix (Fin (M + 2)) (Fin (M + 2)) A) *ᵥ e = x
  rw [Units.val_mul, ← mulVec_mulVec, h₁, h₂]

theorem trans_orbit : ∀ (T : Type) [CommRing T] (O : Subring T) (s : T →+* T), (∀ y ∈ O, s y ∈ O) → (∀ y, s (s y) = y) → IsUnit (2 : O) → (∃ δ : O, IsUnit δ ∧ s δ = -δ) → ∀ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) → ∀ (M : ℕ) (J Ji : Matrix (Fin M) (Fin M) T), (∀ i j, J i j ∈ O) → (∀ i j, Ji i j ∈ O) → J * Ji = 1 → (∀ i j, s (J j i) = J i j) → ∀ x : Fin (M + 2) → O, (∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P) → hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T)) = 0 → ∃ g ∈ UJ s (hypOne J), (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) *ᵥ (e0 T M 0) = (fun i => (x i : T)) ∧ (∀ i j, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O) ∧ ∀ i j, ((g⁻¹ : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O := by
  intro T _ O s hs hss h2 ⟨δ, hδ, hδs⟩ π₁ π₂ hmax M J Ji hJO hJiO hJJ hJ x hprim hiso
  let τ : O →+* O := s.restrict O O hs
  have hτ : ∀ a : O, ((τ a : O) : T) = s a := fun a => rfl
  let JO : Matrix (Fin M) (Fin M) O := fun i j => ⟨J i j, hJO i j⟩
  let JiO : Matrix (Fin M) (Fin M) O := fun i j => ⟨Ji i j, hJiO i j⟩
  have hmapJ : (hypOne JO).map O.subtype = hypOne J := by
    ext i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => rfl
    | succ i =>
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j =>
          induction j using Fin.cases with
          | zero => rfl
          | succ j => rfl
      | succ i =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j =>
          induction j using Fin.cases with
          | zero => rfl
          | succ j => rfl
  have hmul : JO * JiO = 1 := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    show (JO * JiO).map O.subtype = (1 : Matrix (Fin M) (Fin M) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hJJ
  have hiso0 : hform τ (hypOne JO) x x = 0 := by
    have h3 : ((hform τ (hypOne JO) x x : O) : T) =
        hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T)) := by
      rw [← hmapJ]
      simp [hform, hτ]
    exact Subtype.ext (h3.trans hiso)
  obtain ⟨g0, hg0, hgx⟩ := orbit_ring τ (fun a => Subtype.ext (hss a)) h2 δ hδ
    (Subtype.ext hδs) (Ideal.span {π₁}) (Ideal.span {π₂}) hmax JO JiO hmul
    (fun i j => Subtype.ext (hJ i j)) x hprim hiso0
  have hval : ∀ g : GL (Fin (M + 2)) O,
      ((Matrix.GeneralLinearGroup.map O.subtype g : GL (Fin (M + 2)) T) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) T) =
      (g : Matrix (Fin (M + 2)) (Fin (M + 2)) O).map O.subtype := fun g => rfl
  refine ⟨Matrix.GeneralLinearGroup.map O.subtype g0, ?_, ?_, ?_, ?_⟩
  · have h0 : cT τ (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) * hypOne JO *
        (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) = hypOne JO := hg0
    have h1 := congrArg (RingHom.mapMatrix O.subtype) h0
    rw [map_mul, map_mul] at h1
    show cT s ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) T) * hypOne J *
      ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) T) = hypOne J
    have e1 : RingHom.mapMatrix O.subtype (cT τ (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O)) =
        cT s ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) :
          Matrix (Fin (M + 2)) (Fin (M + 2)) T) := by
      ext i j
      rfl
    have e2 : RingHom.mapMatrix O.subtype (hypOne JO) = hypOne J := hmapJ
    have e3 : RingHom.mapMatrix O.subtype (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) =
        ((Matrix.GeneralLinearGroup.map O.subtype g0 : GL (Fin (M + 2)) T) :
          Matrix (Fin (M + 2)) (Fin (M + 2)) T) := rfl
    rwa [e1, e2, e3] at h1
  · funext i
    have h3 := congrArg Subtype.val (congrFun hgx i)
    rw [← h3, hval]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, AddSubmonoidClass.coe_finset_sum,
      Subring.coe_mul, Subring.coe_subtype]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    induction j using Fin.cases with
    | zero => rfl
    | succ j => rfl
  · intro i j
    rw [hval]
    exact ((g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) i j).2
  · intro i j
    rw [← map_inv, hval]
    exact (((g0⁻¹ : GL (Fin (M + 2)) O) : Matrix (Fin (M + 2)) (Fin (M + 2)) O) i j).2

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_vector_extends_hyperbolic : ∀ (T : Type) [CommRing T] (O : Subring T) (s : T →+* T), (∀ y ∈ O, s y ∈ O) → (∀ y, s (s y) = y) → IsUnit (2 : O) → (∃ δ : O, IsUnit δ ∧ s δ = -δ) → ∀ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) → ∀ (M : ℕ) (J Ji : Matrix (Fin M) (Fin M) T), (∀ i j, J i j ∈ O) → (∀ i j, Ji i j ∈ O) → J * Ji = 1 → (∀ i j, s (J j i) = J i j) → ∀ x : Fin (M + 2) → O, (∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P) → hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T)) = 0 → ∃ g ∈ UJ s (hypOne J), (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) *ᵥ (e0 T M 0) = (fun i => (x i : T)) ∧ (∀ i j, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O) ∧ ∀ i j, ((g⁻¹ : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.SW.QuadMaxIdeal

section Quad

variable {R O : Type} [CommRing R] [CommRing O] [IsLocalRing R] (ι : R →+* O) (δ : O) (D : R)

omit [IsLocalRing R] in

theorem isUnit_of_norm (hδ : δ * δ = ι D) (p q : R) (h : IsUnit (p ^ 2 - D * q ^ 2)) :
    IsUnit (ι p + ι q * δ) := by
  obtain ⟨w, hw⟩ := h.exists_right_inv
  refine IsUnit.of_mul_eq_one ((ι p - ι q * δ) * ι w) ?_
  have h1 : ι (p ^ 2 - D * q ^ 2) * ι w = 1 := by rw [← map_mul, hw, map_one]
  simp only [map_sub, map_mul, map_pow] at h1
  linear_combination h1 - (ι q) ^ 2 * ι w * hδ

theorem isUnit_add_mem {u x : R} (hu : IsUnit u) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (u + x) := by
  by_contra h
  have h1 : u + x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have h2 : u ∈ IsLocalRing.maximalIdeal R := by
    simpa using Ideal.sub_mem _ h1 hx
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 hu

theorem isUnit_of_not_mem {x : R} (hx : x ∉ IsLocalRing.maximalIdeal R) : IsUnit x := by
  by_contra h
  exact hx ((IsLocalRing.mem_maximalIdeal _).2 h)

theorem map_mem (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    {P : Ideal O} (hP : P.IsMaximal) {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) :
    ι r ∈ P := by
  by_contra hn
  obtain ⟨y, i, hi, e⟩ := hP.exists_inv hn
  obtain ⟨a, b, rfl⟩ := hsp y
  have hi' : i = ι (1 - a * r) + ι (-(b * r)) * δ := by
    simp only [map_sub, map_mul, map_neg, map_one]
    linear_combination e
  have hu : IsUnit ((1 - a * r) ^ 2 - D * (-(b * r)) ^ 2) := by
    have e1 : (1 - a * r) ^ 2 - D * (-(b * r)) ^ 2 =
        1 + r * (a ^ 2 * r - 2 * a - D * b ^ 2 * r) := by ring
    rw [e1]
    exact isUnit_add_mem isUnit_one (Ideal.mul_mem_right _ _ hr)
  have hiu : IsUnit i := by
    rw [hi']
    exact isUnit_of_norm ι δ D hδ _ _ hu
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hi hiu)

theorem eq_span_of_factor (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (s c : R) (π' : O) (hm : IsLocalRing.maximalIdeal R = Ideal.span {c})
    (hfac : (δ - ι s) * π' = ι c) {P : Ideal O} (hP : P.IsMaximal) (hπ : δ - ι s ∈ P) :
    P = Ideal.span {δ - ι s} := by
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 hπ)
  intro y hy
  obtain ⟨p, q, rfl⟩ := hsp y
  have hr : ι (p + q * s) ∈ P := by
    have e : ι (p + q * s) = (ι p + ι q * δ) - ι q * (δ - ι s) := by
      simp only [map_add, map_mul]; ring
    rw [e]
    exact P.sub_mem hy (P.mul_mem_left _ hπ)
  have hm' : p + q * s ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hr ((isUnit_of_not_mem hn).map ι))
  rw [hm, Ideal.mem_span_singleton'] at hm'
  obtain ⟨a, ha⟩ := hm'
  have h1 : ι a * ι c = ι p + ι q * ι s := by
    rw [← map_mul, ha, map_add, map_mul]
  refine Ideal.mem_span_singleton'.2 ⟨ι q + ι a * π', ?_⟩
  linear_combination (ι a) * hfac + h1

theorem eq_span_of_nonsquare (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hsq : ∀ e : R, e ^ 2 - D ∉ IsLocalRing.maximalIdeal R)
    {P : Ideal O} (hP : P.IsMaximal) : P = Ideal.span {ι ϖ} := by
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 (map_mem ι δ D hδ hsp hP hϖm))
  intro y hy
  obtain ⟨p, q, rfl⟩ := hsp y
  have hN : p ^ 2 - D * q ^ 2 ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hy
      (isUnit_of_norm ι δ D hδ p q (isUnit_of_not_mem hn)))
  have hq : q ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    obtain ⟨w, hw⟩ := (isUnit_of_not_mem hn).exists_right_inv
    apply hsq (p * w)
    have e : (p * w) ^ 2 - D = w ^ 2 * (p ^ 2 - D * q ^ 2) := by
      linear_combination (D * (q * w + 1)) * hw
    rw [e]
    exact Ideal.mul_mem_left _ _ hN
  have hp : p ∈ IsLocalRing.maximalIdeal R := by
    have h1 : p ^ 2 ∈ IsLocalRing.maximalIdeal R := by
      have e : p ^ 2 = (p ^ 2 - D * q ^ 2) + D * q ^ 2 * 1 := by ring
      rw [e]
      refine Ideal.add_mem _ hN (Ideal.mul_mem_right _ _ ?_)
      exact Ideal.mul_mem_left _ _ (by
        rw [pow_two]; exact Ideal.mul_mem_left _ _ hq)
    exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem 2 h1
  rw [hϖ, Ideal.mem_span_singleton'] at hp hq
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  refine Ideal.mem_span_singleton'.2 ⟨ι a + ι b * δ, ?_⟩
  simp only [map_mul]
  ring

theorem exists_root (hD : IsUnit D) (h2 : IsUnit (2 : R)) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) (e : R)
    (he : e ^ 2 - D ∈ IsLocalRing.maximalIdeal R) :
    ∃ e' : R, IsLocalRing.maximalIdeal R = Ideal.span {e' ^ 2 - D} := by
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have heu : IsUnit e := by
    have h1 : IsUnit (D + (e ^ 2 - D)) := isUnit_add_mem hD he
    have h3 : IsUnit (e ^ 2) := by simpa using h1
    exact (isUnit_pow_iff two_ne_zero).1 h3
  have he' := he
  rw [hϖ, Ideal.mem_span_singleton'] at he'
  obtain ⟨c, hc⟩ := he'
  by_cases hcu : IsUnit c
  · refine ⟨e, ?_⟩
    rw [← hc, Ideal.span_singleton_mul_left_unit hcu, hϖ]
  · have hcm : c ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hcu
    have hu : IsUnit (2 * e + (c + ϖ)) :=
      isUnit_add_mem (h2.mul heu) (Ideal.add_mem _ hcm hϖm)
    refine ⟨e + ϖ, ?_⟩
    have e1 : (e + ϖ) ^ 2 - D = (2 * e + (c + ϖ)) * ϖ := by
      linear_combination -hc
    rw [e1, Ideal.span_singleton_mul_left_unit hu, hϖ]

theorem exists_gens (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (hD : IsUnit D) (h2 : IsUnit (2 : R)) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0) :
    ∃ (π₁ π₂ : O) (c : R), c ≠ 0 ∧ π₁ ∣ ι c ∧ π₂ ∣ ι c ∧
      ∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂} := by
  by_cases hsq : ∃ e : R, e ^ 2 - D ∈ IsLocalRing.maximalIdeal R
  · obtain ⟨e0, he0⟩ := hsq
    obtain ⟨e, hm⟩ := exists_root D hD h2 ϖ hϖ e0 he0
    have hc0 : e ^ 2 - D ≠ 0 := by
      intro h0
      have h1 : ϖ ∈ Ideal.span {e ^ 2 - D} := by
        rw [← hm, hϖ]; exact Ideal.mem_span_singleton_self ϖ
      rw [h0] at h1
      exact hϖ0 (by simpa using h1)
    have f1 : (δ - ι e) * (-(δ - ι (-e))) = ι (e ^ 2 - D) := by
      simp only [map_sub, map_neg, map_pow]
      linear_combination -hδ
    have f2 : (δ - ι (-e)) * (-(δ - ι e)) = ι (e ^ 2 - D) := by
      simp only [map_sub, map_neg, map_pow]
      linear_combination -hδ
    refine ⟨δ - ι e, δ - ι (-e), e ^ 2 - D, hc0, ⟨_, f1.symm⟩, ⟨_, f2.symm⟩, ?_⟩
    intro P hP
    have hcm : e ^ 2 - D ∈ IsLocalRing.maximalIdeal R := by
      rw [hm]; exact Ideal.mem_span_singleton_self _
    have hcP := map_mem ι δ D hδ hsp hP hcm
    have hprod : (δ - ι e) * (δ - ι (-e)) ∈ P := by
      have e1 : (δ - ι e) * (δ - ι (-e)) = -((δ - ι e) * (-(δ - ι (-e)))) := by ring
      rw [e1, f1]
      exact P.neg_mem hcP
    rcases hP.isPrime.mem_or_mem hprod with h | h
    · exact Or.inl (eq_span_of_factor ι δ D hδ hsp e _ _ hm f1 hP h)
    · exact Or.inr (eq_span_of_factor ι δ D hδ hsp (-e) _ _ hm f2 hP h)
  · push_neg at hsq
    exact ⟨ι ϖ, ι ϖ, ϖ, hϖ0, dvd_rfl, dvd_rfl, fun P hP =>
      Or.inl (eq_span_of_nonsquare ι δ D hδ hsp ϖ hϖ hsq hP)⟩

end Quad

section Place

open GlobalTheory.CompanionTheory.SW.GoodRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem at_place {d : ℕ} (b : Module.Basis (Fin d) F E)
    (b₂ : Module.Basis (Fin 2) F E) (D : F) (hb0 : b₂ 0 = 1)
    (hD : b₂ 1 * b₂ 1 = algebraMap F E D) (v : HeightOneSpectrum (𝓞 F))
    (hD1 : Valued.v (algebraMap F (Fv F v) D) = 1)
    (h21 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hBC : ∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈
      v.adicCompletionIntegers F)
    (hCB : ∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈
      v.adicCompletionIntegers F)
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    ∃ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) ∧
      IsUnit (π₁ : Fv F v ⊗[F] E) ∧ IsUnit (π₂ : Fv F v ⊗[F] E) := by
  set K := Fv F v with hK
  set B := Algebra.TensorProduct.basis K b₂ with hB
  set C := Algebra.TensorProduct.basis K b with hC
  let Rs : Subring K := (v.adicCompletionIntegers F).toSubring
  have hB0 : B 0 = 1 := by
    rw [hB, Algebra.TensorProduct.basis_apply, hb0]; rfl
  have hB1 : B 1 = inclR K (b₂ 1) := by
    rw [hB, Algebra.TensorProduct.basis_apply]; rfl
  have hBD : B 1 * B 1 = algebraMap K (K ⊗[F] E) (algebraMap F K D) := by
    rw [hB1, ← map_mul, hD]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E D = (algebraMap F (Fv F v) D) ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have hDR : algebraMap F K D ∈ Rs := hD1.le
  obtain ⟨O', hOC, hOB'⟩ := exists_subring Rs B C (algebraMap F K D) hB0 hBD hDR
    (fun k j => by
      have := hBC k j
      rwa [show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this)
    (fun j k => by
      have := hCB j k
      rwa [show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this)
  have hOB : ∀ y, y ∈ O ↔ ∀ j, B.repr y j ∈ Rs := fun y =>
    (hO y).trans ((hOC y).symm.trans (hOB' y))
  have hpq : ∀ p q : K, p ∈ Rs → q ∈ Rs →
      algebraMap K (K ⊗[F] E) p + algebraMap K (K ⊗[F] E) q * B 1 ∈ O := by
    intro p q hp hq
    have h := coord_two B hB0 p q
    refine (hOB _).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [h.1]; exact hp
    · rw [h.2]; exact hq
  have hRmem : ∀ c ∈ Rs, algebraMap K (K ⊗[F] E) c ∈ O := by
    intro c hc
    simpa using hpq c 0 hc Rs.zero_mem
  have hδO : B 1 ∈ O := by
    have := hpq 0 1 Rs.zero_mem Rs.one_mem
    rwa [map_zero, map_one, zero_add, one_mul] at this
  let ι : (v.adicCompletionIntegers F) →+* O :=
    ((algebraMap K (K ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype).codRestrict O
      (fun x => hRmem x x.2)
  let δ : O := ⟨B 1, hδO⟩
  let D' : v.adicCompletionIntegers F := ⟨algebraMap F K D, hDR⟩
  have hδ : δ * δ = ι D' := Subtype.ext hBD
  have hsp : ∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ := fun y => by
    have hy := (hOB y).1 y.2
    exact ⟨⟨_, hy 0⟩, ⟨_, hy 1⟩, Subtype.ext (eq_coord B hB0 y)⟩
  have hunit : ∀ r : v.adicCompletionIntegers F, IsUnit r ↔ Valued.v (r : K) = 1 := fun r =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
  have hv2 : Valued.v (2 : K) = 1 := by simpa [map_ofNat] using h21
  have hDu : IsUnit D' := (hunit D').2 hD1
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := (hunit 2).2 (by
    rw [show ((2 : v.adicCompletionIntegers F) : K) = 2 from
      map_ofNat (v.adicCompletionIntegers F).subtype 2]
    exact hv2)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  obtain ⟨π₁, π₂, c, hc, d1, d2, hmax⟩ := exists_gens ι δ D' hδ hsp hDu h2u ϖ
    hϖ.maximalIdeal_eq hϖ.ne_zero
  have hcK : (c : K) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have hcu : IsUnit (((ι c : O)) : K ⊗[F] E) :=
    (IsUnit.mk0 (c : K) hcK).map (algebraMap K (K ⊗[F] E))
  have key : ∀ π : O, π ∣ ι c → IsUnit (π : K ⊗[F] E) := by
    rintro π ⟨w, hw⟩
    have h1 : (((ι c : O)) : K ⊗[F] E) = (π : K ⊗[F] E) * (w : K ⊗[F] E) :=
      congrArg Subtype.val hw
    rw [h1] at hcu
    exact isUnit_of_mul_isUnit_left hcu
  exact ⟨π₁, π₂, hmax, key π₁ d1, key π₂ d2⟩

end Place

theorem maximal_ideals : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) ∧ IsUnit (π₁ : Fv F v ⊗[F] E) ∧ IsUnit (π₂ : Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ h d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    have hreal : w.IsReal := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x ↦ ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      change star (w.embedding x) = w.embedding x
      rw [← h.2.2.2, hc]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal
  obtain ⟨D, b₂, hsq, hb0, hσ1, hD⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne
  have hD0 : D ≠ 0 := fun h0 => hsq (h0 ▸ IsSquare.zero)
  have I := GlobalTheory.T.integral_almost_all_places F E σ h
  filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero,
    Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k),
    Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 hBC hCB O hO
  exact at_place b b₂ D hb0 hD v hD1 h21 hBC hCB O hO

end GlobalTheory.CompanionTheory.SW.QuadMaxIdeal
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_two_primes_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) ∧ IsUnit (π₁ : Fv F v ⊗[F] E) ∧ IsUnit (π₂ : Fv F v ⊗[F] E) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.QuadMaxIdeal.maximal_ideals
end

section
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit

theorem lam_map_mul {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    [lam.IsAddHaarMeasure] (x : Fv F v) (hx : x ≠ 0) :
    lam.map (fun y => x * y) = (‖x‖₊)⁻¹ • lam := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = ‖x‖ := by
    have := GlobalTheory.GaugeProdFormula.modu_finite F v x hx
    rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at this
    exact this
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = (‖x‖₊)⁻¹ := by
    rw [map_inv]
    apply NNReal.coe_injective
    push_cast
    rw [hc]
  have hm : Measurable fun y : Fv F v => x * y := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  open scoped Pointwise in
  have e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, hc']
  rfl

theorem norm_le_of_val_lt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v)
    (hx : x ≠ 0) (h : Valued.v x < 1) : ‖x‖ ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hv : Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log h0).symm
  set n : ℤ := WithZero.log (Valued.v x) with hn
  have hlt : n < 0 := by
    rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact h
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := GlobalTheory.CompanionTheory.SW.Growth.two_le_norm v
  rw [FinitePlace.norm_def, hv, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n ≤ _
  have h1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)
  calc ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ h1 (by omega)
    _ = _ := by rw [zpow_neg_one, one_div]

theorem fibre_zero_image_mul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (N : ℕ) (hN : 1 ≤ N) (J : Matrix (Fin N) (Fin N) E) (hJ : IsHermND σ J)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    (hlam : IsStdV v lam) (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E))
    (hm : IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m)
    (u : (Fv F v ⊗[F] E)ˣ) (B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E)) (hB : MeasurableSet B) :
    m 0 ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (u : Fv F v ⊗[F] E) * X a i) '' B) =
      ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ (N - 1) : ℝ≥0) : ℝ≥0∞) * m 0 B := by
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  set s : Fv F v := Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) with hs
  have hsu : IsUnit s := u.isUnit.map (Algebra.norm (Fv F v))
  have hs0 : s ≠ 0 := hsu.ne_zero
  have hN' : algebraMap (Fv F v) (Fv F v ⊗[F] E) s = (u : Fv F v ⊗[F] E) * sigR (Fv F v) σ u :=
    GlobalTheory.Doubling.algebraMap_norm_eq hσ _
  set q : ℝ≥0 := ‖s‖₊ with hq
  have hq0 : q ≠ 0 := by rw [hq]; exact nnnorm_ne_zero_iff.2 hs0
  have hsigs : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) s) = algebraMap (Fv F v) (Fv F v ⊗[F] E) s := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => (u : Fv F v ⊗[F] E)
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact u.isUnit
  let T : (Fin 1 → Fin N → Fv F v ⊗[F] E) → Fin 1 → Fin N → Fv F v ⊗[F] E :=
    fun X a i => (u : Fv F v ⊗[F] E) * X a i
  let Ti : (Fin 1 → Fin N → Fv F v ⊗[F] E) → Fin 1 → Fin N → Fv F v ⊗[F] E :=
    fun X a i => ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * X a i
  have hrm : (fun X : Fin 1 → Fin N → Fv F v ⊗[F] E => rmul (Fv F v) X g) = T := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, T]
    rw [Subsingleton.elim p 0, mul_comm]
  have hTc : Continuous T := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hTic : Continuous Ti := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hTT : ∀ X, T (Ti X) = X := by
    intro X; funext a i; simp [T, Ti]
  have hTiT : ∀ X, Ti (T X) = X := by
    intro X; funext a i; simp [T, Ti]
  have hWb : BorelSpace (Fin 1 → Fin N → Fv F v ⊗[F] E) := by infer_instance
  have hTm : Measurable T := hTc.measurable
  have hTim : Measurable Ti := hTic.measurable
  have himg : ∀ C : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), T '' C = Ti ⁻¹' C := by
    intro C
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      simpa [hTiT] using hY
    · intro hX
      exact ⟨Ti X, hX, hTT X⟩
  have himg' : ∀ C : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), T ⁻¹' C = Ti '' C := by
    intro C
    ext X
    constructor
    · intro hX
      exact ⟨T X, hX, hTiT X⟩
    · rintro ⟨Y, hY, rfl⟩
      simpa [hTT] using hY
  have hnorm_inv : ‖Algebra.norm (Fv F v) ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)‖₊ = q⁻¹ := by
    have h1 : Algebra.norm (Fv F v) ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * s = 1 := by
      rw [hs, ← map_mul, Units.inv_mul, map_one]
    have h2 := congrArg (fun x : Fv F v => ‖x‖₊) h1
    simp only [nnnorm_mul, nnnorm_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hmu : (coordW (Fv F v) b lam 1 N).map (fun X => rmul (Fv F v) X g) =
      (q⁻¹ ^ N) • coordW (Fv F v) b lam 1 N := by
    rw [hrm]
    ext C hC
    rw [Measure.map_apply hTm hC, himg', Measure.smul_apply]
    have := GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul F E σ hσ N d b v lam hlam u⁻¹ C hC
    rw [show (Ti '' C) = ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin N) =>
      ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * X p k) '' C) from rfl, this, hnorm_inv, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S =>
    ⟨fun i j => algebraMap (Fv F v) (Fv F v ⊗[F] E) s * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j, by
      intro a c
      have := S.2 a c
      simp only [map_mul, hsigs]
      rw [this]⟩
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) s * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := fun _ _ _ => rfl
  have hτm : Measurable τ := by
    obtain ⟨-, -, -, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Fv F v) 1
    haveI := hBH
    refine Continuous.measurable ?_
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun i j => ?_
    exact continuous_const.mul ((continuous_apply_apply i j).comp continuous_subtype_val)
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g := by
    intro S
    ext i j
    rw [hτe, hN']
    simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g, Matrix.of_apply]
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    ring
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam s hs0 q⁻¹ (lam_map_mul v lam s hs0) τ hτm hτe
  have hfree : IsOpen {X : Fin 1 → Fin N → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m (hW 1 N) (hH 1) hm hfree g hg τ hτ _ _ hmu hc 0
  have hτ0 : τ 0 = 0 := by
    apply Subtype.ext
    funext i j
    change algebraMap (Fv F v) (Fv F v ⊗[F] E) s * 0 = 0
    rw [mul_zero]
  rw [hτ0, hrm] at key
  have hTB : MeasurableSet (T '' B) := by
    rw [himg]; exact hTim hB
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin N → Fv F v ⊗[F] E) => μ' (T '' B)) key
  simp only [Measure.smul_apply, Measure.map_apply hTm hTB] at key2
  have hpre : T ⁻¹' (T '' B) = B := by
    rw [himg, ← Set.preimage_comp]
    have : Ti ∘ T = id := funext hTiT
    rw [this, Set.preimage_id]
  rw [hpre] at key2
  have hcoe : (q : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hq0
  change m 0 (T '' B) = _
  simp only [ENNReal.smul_def, smul_eq_mul] at key2
  have e1 : ((q ^ N : ℝ≥0) : ℝ≥0∞) * ((q⁻¹ ^ N : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_mul, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, ENNReal.coe_one]
  have e2 : ((q ^ N : ℝ≥0) : ℝ≥0∞) * ((q⁻¹ : ℝ≥0) : ℝ≥0∞) = ((q ^ (N - 1) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hq0, mul_one]
  calc m 0 (T '' B) = ((q ^ N : ℝ≥0) : ℝ≥0∞) * (((q⁻¹ ^ N : ℝ≥0) : ℝ≥0∞) * m 0 (T '' B)) := by
        rw [← mul_assoc, e1, one_mul]
    _ = _ := by rw [key2, ← mul_assoc, e2]

theorem val_eq_one_eventually {F : Type} [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) a) = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 F) a
  have h2 := HeightOneSpectrum.Support.finite (𝓞 F) a⁻¹
  refine Filter.eventually_cofinite.2 ((h1.union h2).subset ?_)
  intro v hv
  by_contra hc
  have hc1 : ¬ 1 < v.valuation F a := fun h => hc (Or.inl h)
  have hc2 : ¬ 1 < v.valuation F a⁻¹ := fun h => hc (Or.inr h)
  apply hv
  rw [GlobalTheory.CompanionTheory.SW.Growth.val_alg]
  have hne : v.valuation F a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [not_lt] at hc1 hc2
  rw [map_inv₀] at hc2
  exact le_antisymm hc1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 hc2)

theorem norm_le_of_nonunit (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (d : ℕ) (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E),
      (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) →
      ∀ c : O, ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) →
        ‖Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E)‖ ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hb1 : b.repr 1 ≠ 0 := by
    intro h
    exact one_ne_zero (b.repr.map_eq_zero_iff.1 h)
  obtain ⟨k0, hk0⟩ : ∃ k, b.repr 1 k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hb1 (Finsupp.ext hcon)
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ hσ d b, val_eq_one_eventually _ hk0]
    with v hgood hv O hO c hc hcu
  obtain ⟨O', hO', hσO', -⟩ := hgood
  set s : Fv F v := Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E) with hs
  have hs0 : s ≠ 0 := (hcu.map (Algebra.norm (Fv F v))).ne_zero
  have hN' : algebraMap (Fv F v) (Fv F v ⊗[F] E) s = (c : Fv F v ⊗[F] E) * sigR (Fv F v) σ c :=
    GlobalTheory.Doubling.algebraMap_norm_eq hσ _
  have hσc : sigR (Fv F v) σ c ∈ O :=
    (hO _).2 ((hO' _).1 (hσO' _ ((hO' _).2 ((hO _).1 c.2))))
  have hy : algebraMap (Fv F v) (Fv F v ⊗[F] E) s ∈ O := by
    rw [hN']
    exact O.mul_mem c.2 hσc
  have hrepr : ∀ (r : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d),
      (Algebra.TensorProduct.basis (Fv F v) b).repr (algebraMap (Fv F v) (Fv F v ⊗[F] E) r * y) k =
        r * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
    intro r y k
    rw [← Algebra.smul_def, map_smul]
    rfl
  have hone : (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k0 =
      algebraMap F (Fv F v) (b.repr 1 k0) := by
    rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]
    simp
  have hs1 : Valued.v s ≤ 1 := by
    have h := (hO _).1 hy k0
    rw [← mul_one (algebraMap (Fv F v) (Fv F v ⊗[F] E) s), hrepr, hone,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hv, mul_one] at h
    exact h
  have hlt : Valued.v s < 1 := by
    refine lt_of_le_of_ne hs1 fun h1 => hc ?_
    have hw : algebraMap (Fv F v) (Fv F v ⊗[F] E) s⁻¹ * sigR (Fv F v) σ c ∈ O := by
      refine (hO _).2 fun k => ?_
      have h := (hO _).1 hσc k
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h ⊢
      rw [hrepr, map_mul, map_inv₀, h1, inv_one, one_mul]
      exact h
    have hcw : c * (⟨_, hw⟩ : O) = 1 := by
      apply Subtype.ext
      change (c : Fv F v ⊗[F] E) * (algebraMap (Fv F v) (Fv F v ⊗[F] E) s⁻¹ * sigR (Fv F v) σ c) = 1
      rw [mul_left_comm, ← hN', ← map_mul, inv_mul_cancel₀ hs0, map_one]
    exact IsUnit.of_mul_eq_one _ hcw
  exact norm_le_of_val_lt v s hs0 hlt

theorem fibre_zero_image_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), IsHermND σ J → 3 ≤ N → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (c : O), ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) → ∀ B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), MeasurableSet B → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * X a i) '' B) ≤ ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) B := by
  intro F E _ _ _ _ _ σ hσ N J hJ hN d b
  filter_upwards [norm_le_of_nonunit F E σ hσ d b] with v hv O hO lam hlam m hm h₂ c hc hcu B hB
  have hn := hv O hO c hc hcu
  obtain ⟨u, hu⟩ := hcu
  have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0 := by
    apply Subtype.ext
    funext i j
    simp [hermOf]
  rw [h0]
  have key := fibre_zero_image_mul F E σ hσ N (by omega) J hJ d b v lam hlam m hm u B hB
  rw [hu] at key
  rw [key]
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  set x : ℝ := ‖Algebra.norm (Fv F v) (c : Fv F v ⊗[F] E)‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast GlobalTheory.CompanionTheory.SW.Growth.two_le_norm v
  have hq1 : 1 / (Ideal.absNorm v.asIdeal : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hx1 : x ≤ 1 := hn.trans hq1
  calc x ^ (N - 1) ≤ x ^ 2 := pow_le_pow_of_le_one hx0 hx1 (by omega)
    _ ≤ (1 / (Ideal.absNorm v.asIdeal : ℝ)) ^ 2 := pow_le_pow_left₀ hx0 hn 2
    _ = 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by rw [one_div_pow]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_volume_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), IsHermND σ J → 3 ≤ N → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (c : O), ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) → ∀ B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), MeasurableSet B → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * X a i) '' B) ≤ ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) B := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc

theorem JR_hypOne {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : JR (F := F) R (hypOne J) = hypOne (JR (F := F) R J) := by
  ext i j
  simp only [JR, Matrix.map_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
    simp [hypOne]

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem e0_mem_latV {d : ℕ} (M : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    (e0 (Fv F v ⊗[F] E) M : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) ∈ latV b v := by
  rw [GoodTrans.mem_latV_iff b v O hO]
  intro a i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa [e0] using O.one_mem
  · simpa [e0] using O.zero_mem

theorem primV_subset (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) : primV σ J b v ⊆ latV b v := by
  rintro y ⟨g, hg, rfl⟩
  exact (hg _).2 (e0_mem_latV M b v O hO)

theorem latStab_of_integral (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (g : GL (Fin M) (Fv F v ⊗[F] E)) (hg : g ∈ HR (Fv F v) σ J)
    (hgO : ∀ i j, (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ O)
    (hgiO : ∀ i j, ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j ∈ O) :
    latStab σ J b v ((⟨g, hg⟩ : HR (Fv F v) σ J) : HA (Fv F v) σ J) := by
  let h' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hact : ∀ (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (a : Fin 1),
      actW (Fv F v) σ J h' X a = (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a :=
    fun _ _ => rfl
  intro X
  rw [GoodTrans.mem_latV_iff b v O hO, GoodTrans.mem_latV_iff b v O hO]
  constructor
  · intro hX a i
    have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ
        ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact GoodTrans.mulVec_mem O _ hgiO _ (fun j => by rw [← hact]; exact hX a j) i
  · intro hX a i
    show (actW (Fv F v) σ J h' X a) i ∈ O
    rw [hact]
    exact GoodTrans.mulVec_mem O _ hgO _ (hX a) i

theorem cover_pt (σ : E →ₐ[F] E) {M d : ℕ} (J Ji : Matrix (Fin M) (Fin M) E) (hmul : J * Ji = 1)
    (hJs : ∀ i j, σ (J j i) = J i j)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (hstab : ∀ y ∈ O, sigR (Fv F v) σ y ∈ O)
    (hss : ∀ y, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y)
    (h2 : IsUnit (2 : O)) (hδ : ∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ)
    (π₁ π₂ : O) (hπ : ∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂})
    (hJO : ∀ i j, inclR (Fv F v) (J i j) ∈ O) (hJiO : ∀ i j, inclR (Fv F v) (Ji i j) ∈ O)
    (X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (hX : X ∈ latV b v)
    (hg : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (X 0) (X 0) = 0) :
    X ∈ primV σ J b v ∨ ∃ c : O, (c = π₁ ∨ c = π₂) ∧ ¬ IsUnit c ∧
      X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) ''
        latV b v := by
  classical
  have hXO := (GoodTrans.mem_latV_iff b v O hO X).1 hX
  let x : Fin (M + 2) → O := fun i => ⟨X 0 i, hXO 0 i⟩
  by_cases hp : ∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P
  · left
    have hJR : JR (F := F) (Fv F v) (hypOne J) = hypOne (JR (F := F) (Fv F v) J) := JR_hypOne _ J
    have hmulT : JR (F := F) (Fv F v) J * JR (F := F) (Fv F v) Ji = 1 := by
      have := congrArg (RingHom.mapMatrix (inclR (Fv F v) (F := F) (E := E))) hmul
      rwa [map_mul, map_one] at this
    obtain ⟨g, hgU, hgx, hgO, hgiO⟩ := GlobalTheory.T.primitive_vector_extends_hyperbolic _ O (sigR (Fv F v) σ) hstab hss h2 hδ π₁ π₂ hπ M
      (JR (Fv F v) J) (JR (Fv F v) Ji) hJO hJiO hmulT
      (fun i j => by
        show sigR (Fv F v) σ (inclR (Fv F v) (J j i)) = inclR (Fv F v) (J i j)
        rw [← hJs i j]
        rfl)
      x hp (by rw [← hJR]; exact hg)
    have hgH : g ∈ HR (Fv F v) σ (hypOne J) := by
      show g ∈ UJ (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J))
      rw [hJR]; exact hgU
    refine ⟨(⟨g, hgH⟩ : HR (Fv F v) σ (hypOne J)),
      latStab_of_integral σ (hypOne J) b v O hO g hgH hgO hgiO, ?_⟩
    funext a
    rw [Fin.fin_one_eq_zero a]
    exact hgx
  · right
    push_neg at hp
    obtain ⟨P, hPm, hP⟩ := hp
    have aux : ∀ c : O, P = Ideal.span {c} → ¬ IsUnit c ∧
        X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) ''
          latV b v := by
      intro c hc
      refine ⟨fun hu => hPm.ne_top (by rw [hc]; exact Ideal.span_singleton_eq_top.2 hu), ?_⟩
      have hdiv : ∀ i, ∃ y : O, y * c = x i := fun i => by
        have := hP i
        rw [hc] at this
        exact Ideal.mem_span_singleton'.1 this
      choose y hy using hdiv
      refine ⟨fun _ i => (y i : Fv F v ⊗[F] E), ?_, ?_⟩
      · rw [GoodTrans.mem_latV_iff b v O hO]
        exact fun _ i => (y i).2
      · funext a i
        rw [Fin.fin_one_eq_zero a]
        have := congrArg Subtype.val (hy i)
        simp only [Subring.coe_mul] at this
        show (c : Fv F v ⊗[F] E) * (y i : Fv F v ⊗[F] E) = X 0 i
        rw [mul_comm]
        exact this
    rcases hπ P hPm with h | h
    · exact ⟨π₁, Or.inl rfl, aux _ h⟩
    · exact ⟨π₂, Or.inr rfl, aux _ h⟩

end Place

theorem prim_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, primV σ J b v ⊆ latV b v ∧ ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b lam 1 (M + 2)) (coordHerm (Fv F v) σ b lam 1) m → ∀ h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b, m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) ≤ m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v) + ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) := by
  intro F E _ _ _ _ _ σ h M J hJ hM d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h d b
  have hH := (GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ h M J hJ).1
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ h d b, GlobalTheory.T.local_order_two_primes_almost_all F E σ h d b,
    GlobalTheory.T.local_order_volume_almost_all F E σ h (M + 2) (hypOne J) hH (by omega) d b,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J⁻¹ i j)]
    with v hring h36 h37 hJv hJiv
  obtain ⟨O, hO, hstab, -, h2, hδ, -, -⟩ := hring
  obtain ⟨π₁, π₂, hπ, hu₁, hu₂⟩ := h36 O hO
  refine ⟨primV_subset σ J b v O hO, ?_⟩
  intro lam hlam m hm h₂
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  have hmeas : MeasurableSet (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ h b 1 (M + 2) v
  set H := hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ with hHdef
  have hnull := hm.1 H
  set Z : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
    (gramR (Fv F v) σ (hypOne J) ⁻¹' {(H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E))} ∩
      {X | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ with hZ
  have hnull' : m H Z = 0 := hnull
  let Sc : O → Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) := fun c =>
    {X | ¬ IsUnit c ∧ X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i =>
      (c : Fv F v ⊗[F] E) * Y a i) '' latV b v}
  have hbd : ∀ c : O, IsUnit (c : Fv F v ⊗[F] E) → m H (Sc c) ≤
      ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
    intro c hc
    by_cases hu : IsUnit c
    · have : Sc c = ∅ := Set.eq_empty_of_forall_notMem fun X hX => hX.1 hu
      rw [this, measure_empty]
      simp
    · exact (measure_mono fun X hX => hX.2).trans (h37 O hO lam hlam m hm h₂ c hu hc _ hmeas)
  have hcov : (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) ⊆
      ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) ∪ Z := by
    intro X hX
    by_cases hXZ : X ∈ Z
    · exact Or.inr hXZ
    · left
      have hgr : gramR (Fv F v) σ (hypOne J) X = (H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) := by
        simp only [hZ, Set.mem_compl_iff, not_not] at hXZ
        exact hXZ.1
      have hg : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (X 0) (X 0) = 0 := by
        have := congrFun (congrFun hgr 0) 0
        refine this.trans ?_
        simp [hHdef, hermOf]
      rcases cover_pt σ J J⁻¹ (Matrix.mul_nonsing_inv _ hdet) hJ.1 b v O hO hstab hss h2 hδ π₁ π₂ hπ
        (fun i j => (hO _).2 (hJv i j)) (fun i j => (hO _).2 (hJiv i j)) X hX hg with hp | ⟨c, hc, hn, hi⟩
      · exact Or.inl (Or.inl hp)
      · rcases hc with rfl | rfl
        · exact Or.inl (Or.inr ⟨hn, hi⟩)
        · exact Or.inr ⟨hn, hi⟩
  have hN : ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) =
      ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) +
        ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc m H (latV b v) ≤ m H (((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) ∪ Z) := measure_mono hcov
    _ ≤ m H ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) + m H Z := measure_union_le _ _
    _ = m H ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) := by rw [hnull', add_zero]
    _ ≤ m H (primV σ J b v ∪ Sc π₁) + m H (Sc π₂) := measure_union_le _ _
    _ ≤ m H (primV σ J b v) + m H (Sc π₁) + m H (Sc π₂) := by gcongr; exact measure_union_le _ _
    _ ≤ m H (primV σ J b v) + ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) +
        ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
      gcongr
      · exact hbd _ hu₁
      · exact hbd _ hu₂
    _ = m H (primV σ J b v) + ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
      rw [hN, add_mul, add_assoc]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc
end
end
