import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicWeilVacuumFixedAndTranslatesSpan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitCharacterUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexTranslateCompletedLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal

section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem exists_extension_of_dense {X₀ X M : Type} [AddCommGroup X₀] [AddCommGroup X]
    [AddCommGroup M] [Module ℂ M] (ι : X₀ →+ X) (A : AddSubgroup X) (β : X → X → ℂ)
    (W₀ : X₀ → M →ₗ[ℂ] M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z)
    (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hA : ∀ a ∈ A, ∀ b ∈ A, β a b = 1)
    (hβ : ∀ x, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, β x (m • a) = 1 ∧ β (m • a) x = 1)
    (hW : ∀ x y v, W₀ x (W₀ y v) = β (ι x) (ι y) • W₀ (x + y) v)
    (hd : ∀ (x : X) (m : ℕ), 0 < m → ∃ z, ∃ a ∈ A, ι z = x + m • a)
    (hs : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ z, (∃ a ∈ A, ι z = m • a) → W₀ z v = v) :
    ∃ W : X → M →ₗ[ℂ] M, (∀ z, W (ι z) = W₀ z) ∧
      (∀ x y v, W x (W y v) = β x y • W (x + y) v) ∧
      ∀ x v, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, W (x + m • a) v = W x v := by
  choose b hb0 hb using hβ
  have hb' : ∀ x (n : ℕ), b x ∣ n → ∀ a ∈ A, β x (n • a) = 1 ∧ β (n • a) x = 1 := by
    rintro x n ⟨k, rfl⟩ a ha
    rw [mul_smul]
    exact hb x _ (A.nsmul_mem ha k)
  have hex : ∀ (x : X) (v : M), ∃ G : M, ∃ m : ℕ, 0 < m ∧
      ∀ n : ℕ, m ∣ n → ∀ z, ∀ a ∈ A, ι z = x + n • a → W₀ z v = G := by
    intro x v
    obtain ⟨m, hm0, hm⟩ := hs v
    obtain ⟨z₁, a₁, ha₁, hz₁⟩ := hd x (m * b x) (Nat.mul_pos hm0 (hb0 x))
    refine ⟨W₀ z₁ v, m * b x, Nat.mul_pos hm0 (hb0 x), ?_⟩
    rintro n ⟨k, rfl⟩ z a ha hz
    rw [mul_smul] at hz
    have ha' : k • a ∈ A := A.nsmul_mem ha k
    have hsub : a₁ - k • a ∈ A := A.sub_mem ha₁ ha'
    have hιd : ι (z₁ - z) = (m * b x) • (a₁ - k • a) := by
      rw [map_sub, hz₁, hz, smul_sub]; abel
    have h1 : W₀ (z₁ - z) v = v :=
      hm _ ⟨b x • (a₁ - k • a), A.nsmul_mem hsub _, by rw [hιd, mul_smul]⟩
    have h2 := hW z (z₁ - z) v
    rw [h1, hιd, hz, hl, (hb' x _ (Dvd.intro_left m rfl) _ hsub).1,
      hA _ (A.nsmul_mem ha' _) _ (A.nsmul_mem hsub _), add_sub_cancel] at h2
    simpa using h2
  choose val lev hlev0 hlev using hex
  refine ⟨fun x =>
    { toFun := val x
      map_add' := ?_
      map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro v w
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x w * lev x (v + w))
      (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x w * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x w _ ⟨lev x v * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x (v + w) _ ⟨lev x v * lev x w, by ring⟩ z a ha hz, map_add]
  · intro c v
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x (c • v))
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x (c • v), by ring⟩ z a ha hz,
      ← hlev x (c • v) _ ⟨lev x v, by ring⟩ z a ha hz, map_smul, RingHom.id_apply]
  · intro z
    ext v
    exact (hlev (ι z) v _ dvd_rfl z 0 A.zero_mem (by simp)).symm
  · intro x y v
    change val x (val y v) = β x y • val (x + y) v
    obtain ⟨n, hn0, h1, h2, h3, h4, h5⟩ : ∃ n : ℕ, 0 < n ∧ lev x (val y v) ∣ n ∧ lev y v ∣ n ∧
        lev (x + y) v ∣ n ∧ b x ∣ n ∧ b y ∣ n :=
      ⟨lev x (val y v) * lev y v * lev (x + y) v * b x * b y,
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
          (hb0 _)) (hb0 _),
        ⟨lev y v * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b x, by ring⟩⟩
    obtain ⟨z, a, ha, hz⟩ := hd x n hn0
    obtain ⟨w, c, hc, hw⟩ := hd y n hn0
    have hzw : ι (z + w) = x + y + n • (a + c) := by
      rw [map_add, hz, hw, smul_add]; abel
    have hβzw : β (ι z) (ι w) = β x y := by
      rw [hz, hw, hl, hr, hr, (hb' x n h4 c hc).1, (hb' y n h5 a ha).2,
        hA _ (A.nsmul_mem ha n) _ (A.nsmul_mem hc n)]
      ring
    rw [← hlev x (val y v) n h1 z a ha hz, ← hlev (x + y) v n h3 (z + w) _ (A.add_mem ha hc) hzw,
      ← hlev y v n h2 w c hc hw, hW, hβzw]
  · intro x v
    refine ⟨lev x v, hlev0 _ _, fun a ha => ?_⟩
    change val (x + lev x v • a) v = val x v
    obtain ⟨z, c, hc, hz⟩ := hd (x + lev x v • a) (lev x v * lev (x + lev x v • a) v)
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev _ v _ (Dvd.intro_left _ rfl) z c hc hz]
    refine hlev x v _ dvd_rfl z (a + lev (x + lev x v • a) v • c)
      (A.add_mem ha (A.nsmul_mem hc _)) ?_
    rw [hz, smul_add, mul_smul, add_assoc]

end GlobalTheory.FinWeil
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.GamAlg

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem sgA_sgA (D : D7) (y : AE D) : sgA D (sgA D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sum_eq_trace {R : Type} [CommRing R] (s : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    ∑ i, ∑ j, x i j * s (y i j) = Matrix.trace (x * (y.map s).transpose) := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem trace_inv {R : Type} [CommRing R] (s : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R)
    (p : Matrix (Fin a) (Fin a) R) (q : Matrix (Fin b) (Fin b) R)
    (hp : (p.map s).transpose * p = 1) (hq : (q.map s).transpose * q = 1) :
    Matrix.trace (p * x * q * ((p * y * q).map s).transpose) = Matrix.trace (x * (y.map s).transpose) := by
  have hq' : q * (q.map s).transpose = 1 := mul_eq_one_comm.1 hq
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  have h : p * x * q * ((q.map s).transpose * ((y.map s).transpose * (p.map s).transpose)) =
      p * (x * (q * (q.map s).transpose) * (y.map s).transpose * (p.map s).transpose) := by
    simp only [Matrix.mul_assoc]
  rw [h, hq', Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, hp, Matrix.mul_one]

end GlobalTheory.FinWeil.GamAlg

open GlobalTheory.FinWeil.GamAlg GlobalTheory.NormSum.PtsMem in

theorem GlobalTheory.FinWeil.gamA_alg : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), (∀ u ζ η, gamA ψ (actA D N N' u ζ) (actA D N N' u η) = gamA ψ ζ η) ∧ (∀ ζ : XA D N N', gamA ψ ζ ζ = 1) ∧ (∀ (r : 𝓞 D.host.E) (ζ η : XA D N N'), gamA ψ (r • ζ) η = gamA ψ ζ (sgO D r • η)) ∧ (∀ ζ η ξ : XA D N N', gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ) ∧ (∀ ζ η ξ : XA D N N', gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ) := by
  intro D _ cc δ _ ψ hψ N N'
  obtain ⟨hadd, -, -, hsg, -⟩ := hψ
  refine ⟨?_, fun ζ => ?_, fun r ζ η => ?_, fun ζ η ξ => ?_, fun ζ η ξ => ?_⟩
  · rintro ⟨g, g'⟩ ζ η
    unfold gamA
    rw [sum_eq_trace, sum_eq_trace, actA_apply, actA_apply,
      trace_inv _ _ _ _ _ ((mem_GA D _).1 g'.2) ((mem_GA D _).1 (inv_mem g.2))]
  · unfold gamA
    set t := ∑ i, ∑ j, ζ i j * sgA D (ζ i j) with ht
    have h1 : sgA D t = t := by
      simp only [ht, map_sum, map_mul, sgA_sgA]
      simp only [mul_comm]
    have h2 : t = inc D (1 / 2) * t + sgA D (inc D (1 / 2) * t) := by
      rw [map_mul, sgA_inc, h1, ← add_mul, ← map_add, map_div₀, map_one, map_ofNat, add_halves, map_one, one_mul]
    rw [h2]
    exact hsg _
  · unfold gamA
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_AE, smul_AE, map_mul, sgA_inc, coe_sgO, conj_conj]
    ring
  · unfold gamA
    rw [← hadd]
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  · unfold gamA
    rw [← hadd]
    simp only [Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicHermitianCharacterPairing_properties : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), (∀ u ζ η, gamA ψ (actA D N N' u ζ) (actA D N N' u η) = gamA ψ ζ η) ∧ (∀ ζ : XA D N N', gamA ψ ζ ζ = 1) ∧ (∀ (r : 𝓞 D.host.E) (ζ η : XA D N N'), gamA ψ (r • ζ) η = gamA ψ ζ (sgO D r • η)) ∧ (∀ ζ η ξ : XA D N N', gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ) ∧ (∀ ζ η ξ : XA D N N', gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ) := by
  atlas_forward_decl GlobalTheory.FinWeil.gamA_alg
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.WdCocycle

section General

variable {D : D7} {T : Tor D} {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

theorem hf_conj (x z : VC D N N') : Hf D T z x = (starRingEnd ℂ) (Hf D T x z) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem wd_wd (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = ee (-(w0 D * Hf D T x y).im) • Wd D T (x + y) F := by
  funext z
  have h1 : Hf D T x y = ((Hf D T x y).re : ℂ) + ((Hf D T x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : Hf D T y x = ((Hf D T x y).re : ℂ) - ((Hf D T x y).im : ℂ) * Complex.I := by
    rw [hf_conj x y]
    apply Complex.ext <;> simp
  have h3 : (Hf D T y x).re = (Hf D T x y).re := by
    rw [hf_conj x y, Complex.conj_re]
  have h4 : (w0 D * Hf D T x y).im = ((Hf D T x y).im + Real.sqrt D.host.d * (Hf D T x y).re) / 2 := by
    have : w0 D = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      rw [w0]; push_cast; ring
    rw [this]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have key : ee (qH D T x / 2) * ee (qH D T y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) y - (Real.pi : ℂ) * Hf D T y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      ee (-(w0 D * Hf D T x y).im) * ee (qH D T (x + y) / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z (x + y) - (Real.pi : ℂ) * Hf D T (x + y) (x + y) / 2) := by
    simp only [ee, ← Complex.exp_add, qH]
    congr 1
    rw [h4]
    simp only [hf_add_left, hf_add_right, Complex.add_re, h3]
    rw [h2]
    generalize (Hf D T x y).re = a at h1 ⊢
    generalize (Hf D T x y).im = b at h1 ⊢
    rw [h1]
    push_cast
    ring
  simp only [Wd, U, wdPh, Pi.smul_apply, smul_eq_mul]
  rw [add_assoc z x y]
  linear_combination F (z + (x + y)) * key

end General

variable {D : D7}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem hf_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y) =
      ((‖δ‖ ^ 2 / area (lamOf D cc δ) : ℝ) : ℂ) * ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  have h : δ * starRingEnd ℂ δ = (‖δ‖ : ℂ) ^ 2 := Complex.mul_conj' δ
  simp only [Hf, pt, embV, tor0, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, emb_conj]
  push_cast
  rw [← h, div_mul_eq_mul_div]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Pi.add_apply, Matrix.add_apply, smul_eq_mul, map_add, mul_add]

theorem wd_cocycle : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  intro D hg cc δ _
  obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
  let w : 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a
  have hw : (w : D.host.E) = ((a : D.host.K) : D.host.E) := rfl
  have hτ : ∀ τ, embT D τ (w : D.host.E) = w0 D := fun τ => by
    rw [hw, ← ha]
    exact hg.1 τ _
  refine ⟨w, ?_, fun N N' z y => ⟨?_, pt_add cc δ z y, fun F => ?_⟩⟩
  · apply RingOfIntegers.ext
    apply D.host.φ₀.injective
    change D.host.φ₀ ((w : D.host.E) + D.host.conj (w : D.host.E)) = D.host.φ₀ 1
    rw [map_add, emb_conj, hw, ha, map_one, w0]
    simp only [map_div₀, map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  · rw [hf_pt, psi0, Complex.im_ofReal_mul]
  · rw [wd_wd, pt_add, hf_pt, psi0]
    congr 3
    rw [mul_left_comm, Complex.im_ofReal_mul, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← hτ τ, ← map_mul]
    simp only [Finset.mul_sum, mul_assoc]

end GlobalTheory.FinWeil.WdCocycle
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_point_additive_form : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  first | exact @GlobalTheory.FinWeil.WdCocycle.wd_cocycle | exact GlobalTheory.FinWeil.WdCocycle.wd_cocycle | (intros; apply GlobalTheory.FinWeil.WdCocycle.wd_cocycle <;> assumption)
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.LatSelfDual

theorem ee_neg_eq_one_iff (t : ℝ) : ee (-t) = 1 ↔ ∃ m : ℤ, t = m := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [mul_comm (n : ℂ)] at hn
    have h3 := mul_left_cancel₀ h2 hn
    have h4 : (-t : ℝ) = (n : ℝ) := by exact_mod_cast h3
    push_cast
    linarith
  · rintro ⟨m, rfl⟩
    refine ⟨-m, ?_⟩
    push_cast
    ring

theorem gamA_add_left {D : D7} {ψ : AE D → ℂ} (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y) {N N' : ℕ} (ζ η ξ : XA D N N') :
    gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ := by
  simp only [gamA, ← hψ, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem gamA_add_right {D : D7} {ψ : AE D → ℂ} (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y) {N N' : ℕ} (ζ η ξ : XA D N N') :
    gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ := by
  simp only [gamA, ← hψ, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem gamA_rat {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {ψ : AE D → ℂ} (hψ : ∀ a, ψ (inc D a) = psi0 D cc δ a)
    {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    gamA ψ (z.map (inc D)) (y.map (inc D)) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  rw [← hψ]
  simp only [gamA, Matrix.map_apply, map_sum, map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]

theorem latA_selfDual (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) (ψ : AE D → ℂ)
    (hψ : IsPsi D cc δ ψ) (N N' : ℕ) : SelfDual (gamA ψ) (latA D cc N N') := by
  obtain ⟨hadd, -, hrat, -, m₀, hm₀, h₀⟩ := hψ
  obtain ⟨l1, l2, l3, -, ⟨m₁, hm₁, h₁⟩, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hG cc δ hC N N'
  obtain ⟨w, -, hw⟩ := GlobalTheory.T.theta_point_additive_form D hG cc δ hC
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, hL, h1, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
    exact h1 ▸ (hL 1).2
  obtain ⟨-, -, t1, t2, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩)
  have key : ∀ z y : Matrix (Fin N') (Fin N) D.host.E, gamA ψ (z.map (inc D)) (y.map (inc D)) = 1 ↔
      ∃ m : ℤ, (Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im = m := fun z y => by
    rw [gamA_rat hrat, ← (hw N N' z y).1, ee_neg_eq_one_iff]
  have hM : 0 < m₀ * m₁ * m₁ := by positivity
  have hs : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N',
      (∑ i, ∑ j, ((m₁ : AE D) * ζ i j) * sgA D ((m₁ : AE D) * η i j)) ∈ OhE D := fun ζ hζ η hη =>
    sum_mem fun i _ => sum_mem fun j _ => mul_mem (h₁ _ (hζ i j)) (Formalism.UG.P.csDual_sig_mem _ (h₁ _ (hη i j)))
  have dl : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ((m₀ * m₁ * m₁) • ζ) η = 1 := fun ζ hζ η hη => by
    rw [← h₀ _ (hs ζ hζ η hη), gamA]
    congr 1
    simp only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have dr : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ ((m₀ * m₁ * m₁) • η) = 1 := fun ζ hζ η hη => by
    rw [← h₀ _ (hs ζ hζ η hη), gamA]
    congr 1
    simp only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have iso : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ η = 1 := fun ζ hζ η hη => by
    obtain ⟨z, a, ha, hz⟩ := l3 ζ _ hM
    obtain ⟨y, b, hb, hy⟩ := l3 η _ hM
    have hzm : z.map (inc D) ∈ latA D cc N N' := hz ▸ add_mem hζ (nsmul_mem ha _)
    have hym : y.map (inc D) ∈ latA D cc N N' := hy ▸ add_mem hη (nsmul_mem hb _)
    have h := (key z y).2 (t1 _ ((l1 z).1 hzm) _ ((l1 y).1 hym))
    rwa [hz, gamA_add_left hadd, dl a ha _ hym, mul_one, hy, gamA_add_right hadd, dr ζ hζ b hb, mul_one] at h
  refine fun ζ => ⟨iso ζ, fun h => ?_⟩
  obtain ⟨z, a, ha, hz⟩ := l3 ζ 1 one_pos
  rw [one_smul] at hz
  have hzm : z.map (inc D) ∈ latA D cc N N' := by
    refine (l1 z).2 (t2 _ fun x hx => ?_)
    obtain ⟨y, rfl⟩ := l2 x hx
    have hym := (l1 y).2 hx
    rw [← key, hz, gamA_add_left hadd, h _ hym, iso a ha _ hym, mul_one]
  have : ζ = z.map (inc D) - a := by rw [hz, add_sub_cancel_right]
  rw [this]
  exact sub_mem hzm ha

end GlobalTheory.FinWeil.LatSelfDual
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedStandardAdelicLattice_selfDual : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), SelfDual (gamA ψ) (latA D cc N N') := by
  atlas_forward_decl GlobalTheory.FinWeil.LatSelfDual.latA_selfDual
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.AdelicChar

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_int (k : ℤ) : ee k = 1 := by
  rw [ee, mul_comm]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I k

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem cmTraceAdditiveCharacter_add (a b : D.host.E) : psi0 D cc δ (a + b) = psi0 D cc δ a * psi0 D cc δ b := by
  rw [psi0, psi0, psi0, ← ee_add]
  congr 1
  simp only [map_add, Finset.sum_add_distrib, Complex.add_im]
  ring

theorem cmTraceAdditiveCharacter_zero : psi0 D cc δ 0 = 1 := by simp [psi0, ee]

theorem embT_conj (τ : D.what₂.Tau) (a : D.host.E) :
    embT D τ (D.host.conj a) = (starRingEnd ℂ) (embT D τ a) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have h : D.host.conj a = IsCMField.complexConj D.host.E a := by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj]
    exact D.host.toHostAx.conjE_apply _ a
  rw [h, IsCMField.complexEmbedding_complexConj]

theorem cmTraceAdditiveCharacter_add_conj (a : D.host.E) : psi0 D cc δ (a + D.host.conj a) = 1 := by
  have : (∑ τ, embT D τ (a + D.host.conj a)).im = 0 := by
    simp [Complex.im_sum, embT_conj]
  rw [psi0, this]
  simp [ee]

theorem im_div_area (hcc : cc ≠ ⊥) (hδ : δ ≠ 0) {x y : ℂ} (hx : x ∈ lamOf D cc δ) (hy : y ∈ lamOf D cc δ) :
    ∃ k : ℤ, (x * (starRingEnd ℂ) y).im / area (lamOf D cc δ) = k := by
  obtain ⟨a, τ, ha, -, h⟩ := GlobalTheory.CurveLattice.exists_tau D cc hcc
  have hda : δ * a ≠ 0 := mul_ne_zero hδ ha
  rw [GlobalTheory.CurveLattice.area_of_tau hda (h δ)]
  obtain ⟨m, n, rfl⟩ := (h δ x).1 hx
  obtain ⟨m', n', rfl⟩ := (h δ y).1 hy
  refine ⟨m * n' - n * m', ?_⟩
  have hp : 0 < ‖δ * a‖ ^ 2 * τ.im := by
    have := norm_pos_iff.2 hda
    have := τ.im_pos
    positivity
  rw [div_eq_iff hp.ne']
  generalize δ * a = b
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem cmTraceAdditiveCharacter_trivial_multiple_integers (hg : admG1 D) (hc : Crv D cc δ) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : D.host.E, IsIntegral ℤ r → psi0 D cc δ ((m : D.host.E) * r) = 1 := by
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1
  have hcc := hc.1.1
  set n := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by simpa [hn, Ideal.absNorm_eq_zero_iff] using hcc
  refine ⟨n * n, by positivity, fun r hr => ?_⟩
  let t : 𝓞 D.host.K := ⟨Algebra.trace D.host.K D.host.E r, Algebra.isIntegral_trace hr⟩
  have hnc : (n : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  obtain ⟨k, hk⟩ := im_div_area D cc δ hcc hδ
    ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, cc.mul_mem_right t hnc, rfl⟩)
    ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, hnc, rfl⟩)
  rw [psi0, ← ee_int (-k)]
  congr 1
  have h1 : ∑ τ, embT D τ (((n * n : ℕ) : D.host.E) * r) =
      (n : ℂ) * n * D.host.φ₀ ((t : D.host.K) : D.host.E) := by
    have := hg.2 r
    simp only [map_mul, map_natCast, ← Finset.mul_sum, this, Nat.cast_mul]
    rfl
  have h2 : D.host.φ₀ (((n * t : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      (n : ℂ) * D.host.φ₀ ((t : D.host.K) : D.host.E) := by simp
  have h3 : D.host.φ₀ ((((n : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E) = (n : ℂ) := by simp
  rw [h2, h3] at hk
  rw [h1, Int.cast_neg, ← hk]
  generalize D.host.φ₀ ((t : D.host.K) : D.host.E) = z
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem exists_rat (m : ℕ) (hm : 0 < m) (y : AE D) :
    ∃ e : D.host.E, ∃ s ∈ OhE D, y = inc D e + (m : AE D) * s := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨r, -, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D (n * m) (Nat.mul_pos hn hm) _ hy
  have h1 : inc D ((n : D.host.E)⁻¹) * (n : AE D) = 1 := by
    rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one]
  refine ⟨(n : D.host.E)⁻¹ * r, w, hw, ?_⟩
  rw [map_mul]
  push_cast at e
  linear_combination inc D ((n : D.host.E)⁻¹) * e + ((m : AE D) * w - y) * h1

theorem exists_psi : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ ψ : AE D → ℂ, IsPsi D cc δ ψ := by
  intro D hg cc δ hc
  obtain ⟨m, hm, hint⟩ := cmTraceAdditiveCharacter_trivial_multiple_integers D cc δ hg hc
  choose e s hs he using exists_rat D m hm
  have key : ∀ (y : AE D) (a : D.host.E) (w : AE D), w ∈ OhE D → y = inc D a + (m : AE D) * w →
      psi0 D cc δ (e y) = psi0 D cc δ a := by
    intro y a w hw h
    have hm' : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h1 : inc D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
      rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ hm', map_one]
    have h2 : inc D ((m : D.host.E)⁻¹ * (e y - a)) = w - s y := by
      rw [map_mul, map_sub]
      linear_combination inc D ((m : D.host.E)⁻¹) * (h - he y) + (w - s y) * h1
    have h3 := hint _ ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 (h2 ▸ sub_mem hw (hs y)))
    rw [mul_inv_cancel_left₀ hm'] at h3
    rw [show e y = a + (e y - a) by ring, cmTraceAdditiveCharacter_add, h3, mul_one]
  refine ⟨fun y => psi0 D cc δ (e y), fun x y => ?_, ?_, fun a => ?_, fun y => ?_, m, hm, fun w hw => ?_⟩
  · rw [← cmTraceAdditiveCharacter_add]
    refine key _ _ _ (add_mem (hs x) (hs y)) ?_
    rw [map_add]
    linear_combination he x + he y
  · exact (key 0 0 0 (zero_mem _) (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)
  · exact key _ a 0 (zero_mem _) (by simp)
  · have hw : sgA D (s y) ∈ OhE D := Formalism.UG.P.csDual_sig_mem _ (hs y)
    refine (key _ (e y + D.host.conj (e y)) _ (add_mem (hs y) hw) ?_).trans (cmTraceAdditiveCharacter_add_conj D cc δ _)
    have h := congrArg (sgA D) (he y)
    rw [map_add, map_mul, map_natCast, GlobalTheory.NormSum.PtsMem.sgA_inc] at h
    rw [map_add]
    linear_combination he y + h
  · exact (key _ 0 w hw (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)

end GlobalTheory.FinWeil.AdelicChar
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdeleExtendedCharacter_of_curve : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ ψ : AE D → ℂ, IsPsi D cc δ ψ := by
  atlas_forward_decl GlobalTheory.FinWeil.AdelicChar.exists_psi
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_rationalTranslate_mem_thetaFunctions : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N' := by
  first | exact @GlobalTheory.FinWeil.RatTransl.wd_mem_TT | exact GlobalTheory.FinWeil.RatTransl.wd_mem_TT | (intros; apply GlobalTheory.FinWeil.RatTransl.wd_mem_TT <;> assumption)
end

section
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.Model

theorem conjE_conjE (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem sgA_incE (D : D7) (x : D.host.E) : sgA D (inc D x) = inc D (D.host.conj x) := by
  simp [sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]

theorem wd_at_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

theorem pt_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (m • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
  ring

def incM (D : D7) (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →+ XA D N N' :=
  (inc D).toAddMonoidHom.mapMatrix

theorem incM_apply (D : D7) (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) : incM D N N' z = z.map (inc D) := rfl

theorem exists_div (D : D7) {N N' : ℕ} {m : ℕ} (hm : 0 < m) (z : Matrix (Fin N') (Fin N) D.host.E) (a : XA D N N')
    (h : z.map (inc D) = m • a) : ∃ z' : Matrix (Fin N') (Fin N) D.host.E, z = m • z' ∧ z'.map (inc D) = a := by
  have hm' : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  refine ⟨Matrix.of fun i j => (m : D.host.E)⁻¹ * z i j, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    field_simp
  · ext i j
    have h1 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul] at h1
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, h1]
    rw [← mul_assoc, ← map_natCast (inc D) m, ← map_mul, inv_mul_cancel₀ hm', map_one, one_mul]

theorem mul_nsmul_left {X : Type} [AddCommGroup X] (f : X → ℂ) (h0 : f 0 = 1) (h : ∀ x y, f (x + y) = f x * f y)
    (m : ℕ) (x : X) : f (m • x) = f x ^ m := by
  induction m with
  | zero => simp [h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem exists_isModel (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ) :
    ∃ w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_finiteAdeleExtendedCharacter_of_curve D hD cc δ hc
  obtain ⟨w, hw, hwd⟩ := GlobalTheory.T.theta_point_additive_form D hD cc δ hc
  obtain ⟨hinv, halt, hadj, hl, hr⟩ := GlobalTheory.T.adelicHermitianCharacterPairing_properties D hD cc δ hc ψ hψ N N'
  have hsd := GlobalTheory.T.completedStandardAdelicLattice_selfDual D hD cc δ hc ψ hψ N N'
  obtain ⟨hrat, -, hdense, hden, -, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'
  have htt := GlobalTheory.T.weilOperator_rationalTranslate_mem_thetaFunctions D hD cc δ hc N N'
  let W₀ : Matrix (Fin N') (Fin N) D.host.E → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N' := fun z =>
    { toFun := fun F => ⟨Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F, htt z F F.2⟩
      map_add' := fun F G => Subtype.ext (wd_add _ _ _)
      map_smul' := fun c F => Subtype.ext (wd_smul _ _ _) }
  have hz1 : ∀ y : XA D N N', gamA ψ 0 y = 1 := fun y => by simp [gamA, hψ.2.1]
  have hz2 : ∀ y : XA D N N', gamA ψ y 0 = 1 := fun y => by simp [gamA, hψ.2.1]
  have hn1 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ (m • x) y = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun x => gamA ψ x y) (hz1 y) (fun a b => hl a b y) m x
  have hn2 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ x (m • y) = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun y => gamA ψ x y) (hz2 x) (fun a b => hr x a b) m y
  have hiso : ∀ a ∈ latA D cc N N', ∀ b ∈ latA D cc N N', gamA ψ (w • a) b = 1 := fun a ha b hb =>
    (hsd _).1 ((latA D cc N N').smul_mem w ha) b hb
  obtain ⟨WA, h1, h2, h3⟩ := GlobalTheory.FinWeil.exists_extension_of_dense (incM D N N') (latA D cc N N').toAddSubgroup
    (fun x y => gamA ψ (w • x) y) W₀
    (fun x y z => by simp only [smul_add, hl]) (fun x y z => hr _ _ _) hiso
    (fun x => by
      obtain ⟨m, hm, hx⟩ := hden x
      refine ⟨m, hm, fun a ha => ⟨?_, ?_⟩⟩
      · have := hiso _ hx a ha
        rw [smul_comm, hn1] at this
        simp only [hn2, this]
      · have := hiso a ha _ hx
        rw [hn2] at this
        show gamA ψ (w • m • a) x = 1
        rw [smul_comm, hn1, this])
    (fun x y v => by
      apply Subtype.ext
      have h := (hwd N N' x y).2.2 v
      have h' : gamA ψ (w • incM D N N' x) (incM D N N' y) =
          psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * x i j * D.host.conj (y i j)) := by
        rw [← hψ.2.2.1]
        simp only [gamA, incM_apply, Matrix.smul_apply, Matrix.map_apply, smul_AE, sgA_incE, map_sum, map_mul]
      show Wd D _ _ (Wd D _ _ _) = gamA ψ (w • incM D N N' x) (incM D N N' y) • Wd D _ _ _
      rw [h', h])
    (fun x m hm => hdense x m hm)
    (fun v => by
      obtain ⟨m, hm, hv⟩ := v.2.2
      refine ⟨m, hm, ?_⟩
      rintro z ⟨a, ha, hz⟩
      obtain ⟨z', rfl, rfl⟩ := exists_div D hm z a hz
      apply Subtype.ext
      show Wd D _ (pt D _ δ (m • z')) _ = _
      rw [pt_nsmul]
      exact hv _ ((hrat z').1 ha))
  refine ⟨w, gamA ψ, WA, ⟨fun r => ?_, hw, hl, hr, halt, hadj, fun v => ?_, h2⟩, hsd, hinv, fun z F => ?_, h3⟩
  · apply RingOfIntegers.ext
    rw [coe_sgO, coe_sgO, conjE_conjE]
  · have := h1 0
    rw [map_zero] at this
    rw [this]
    apply Subtype.ext
    show Wd D _ (pt D _ δ 0) _ = _
    rw [pt_zero, wd_at_zero]
  · rw [← incM_apply, h1]
    rfl

end GlobalTheory.FinWeil.Model
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicWeilRepresentationModel : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∃ w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA := by
  atlas_forward_decl GlobalTheory.FinWeil.Model.exists_isModel
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicWeil_vacuum_fixed_and_translates_span : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∃ h : e0 ∈ TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') ⟨e0, h⟩ ∧ Submodule.span ℂ (Set.range fun ζ => WA ζ ⟨e0, h⟩) = ⊤ := by
  first | exact @GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span | exact GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span | (intros; apply GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodIndexNormalization_negative_inert : ∀ D : D7, ∃ lam : ℕ →* ℂ, GoodNorm (sgO D) lam ∧ ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  first | exact @GlobalTheory.FinWeil.exists_goodNorm | exact GlobalTheory.FinWeil.exists_goodNorm | (intros; apply GlobalTheory.FinWeil.exists_goodNorm <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_character_unitary_group : ∀ (D : D7) (N₀ : ℕ) (χ : HeckeU D N₀) (N : ℕ), ∃ c : GA D N →* ℂˣ, (∀ k : GA D N, SuppInert D (k : GL (Fin N) (AE D)) → c k = 1) ∧ ∀ (g : GA D N) (x : (AE D)ˣ), (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) → x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → c g = χ.f x := by
  first | exact @GlobalTheory.SplitCharacter.exists_split_character | exact GlobalTheory.SplitCharacter.exists_split_character | (intros; apply GlobalTheory.SplitCharacter.exists_split_character <;> assumption)
end

section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weil_representation_heisenberg : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → ∀ e : M, e ≠ 0 → Fixes W A e → Submodule.span ℂ (Set.range fun x => W x e) = ⊤ → ∀ {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) → (∀ g, idx A (A.map (ρ g)) ≠ 0) → ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g, SelfDual γ (A.map (ρ g)) ∧ Om g e = normOp lam W A (A.map (ρ g)) e := by
  first | exact @GlobalTheory.FinWeil.exists_weil_rep | exact GlobalTheory.FinWeil.exists_weil_rep | (intros; apply GlobalTheory.FinWeil.exists_weil_rep <;> assumption)
end

section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.IopSum

theorem act_inv_act {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u⁻¹ (actA D N N' u ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem act_act_inv {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u (actA D N N' u⁻¹ ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem mem_map_act {D : D7} {N N' : ℕ} (A : Submodule (𝓞 D.host.E) (XA D N N')) (u : GA D N × GA D N') (ζ : XA D N N') :
    ζ ∈ A.map (actA D N N' u) ↔ actA D N N' u⁻¹ ζ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [act_inv_act]
  · intro h
    exact ⟨_, h, act_act_inv u ζ⟩

theorem mem_moved {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} (g : GA D N) (g' : GA D N') (ζ : XA D N N') :
    ζ ∈ (latA D cc N N').map (actA D N N' (g, g')) ↔
      ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
        ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  rw [mem_map_act, Prod.inv_mk, actA_apply, mem_latA, Subgroup.coe_inv, Subgroup.coe_inv, inv_inv]

theorem pt_sub {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z z' : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z - z') = pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ z' := by
  funext τ i j
  simp [pt, embV, tor0, mul_sub]

theorem sd_of_moves {D : D7} {N : ℕ} (g : GA D N) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  have : L = Lt g := Submodule.ext fun x => (h x).trans ((hLt g).1 x).symm
  rw [this]
  exact (hLt g).2

end GlobalTheory.FinWeil.IopSum

namespace GlobalTheory.FinWeil

open IopSum

theorem iop_eq_sumOp : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → SelfDual γ ((latA D cc N N').map (actA D N N' (g, g'))) → ∀ F : TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') F → Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') F = ((Real.sqrt (idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) : ℝ))⁻¹ : ℂ) • ((sumOp WA (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := by
  intro D hG cc δ hC N N' w γ WA hM g g' L₁ L₁' hL hL' hSD F hF
  obtain ⟨hlat1, -, hlat3, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hG cc δ hC N N'
  have hidx := (GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hG cc δ hC N N' g g').1
  have hidx' := (GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hG cc δ hC N N' g⁻¹ g'⁻¹).1
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hW := (GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨L₁, L₁', sd_of_moves g hL, sd_of_moves g' hL', rfl⟩)).2.1
  simp only [← mem_moved] at hA hB
  set A := latA D cc N N' with hAdef
  set B := A.map (actA D N N' (g, g')) with hBdef
  set La₂ := La D (tor0 D cc δ) L₁ L₁' with hLa₂
  set La₁ := La0 D (tor0 D cc δ) N N' with hLa₁

  have hm : ∀ a ∈ A, idx A (A.map (actA D N N' (g⁻¹, g'⁻¹))) • a ∈ B := by
    intro a ha
    rw [hBdef, mem_map_act, map_nsmul, Prod.inv_mk]
    exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup
      (K := (A.map (actA D N N' (g⁻¹, g'⁻¹))).toAddSubgroup) ⟨a, ha, rfl⟩
  choose z hz hzB using fun q : La₂ ⧸ La₁.addSubgroupOf La₂ => hA _ (Quotient.out q).2
  have hsub : ∀ x y : Matrix (Fin N') (Fin N) D.host.E, x.map (inc D) - y.map (inc D) ∈ A ↔
      pt D (tor0 D cc δ) δ x - pt D (tor0 D cc δ) δ y ∈ La₁ := by
    intro x y
    rw [← Matrix.map_sub _ (map_sub (inc D)), hlat1, pt_sub]
  have huniq : ∀ q q', (z q).map (inc D) - (z q').map (inc D) ∈ A → q = q' := by
    intro q q' h
    rw [hsub, ← hz, ← hz] at h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using h
  have htr : ∀ b ∈ B, ∃! q, b - (z q).map (inc D) ∈ A := by
    intro b hb
    obtain ⟨y, a, ha, hy⟩ := hlat3 b _ (Nat.pos_of_ne_zero hidx')
    have hyB : y.map (inc D) ∈ B := hy ▸ B.add_mem hb (hm a ha)
    have hex : b - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
      have h1 : y.map (inc D) - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
        rw [hsub, ← hz]
        have h2 := QuotientAddGroup.out_eq' (QuotientAddGroup.mk ⟨_, hB y hyB⟩ : La₂ ⧸ La₁.addSubgroupOf La₂)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h2
        simpa [neg_add_eq_sub] using h2
      have h3 := A.sub_mem h1 (nsmul_mem ha (idx A (A.map (actA D N N' (g⁻¹, g'⁻¹)))))
      rw [hy] at h3
      convert h3 using 1
      abel
    refine ⟨QuotientAddGroup.mk ⟨_, hB y hyB⟩, ?_, ?_⟩
    · exact hex
    · intro q hq
      refine huniq _ _ ?_
      have := A.sub_mem hex hq
      rwa [sub_sub_sub_cancel_left] at this
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hidx
  haveI : Finite (La₂ ⧸ La₁.addSubgroupOf La₂) := by
    refine Finite.of_injective (fun q => (QuotientAddGroup.mk ⟨_, hzB q⟩ :
      B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)) fun q q' h => ?_
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    refine (huniq q' q ?_).symm
    simpa [neg_add_eq_sub] using h
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  obtain ⟨h1, h2⟩ := (GlobalTheory.FinWeil.sumOp_transversal hM.1 A B hSD).1 F hF _ (fun q => (z q).map (inc D)) hzB htr
  rw [h1, h2]
  funext v
  rw [Iop, finsum_eq_sum_of_fintype, AddSubgroup.index, Nat.card_eq_fintype_card, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hM.2.2.2.1, ← hz, hW _ (Quotient.out q).2]

end GlobalTheory.FinWeil
end
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntertwiner_eq_normalisedAdelicSum : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → SelfDual γ ((latA D cc N N').map (actA D N N' (g, g'))) → ∀ F : TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') F → Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') F = ((Real.sqrt (idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) : ℝ))⁻¹ : ℂ) • ((sumOp WA (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := by
  first | exact @GlobalTheory.FinWeil.iop_eq_sumOp | exact GlobalTheory.FinWeil.iop_eq_sumOp | (intros; apply GlobalTheory.FinWeil.iop_eq_sumOp <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in

theorem exists_weil_of_vacuum (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ)
    (e0 : VC D N N' → ℂ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (h0 : e0 ≠ 0) (χ : HeckeU D N) (χ' : HeckeU D N') :
    ∃ W : WeilO D cc δ N N' e0, W.chV = χ ∧ W.chV' = χ' ∧ W.ep = 1 ∧ W.ep' = 1 := by
  have hg : admG1 D := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨w, γ, WA, hM⟩ := GlobalTheory.T.exists_adelicWeilRepresentationModel D hg cc δ hc N N'
  obtain ⟨hT, hfix, hspan⟩ := GlobalTheory.T.adelicWeil_vacuum_fixed_and_translates_span D hg cc δ hc N N' w γ WA hM e0 he h0
  obtain ⟨lam, hlam, hsq⟩ := GlobalTheory.T.exists_goodIndexNormalization_negative_inert D
  obtain ⟨c', hc1', hc2'⟩ := GlobalTheory.T.exists_split_character_unitary_group D N χ N'
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_split_character_unitary_group D N' χ' N
  have hidx := GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hg cc δ hc N N'
  have hM' := hM
  obtain ⟨hH, hSD, hinv, hrat, hcont⟩ := hM'
  obtain ⟨Om, hOm1, hOm2⟩ := GlobalTheory.T.exists_weil_representation_heisenberg hH lam hlam _ hSD ⟨e0, hT⟩ (fun h => h0 (congrArg Subtype.val h)) hfix hspan
    (actA D N N') hinv (fun u => (hidx u.1 u.2).1)
  let O : GA D N → GA D N' → (VC D N N' → ℂ) → (VC D N N' → ℂ) := fun g g' F =>
    if h : F ∈ TTs D (tor0 D cc δ) N N' then
      ((((c' g' * c g : ℂˣ) : ℂ) • Om (g, g') ⟨F, h⟩ : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) else 0
  have hO : ∀ g g' (F : TTs D (tor0 D cc δ) N N'), O g g' F =
      ((((c' g' * c g : ℂˣ) : ℂ) • Om (g, g') F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := fun g g' F => dif_pos F.2
  refine ⟨{ nz := h0, chV := χ, chV' := χ', ep := 1, ep' := 1, ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩, Om := O,
            maps := ?_, add := ?_, smul := ?_, one := ?_, mul := ?_, lift := ?_, inert := ?_, split := ?_ }, rfl, rfl, rfl, rfl⟩
  · intro g g' F hF
    rw [hO g g' ⟨F, hF⟩]
    exact Subtype.property _
  · intro g g' F hF F' hF'
    have := hO g g' (⟨F, hF⟩ + ⟨F', hF'⟩)
    rw [map_add, smul_add, Submodule.coe_add, Submodule.coe_add, ← hO, ← hO] at this
    exact this
  · intro g g' a F hF
    have := hO g g' (a • ⟨F, hF⟩)
    rw [map_smul, smul_comm, Submodule.coe_smul, Submodule.coe_smul a, ← hO] at this
    exact this
  · intro F hF
    rw [hO 1 1 ⟨F, hF⟩, map_one, map_one, mul_one, Units.val_one, one_smul, Prod.mk_one_one, map_one]
    rfl
  · intro g₁ g₂ g₁' g₂' F hF
    rw [hO _ _ ⟨F, hF⟩, hO g₂ g₂' ⟨F, hF⟩, hO, map_smul, smul_smul, ← Prod.mk_mul_mk, map_mul Om, map_mul, map_mul,
      ← Units.val_mul, mul_mul_mul_comm]
    rfl
  · intro g g' z F hF
    obtain ⟨m, hm, h⟩ := hcont (actA D N N' (g, g') (z.map (inc D))) (Om (g, g') ⟨F, hF⟩)
    refine ⟨m, hm, fun z' hz' => ?_⟩
    choose a ha1 ha2 using hz'
    have h1 : z'.map (inc D) = actA D N N' (g, g') (z.map (inc D)) + m • (Matrix.of a : XA D N N') := by
      rw [← sub_eq_iff_eq_add']
      ext i j
      rw [actA_apply, ha2 i j, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    have h2 := hrat z ⟨F, hF⟩
    rw [← h2, hO, hO g g' ⟨F, hF⟩, ← hrat, map_smul, hOm1, h1, h (Matrix.of a) ha1]
  · intro k k' hk hk' hs hs'
    have h3 := (GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ (hOm2 (k, k')).1).2.2 ((hidx k k').2.2 hk hk')
    rw [hO k k' ⟨e0, hT⟩, hc1 k hs, hc1' k' hs', mul_one, Units.val_one, one_smul, (hOm2 (k, k')).2, normOp, h3.1,
      h3.2 _ hfix, map_one, inv_one, one_smul]
  · intro g g' x x' L₁ L₁' hs hs' hx h1 h1' hL hL'
    have h3 := GlobalTheory.T.thetaIntertwiner_eq_normalisedAdelicSum D hg cc δ hc N N' w γ WA hM g g' L₁ L₁' hL hL' (hOm2 (g, g')).1 ⟨e0, hT⟩ hfix
    have h4 := hsq _ (hidx g g').1 fun q hq hi => (hidx g g').2.1 q hq (hs q hq hi) (hs' q hq hi)
    rw [hO g g' ⟨e0, hT⟩, hc2 g x (fun q hq hi => (hx q hq hi).1) h1, hc2' g' x' (fun q hq hi => (hx q hq hi).2) h1',
      (hOm2 (g, g')).2, normOp, h4, Submodule.coe_smul, Submodule.coe_smul, ← h3, zpow_one, zpow_one]
    rfl

theorem exists_weil : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even N → Even N' → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ (χ : HeckeU D N) (χ' : HeckeU D N'), ∃ W : WeilO D cc δ N N' e0, W.chV = χ ∧ W.chV' = χ' ∧ W.ep = 1 ∧ W.ep' = 1 :=
  fun D cc δ hc N N' _ _ e0 he h0 χ χ' => exists_weil_of_vacuum D cc δ hc N N' e0 he h0 χ χ'

end GlobalTheory.FinWeil
end
