import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetDvdEquivariantFramePolynomial
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_dvd_equivariant_framePolynomial : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i)) * evalFr P X) → ∀ b : B, (∀ i, 1 ≤ a b i) → ∃ Q : MvPolynomial (FrVar m) K, P = (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det * Q := by
  first | exact @GlobalTheory.FrameDet.det_dvd_of_equivariant | exact GlobalTheory.FrameDet.det_dvd_of_equivariant | (intros; apply GlobalTheory.FrameDet.det_dvd_of_equivariant <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

noncomputable def blockDetPoly (K : Type) [CommRing K] {B : Type} (m : B → ℕ) (b : B) :
    MvPolynomial (FrVar m) K :=
  (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det

theorem evalFr_map_blockDetPoly {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S) :
    evalFr (MvPolynomial.map φ (blockDetPoly K m b)) X = (X b).det := by
  unfold evalFr blockDetPoly
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i k
  simp

theorem evalFr_blockDetPoly {K : Type} [CommRing K] {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) :
    evalFr (blockDetPoly K m b) X = (X b).det := by
  have := evalFr_map_blockDetPoly (RingHom.id K) m b X
  rwa [MvPolynomial.map_id] at this

theorem exists_eq_prod_blockDetPoly_pow_mul (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B]
    [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (s : ℕ) :
    ∀ (n : B → ℕ), ∑ b, n b = s → ∀ (P : MvPolynomial (FrVar m) K),
      (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K),
        (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
        evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + n b)) * evalFr P X) →
      ∃ G : MvPolynomial (FrVar m) K, P = (∏ b, blockDetPoly K m b ^ n b) * G := by
  induction s with
  | zero =>
    intro n hn P _
    have h0 : ∀ b, n b = 0 := fun b =>
      (Finset.sum_eq_zero_iff.1 hn) b (Finset.mem_univ b)
    exact ⟨P, by simp [h0]⟩
  | succ s ih =>
    intro n hn P hP
    obtain ⟨b₀, -, hb₀⟩ : ∃ b ∈ (Finset.univ : Finset B), n b ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by omega)
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.det_dvd_equivariant_framePolynomial K B m P (fun b i => a b i + n b) hP b₀ (fun i => by omega)
    change P = blockDetPoly K m b₀ * Q at hQ
    set n' : B → ℕ := Function.update n b₀ (n b₀ - 1) with hn'
    have hn'0 : n' b₀ + 1 = n b₀ := by simp only [hn', Function.update_self]; omega
    have hn'1 : ∀ b, b ≠ b₀ → n' b = n b := fun b hb => by
      simp only [hn', Function.update_of_ne hb]
    have hsum : ∑ b, n' b = s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀)] at hn ⊢
      have : ∑ b ∈ Finset.univ.erase b₀, n' b = ∑ b ∈ Finset.univ.erase b₀, n b :=
        Finset.sum_congr rfl fun b hb => hn'1 b (Finset.ne_of_mem_erase hb)
      omega
    have hev : ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
        evalFr P X = (X b₀).det * evalFr Q X := fun X => by
      rw [← evalFr_blockDetPoly m b₀ X, hQ]
      simp only [evalFr, map_mul]
    obtain ⟨G, hG⟩ := ih n' hsum Q (by
      intro X b t hX ht htri
      have h := hP X b t hX ht htri
      rw [hev, hev] at h
      by_cases hb : b = b₀
      · subst hb
        rw [Function.update_self, Matrix.det_mul] at h
        have hd : t.det = ∏ i, t i i := Matrix.det_of_upperTriangular htri
        have hp : (∏ i, t i i ^ (a b i + n b)) = t.det * ∏ i, t i i ^ (a b i + n' b) := by
          rw [hd, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← hn'0]; ring
        rw [hp] at h
        apply mul_left_cancel₀ (mul_ne_zero (hX b) ht)
        rw [h]; ring
      · rw [Function.update_of_ne (Ne.symm hb)] at h
        rw [hn'1 b hb]
        apply mul_left_cancel₀ (hX b₀)
        rw [h]; ring)
    refine ⟨G, ?_⟩
    rw [hQ, hG, ← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀),
      ← Finset.mul_prod_erase _ (fun b => blockDetPoly K m b ^ n b) (Finset.mem_univ b₀)]
    have : ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n' b
        = ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n b :=
      Finset.prod_congr rfl fun b hb => by rw [hn'1 b (Finset.ne_of_mem_erase hb)]
    rw [this, ← hn'0]; ring

theorem evalFr_eq_prod_det_pow_mul : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (N : ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + N)) * evalFr P X) → ∃ G : MvPolynomial (FrVar m) K, ∀ (S : Type) [CommRing S] (φ : K →+* S) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S), evalFr (MvPolynomial.map φ P) X = (∏ b, (X b).det) ^ N * evalFr (MvPolynomial.map φ G) X := by
  intro K _ _ B _ _ m P a N hP
  obtain ⟨G, hG⟩ := exists_eq_prod_blockDetPoly_pow_mul K B m a _ (fun _ => N) rfl P hP
  refine ⟨G, fun S _ φ X => ?_⟩
  rw [hG, ← Finset.prod_pow]
  simp only [← evalFr_map_blockDetPoly φ m _ X]
  simp only [evalFr, map_mul, map_prod, map_pow]

end GlobalTheory.LamT
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem evR_frChg_mul_triangular (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (F : Rul Xo c) (hF : F ∈ sec Xo c a n) (z z' : FrPt Xo c K)
    (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (hT : ∀ b, (T b).BlockTriangular id)
    (hd : ∀ b, (T b).det ≠ 0) (h : FrChg (fun b => (T b).transpose) 1 z z') :
    evR Xo c F z' = (∏ b, ∏ i, T b i i ^ a (b, i)) * evR Xo c F z := by
  have hne : ∀ b i, T b i i ≠ 0 := by
    intro b i
    have h1 := hd b
    rw [Matrix.det_of_isUpperTriangular (hT b)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
  let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)
  have hb : FrBor t z z' := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z z' z').1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩
    exact hT τ hij
  have hw := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 K inferInstance a n F hF
    t z z' hb
  rw [hw]
  congr 1
  simp only [wchar, Fintype.prod_option, Fintype.prod_sigma, t, Formalism.L2.Pj.ex, Units.val_one, one_pow, _root_.one_mul,
    Units.val_mk0]

theorem exists_isFrPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ _ y a n F hF
  obtain ⟨P, N, hP⟩ := GlobalTheory.LamT.RatFn.exists_poly_div_det E H Dw l Xo c K y a n F hF
  have hrefl : FrMap (AlgHom.id c.F K) y y := GlobalTheory.Frames.frMapUniq_refl y
  have hPK : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr P Y := by
    intro z' Y hY h
    have h1 := hP K (AlgHom.id c.F K) y z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P := MvPolynomial.map_id P
    rwa [h2] at h1
  obtain ⟨G, hG⟩ := GlobalTheory.LamT.evalFr_eq_prod_det_pow_mul K (E →+* ℂ) Dw.mult P (fun b i => a (b, i)) N (by
    intro X b t hX ht htri
    let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := Function.update (fun _ => 1) b t
    have hTb : T b = t := Function.update_self ..
    have hTo : ∀ b', b' ≠ b → T b' = 1 := fun b' h => Function.update_of_ne h ..
    have hTtri : ∀ b', (T b').BlockTriangular id := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact htri
      · rw [hTo b' h]; exact Matrix.blockTriangular_one
    have hTd : ∀ b', (T b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact ht
      · rw [hTo b' h]; simp
    have hup : Function.update X b (X b * t) = fun b' => X b' * T b' := by
      funext b'
      by_cases h : b' = b
      · subst h; rw [hTb, Function.update_self]
      · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hPK z₁ X hX h₁
    have e₂ := hPK z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := evR_frChg_mul_triangular E H Dw l Xo c K a n F hF z₁ z₂ T hTtri hTd h₂
    have p₁ : (∏ b', ∏ i, T b' i i ^ a (b', i)) = ∏ i, t i i ^ a (b, i) := by
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i := by
      simp only [Matrix.det_mul, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hup, ← e₂, ← e₁, e₃, p₁, p₂]
    simp only [pow_add, Finset.prod_mul_distrib, mul_pow, Finset.prod_pow]
    ring)
  refine ⟨G, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  have h1 := hP S φ z z' Y hY hz hz'
  rw [hG S φ.toRingHom Y] at h1
  have hu : IsUnit ((∏ b, (Y b).det) ^ N) := (IsUnit.prod_univ_iff.2 hY).pow N
  exact hu.mul_left_cancel h1

end GlobalTheory.LamT
end
