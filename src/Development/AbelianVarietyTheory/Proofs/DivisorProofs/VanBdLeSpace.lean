import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedRuleOfFlagComponentSection
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedRule_of_flagComponentSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (e : Ix Dw → ℤ) (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)), ∃ f : GlobalTheory.AllWt.secZ Xo c e, (f : Rul Xo c) ∈ GlobalTheory.AllWt.suppOn Z ∧ sec₀ X Z e f = m := by
  first | exact @GlobalTheory.CompHS.exists_suppOn_sec₀_eq | exact GlobalTheory.CompHS.exists_suppOn_sec₀_eq | (intros; apply GlobalTheory.CompHS.exists_suppOn_sec₀_eq <;> assumption)
end

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FrameEval

namespace GlobalTheory.NonDomVanish

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frBor_univ {p A : TRing c.F} {j : Sp p.R ⟶ Xo.XF c} {y₀ : FrPt Xo c p.R} {π : p.R →ₐ[c.F] A.R}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R} {s : (A.R)ˣ} {u : FrPt Xo c A.R}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S]
    {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    {a a' : A.R →ₐ[c.F] S} (ha : FrMap a u y) (ha' : FrMap a' u y') (h : FrBor t y y') :
    evR Xo c f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evR Xo c f y := by
  obtain ⟨B, uB, uB', tB, q, q', hq, hq', hB, hU⟩ :=
    univFrame_borelPairs GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c p A j y₀ π X s u hj hu
  obtain ⟨b, e1, e2, e3⟩ := hU S a a' y y' t ha ha' h
  have k : FrMap b uB y := GlobalTheory.FlagTan.frMap_of_comp hq ha fun x => DFunLike.congr_fun e1 x
  have k' : FrMap b uB' y' := GlobalTheory.FlagTan.frMap_of_comp hq' ha' fun x => DFunLike.congr_fun e2 x
  have ht : t = fun i => Units.map (b : B.R →* S) (tB i) := funext fun i => Units.ext (e3 i).symm
  rw [GlobalTheory.FlagTan.evR_eq hf.1 k, GlobalTheory.FlagTan.evR_eq hf.1 k', hf.2 B tB uB uB' hB, map_mul, ht]
  congr 1
  simp only [← map_zpow, ← map_prod]
  rfl

section Mat

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S]

def trv (a b : n) (x : S) : Matrix n n S := 1 + single a b x

def lowerTriangularTwoBlockMatrix (a b : n) (s y : S) : Matrix n n S := 1 + single a a (s - 1) + single b a 1 + single b b (y - 1)

def weylTwoBlockMatrix (a b : n) (y : S) : Matrix n n S := 1 + single a a (y - 1) + single a b 1 - single b a 1 - single b b 1

def weylTwoBlockMatrixInv (a b : n) (y : S) : Matrix n n S := 1 - single a a 1 - single a b 1 + single b a 1 + single b b (y - 1)

theorem lowerTriangularTwoBlock_mul_weylTwoBlock_eq_transvection (a b : n) (hab : a ≠ b) (s y : S) (hsy : s * y = 1) :
    lowerTriangularTwoBlockMatrix a b s y * weylTwoBlockMatrix a b y = trv a b s := by
  have h1 : ∀ (c d : S) (i l : n), single i a c * single b l d = 0 := fun c d i l =>
    single_mul_single_of_ne c i a b hab d
  have h2 : ∀ (c d : S) (i l : n), single i b c * single a l d = 0 := fun c d i l =>
    single_mul_single_of_ne c i b a hab.symm d
  simp only [lowerTriangularTwoBlockMatrix, weylTwoBlockMatrix, trv, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    single_mul_single_same, h1, h2, zero_add, add_zero]
  ext r c
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases hr : a = r <;> by_cases hc : a = c <;> by_cases hr' : b = r <;> by_cases hc' : b = c <;>
    simp_all <;> first | linear_combination hsy | linear_combination -hsy | ring

theorem weylTwoBlockMatrix_mul_weylTwoBlockMatrixInv (a b : n) (hab : a ≠ b) (y : S) : weylTwoBlockMatrix a b y * weylTwoBlockMatrixInv a b y = 1 := by
  have h1 : ∀ (c d : S) (i l : n), single i a c * single b l d = 0 := fun c d i l =>
    single_mul_single_of_ne c i a b hab d
  have h2 : ∀ (c d : S) (i l : n), single i b c * single a l d = 0 := fun c d i l =>
    single_mul_single_of_ne c i b a hab.symm d
  simp only [weylTwoBlockMatrixInv, weylTwoBlockMatrix, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    single_mul_single_same, h1, h2, zero_add, add_zero]
  ext r c
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.zero_apply]
  by_cases hr : a = r <;> by_cases hc : a = c <;> by_cases hr' : b = r <;> by_cases hc' : b = c <;>
    simp_all <;> ring

theorem isUnit_det_trv (a b : n) (hab : a ≠ b) (x : S) : IsUnit (trv a b x).det := by
  have : trv a b x = transvection a b x := rfl
  rw [this, det_transvection_of_ne a b hab]
  exact isUnit_one

theorem isUnit_det_weylTwoBlockMatrix (a b : n) (hab : a ≠ b) (y : S) : IsUnit (weylTwoBlockMatrix a b y).det :=
  Matrix.isUnit_det_of_right_inverse (weylTwoBlockMatrix_mul_weylTwoBlockMatrixInv a b hab y)

variable {S' : Type} [CommRing S'] (g : S →+* S')

theorem trv_map (a b : n) (x : S) : (trv a b x).map g = trv a b (g x) := by
  ext r c; simp [trv, Matrix.single_apply, Matrix.one_apply, apply_ite g]

theorem weylTwoBlockMatrix_map_ringHom (a b : n) (y : S) : (weylTwoBlockMatrix a b y).map g = weylTwoBlockMatrix a b (g y) := by
  ext r c; simp [weylTwoBlockMatrix, Matrix.single_apply, Matrix.one_apply, apply_ite g]

theorem trv_zero (a b : n) : trv a b (0 : S) = 1 := by simp [trv]

theorem lowerTriangularTwoBlockMatrix_diag_apply {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S] (a b : n) (hab : a ≠ b)
    (s y : S) (i : n) : lowerTriangularTwoBlockMatrix a b s y i i = if i = a then s else if i = b then y else 1 := by
  simp only [lowerTriangularTwoBlockMatrix, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases hia : i = a
  · subst hia; simp [hab, Ne.symm hab]
  · by_cases hib : i = b
    · subst hib; simp [hia, hab, Ne.symm hab]
    · simp [hia, hib, Ne.symm hia, Ne.symm hib]

theorem lowerTriangularTwoBlockMatrix_apply_of_ne {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S] (a b : n)
    (s y : S) (i j : n) (hij : i ≠ j) (h : ¬ (i = b ∧ j = a)) : lowerTriangularTwoBlockMatrix a b s y i j = 0 := by
  simp only [lowerTriangularTwoBlockMatrix, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases h1 : a = i <;> by_cases h2 : a = j <;> by_cases h3 : b = i <;> by_cases h4 : b = j <;> simp_all

end Mat

section Fam

variable {J : Type} [DecidableEq J] {m : J → ℕ} {S : Type} [CommRing S]

def famU (τ₀ : J) (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S :=
  Function.update (fun _ => 1) τ₀ M

theorem famU_self (τ₀ : J) (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) : famU τ₀ M τ₀ = M := by
  simp [famU]

theorem famU_of_ne {τ₀ τ : J} (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) (h : τ ≠ τ₀) : famU τ₀ M τ = 1 := by
  simp [famU, Function.update_of_ne h]

theorem famU_map {S' : Type} [CommRing S'] (g : S →+* S') (τ₀ : J) (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) (τ : J) :
    (famU τ₀ M τ).map g = famU τ₀ (M.map g) τ := by
  by_cases h : τ = τ₀
  · subst h; simp [famU_self]
  · simp [famU_of_ne _ h, Matrix.map_one]

theorem isUnit_det_famU (τ₀ : J) (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) (hM : IsUnit M.det) (τ : J) :
    IsUnit (famU τ₀ M τ).det := by
  by_cases h : τ = τ₀
  · subst h; simpa [famU_self] using hM
  · simp [famU_of_ne _ h]

end Fam

theorem map_mul_alg {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    {k : Type} [Fintype k] [DecidableEq k] (φ : S →ₐ[R] S') (M N : Matrix k k S) :
    (M * N).map φ = M.map φ * N.map φ := Matrix.map_mul (f := φ.toRingHom)

theorem famU_one {J : Type} [DecidableEq J] {m : J → ℕ} {S : Type} [CommRing S] (τ₀ τ : J) :
    famU (m := m) τ₀ (1 : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) τ = 1 := by
  by_cases h : τ = τ₀
  · subst h; simp [famU_self]
  · simp [famU_of_ne _ h]

theorem famU_mul {J : Type} [DecidableEq J] {m : J → ℕ} {S : Type} [CommRing S] (τ₀ τ : J)
    (M N : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) : famU τ₀ M τ * famU τ₀ N τ = famU τ₀ (M * N) τ := by
  by_cases h : τ = τ₀
  · subst h; simp [famU_self]
  · simp [famU_of_ne _ h]

theorem poly_eq_zero_of_toLaurent_eq {R : Type} [CommRing R] (φ ψ : Polynomial R) (m : ℤ) (hm : m < 0)
    (h : Polynomial.toLaurent φ = LaurentPolynomial.T m * LaurentPolynomial.invert (Polynomial.toLaurent ψ)) :
    φ = 0 := by
  have key : ∀ ψ : Polynomial R,
      LaurentPolynomial.trunc (LaurentPolynomial.T m * LaurentPolynomial.invert (Polynomial.toLaurent ψ)) = 0 := by
    intro ψ
    induction ψ using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, mul_add, map_add, hp, hq, add_zero]
    | monomial k a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
        map_mul (LaurentPolynomial.invert (R := R)), LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        mul_left_comm, ← LaurentPolynomial.T_add, LaurentPolynomial.trunc_C_mul_T, if_neg (by omega)]
  rw [← Polynomial.trunc_toLaurent φ, h, key]

theorem eq_zero_of_field {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (hfield : ∀ (L : Type) [Field L] [Algebra c.F L] (w : FrPt Xo c L), evR Xo c g w = 0) : g = 0 := by
  funext p y
  have hred : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  show g p y = 0
  refine IsNilpotent.eq_zero ?_
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : p.R →ₐ[c.F] P.ResidueField := IsScalarTower.toAlgHom c.F p.R P.ResidueField
  obtain ⟨w, hw⟩ := GlobalTheory.FlagTan.exists_frMap φ y
  have h4 := hfield _ w
  rw [GlobalTheory.FlagTan.evR_eq hg.1 hw] at h4
  exact Ideal.algebraMap_residueField_eq_zero.1 h4

open Classical in

theorem eq_zero_of_lt {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (τ₀ : E →+* ℂ)
    (a b : Fin (Dw.mult τ₀)) (hab : (b : ℕ) = a + 1) (hlt : e (some ⟨τ₀, a⟩) < e (some ⟨τ₀, b⟩)) : f = 0 := by
  have hne : a ≠ b := by intro h; rw [h] at hab; omega
  apply eq_zero_of_field hf
  intro L _ _ w
  obtain ⟨p, A, j, y₀, π, X, s, u, α, -, hj, hu, hα, -⟩ := GlobalTheory.FlagTan.exists_chart w w rfl
  obtain ⟨⟨hX, huniv⟩, u₀, hu₀, hchg⟩ := hu
  have calc4 := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c
  let ι : L →ₐ[c.F] Polynomial L := IsScalarTower.toAlgHom c.F L (Polynomial L)
  let M1 : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (Polynomial L) :=
    fun τ => (X τ).map (ι.comp α)
  have hM1 : ∀ τ, IsUnit (M1 τ).det := fun τ => by
    have := (hX τ).map (ι.comp α).toRingHom
    rwa [RingHom.map_det] at this
  let s1 : (Polynomial L)ˣ := Units.map ((ι.comp α) : A.R →* Polynomial L) s
  obtain ⟨α1, hα1, -⟩ := huniv (Polynomial L) (ι.comp (α.comp π))
    (fun τ => famU τ₀ (trv a b Polynomial.X) τ * M1 τ) s1
    (fun τ => by rw [Matrix.det_mul]; exact (isUnit_det_famU _ _ (isUnit_det_trv a b hne _) τ).mul (hM1 τ))
  obtain ⟨α2, hα2, -⟩ := huniv (Polynomial L) (ι.comp (α.comp π))
    (fun τ => famU τ₀ (weylTwoBlockMatrix a b Polynomial.X) τ * M1 τ) s1
    (fun τ => by rw [Matrix.det_mul]; exact (isUnit_det_famU _ _ (isUnit_det_weylTwoBlockMatrix a b hne _) τ).mul (hM1 τ))
  let ev0 : Polynomial L →ₐ[c.F] L := (Polynomial.aeval (0 : L)).restrictScalars c.F
  have hev0ι : ∀ q, ev0 (ι q) = q := fun q => by simp [ev0, ι]
  have hev0X : ev0 Polynomial.X = 0 := by simp [ev0]
  have hev : ev0.comp α1 = α := by
    obtain ⟨k, -, huq⟩ := huniv L (α.comp π) (fun τ => (X τ).map α) (Units.map (α : A.R →* L) s)
      (fun τ => by have := (hX τ).map α.toRingHom; rwa [RingHom.map_det] at this)
    have e1 := huq α ⟨rfl, fun τ => rfl, rfl⟩
    have e2 := huq (ev0.comp α1) ⟨?_, ?_, ?_⟩
    · exact e2.trans e1.symm
    · ext x
      have := congrArg (fun g => g x) hα1.1
      simp only [AlgHom.comp_apply] at this ⊢
      rw [this, hev0ι]
    · intro τ
      rw [show (ev0.comp α1 : A.R → L) = ev0 ∘ α1 from rfl, ← Matrix.map_map, hα1.2.1 τ, map_mul_alg,
        show (X τ).map α = ((X τ).map (ι.comp α)).map ev0 by rw [Matrix.map_map]; congr 1; funext x; simp [hev0ι]]
      rw [show (famU τ₀ (trv a b Polynomial.X) τ).map ev0 = 1 by
        rw [show (ev0 : Polynomial L → L) = (ev0.toRingHom : Polynomial L → L) from rfl, famU_map, trv_map]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hev0X, trv_zero, famU_one]]
      rw [one_mul]
    · show ev0 (α1 s) = α s
      rw [hα1.2.2]
      exact hev0ι _
  let tl : Polynomial L →ₐ[c.F] LaurentPolynomial L := (Polynomial.toLaurentAlg (R := L)).restrictScalars c.F
  let inv : LaurentPolynomial L →ₐ[c.F] LaurentPolynomial L :=
    ((LaurentPolynomial.invert (R := L)).toAlgHom).restrictScalars c.F
  have htl : ∀ q, tl q = Polynomial.toLaurent q := fun q => rfl
  have hinv : ∀ q, inv q = LaurentPolynomial.invert q := fun q => rfl
  have hinvι : ∀ q, inv (tl (ι q)) = tl (ι q) := fun q => by
    simp [htl, hinv, ι, Polynomial.toLaurent_C, LaurentPolynomial.invert_C]
  let β1 := tl.comp α1
  let β2 := inv.comp (tl.comp α2)
  have hβπ : ∀ x, β2 (π x) = β1 (π x) := fun x => by
    have e1 := congrArg (fun g => g x) hα1.1
    have e2 := congrArg (fun g => g x) hα2.1
    simp only [AlgHom.comp_apply] at e1 e2
    simp only [β1, β2, AlgHom.comp_apply, e1, e2, hinvι]
  have hβs : β2 s = β1 s := by
    simp only [β1, β2, AlgHom.comp_apply, hα1.2.2, hα2.2.2]
    exact hinvι _
  obtain ⟨z1, hz1⟩ := GlobalTheory.FlagTan.exists_frMap β1 u
  obtain ⟨z2, hz2⟩ := GlobalTheory.FlagTan.exists_frMap β2 u
  obtain ⟨w0, hw0⟩ := GlobalTheory.FlagTan.exists_frMap (β1.comp π) y₀
  have hw1 : FrMap β1 u₀ w0 := GlobalTheory.FlagTan.frMap_of_comp hu₀ hw0 (fun _ => rfl)
  have hw2 : FrMap β2 u₀ w0 := GlobalTheory.FlagTan.frMap_of_comp hu₀ hw0 (fun x => hβπ x)
  have c1 := ((calc4 A.R).2.2.1 _ β1 X s u₀ u w0 z1 hchg hw1).1 hz1
  have c2 := ((calc4 A.R).2.2.1 _ β2 X s u₀ u w0 z2 hchg hw2).1 hz2
  let Tu : (LaurentPolynomial L)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let Bf : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (LaurentPolynomial L) :=
    fun τ => famU τ₀ (lowerTriangularTwoBlockMatrix a b (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))) τ
  have hN : ∀ τ, (((X τ).map (ι.comp α)).map tl).map inv = ((X τ).map (ι.comp α)).map tl := fun τ => by
    simp only [Matrix.map_map]
    congr 1
    funext x
    exact hinvι _
  have hmat : ∀ τ, Bf τ * (X τ).map β2 = (X τ).map β1 := fun τ => by
    have e1 : (X τ).map β1 = ((X τ).map α1).map tl := by rw [Matrix.map_map]; rfl
    have e2 : (X τ).map β2 = (((X τ).map α2).map tl).map inv := by rw [Matrix.map_map, Matrix.map_map]; rfl
    rw [e1, e2, hα1.2.1 τ, hα2.2.1 τ, map_mul_alg, map_mul_alg, map_mul_alg, hN]
    rw [show ((famU τ₀ (weylTwoBlockMatrix a b Polynomial.X) τ).map tl).map inv =
        famU τ₀ (weylTwoBlockMatrix a b (LaurentPolynomial.T (-1))) τ by
      rw [show (tl : Polynomial L → LaurentPolynomial L) = (tl.toRingHom : Polynomial L → LaurentPolynomial L) from rfl,
        show (inv : LaurentPolynomial L → LaurentPolynomial L) =
          (inv.toRingHom : LaurentPolynomial L → LaurentPolynomial L) from rfl, famU_map, famU_map, weylTwoBlockMatrix_map_ringHom, weylTwoBlockMatrix_map_ringHom]
      simp [htl, hinv, Polynomial.toLaurent_X, LaurentPolynomial.invert_T]]
    rw [show (famU τ₀ (trv a b Polynomial.X) τ).map tl = famU τ₀ (trv a b (LaurentPolynomial.T 1)) τ by
      rw [show (tl : Polynomial L → LaurentPolynomial L) = (tl.toRingHom : Polynomial L → LaurentPolynomial L) from rfl,
        famU_map, trv_map]
      simp [htl, Polynomial.toLaurent_X]]
    rw [← mul_assoc, famU_mul, lowerTriangularTwoBlock_mul_weylTwoBlock_eq_transvection a b hne _ _ (by rw [← LaurentPolynomial.T_add]; simp)]
  have c3 : FrChg Bf 1 z2 z1 := by
    refine ((calc4 (LaurentPolynomial L)).1 _ Bf _ 1 w0 z2 z1 c2).2 ?_
    rw [one_mul, hβs]
    convert c1 using 1
    funext τ
    exact hmat τ
  let t : Ix Dw → (LaurentPolynomial L)ˣ := fun k => Option.elim k 1
    (fun q => if q = ⟨τ₀, a⟩ then Tu else if q = ⟨τ₀, b⟩ then Tu⁻¹ else 1)
  have hba : ¬ (b < a) := by intro h; have := Fin.lt_def.1 h; omega
  have hdiag : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), Bf τ i i = (t (some ⟨τ, i⟩) : LaurentPolynomial L) := by
    intro τ i
    by_cases hτ : τ = τ₀
    · subst hτ
      simp only [Bf, famU_self, t, Option.elim, lowerTriangularTwoBlockMatrix_diag_apply a b hne]
      by_cases hia : i = a
      · subst hia; simp [Tu]
      · by_cases hib : i = b
        · subst hib; simp [hne, Ne.symm hne, Tu]
        · simp [hia, hib]
    · simp [Bf, famU_of_ne _ hτ, t, hτ]
  have hlow : ∀ (τ : E →+* ℂ) (i j : Fin (Dw.mult τ)), i < j → Bf τ i j = 0 := by
    intro τ i j hij
    by_cases hτ : τ = τ₀
    · subst hτ
      simp only [Bf, famU_self]
      refine lowerTriangularTwoBlockMatrix_apply_of_ne a b (LaurentPolynomial.T 1 : LaurentPolynomial L) (LaurentPolynomial.T (-1)) i j (ne_of_lt hij) ?_
      rintro ⟨rfl, rfl⟩
      exact hba hij
    · simp [Bf, famU_of_ne _ hτ, Matrix.one_apply, ne_of_lt hij]
  have hbor : FrBor t z2 z1 := ((calc4 (LaurentPolynomial L)).2.2.2 t z2 z1).2 ⟨Bf, hdiag, hlow, by simpa [t] using c3⟩
  have hw := evR_frBor_univ hj ⟨⟨hX, huniv⟩, u₀, hu₀, hchg⟩ hf hz2 hz1 hbor
  rw [GlobalTheory.FlagTan.evR_eq hf.1 hz1, GlobalTheory.FlagTan.evR_eq hf.1 hz2] at hw
  have hTu : ∀ n : ℤ, ((Tu ^ n : (LaurentPolynomial L)ˣ) : LaurentPolynomial L) = LaurentPolynomial.T n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [LaurentPolynomial.T_zero]
    | succ k ih => rw [zpow_add_one, Units.val_mul, ih, LaurentPolynomial.T_add]
    | pred k ih => rw [zpow_sub_one, Units.val_mul, ih, sub_eq_add_neg, LaurentPolynomial.T_add]; rfl
  have hsa : (some ⟨τ₀, a⟩ : Ix Dw) ≠ some ⟨τ₀, b⟩ := by
    intro h; simp only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact hne h
  have hprod : ((∏ i, t i ^ e i : (LaurentPolynomial L)ˣ) : LaurentPolynomial L) =
      LaurentPolynomial.T (e (some ⟨τ₀, a⟩) - e (some ⟨τ₀, b⟩)) := by
    rw [Finset.prod_eq_mul (some ⟨τ₀, a⟩) (some ⟨τ₀, b⟩) hsa ?_ (by simp) (by simp)]
    · have hb' : (⟨τ₀, b⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≠ ⟨τ₀, a⟩ := by
        intro h; simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact hne h.symm
      simp only [t, Option.elim, if_true, hb', if_false, inv_zpow', Units.val_mul, hTu]
      rw [← LaurentPolynomial.T_add]; ring_nf
    · intro k _ hk
      rcases k with _ | q
      · simp [t]
      · have h1 : q ≠ ⟨τ₀, a⟩ := fun h => hk.1 (by rw [h])
        have h2 : q ≠ ⟨τ₀, b⟩ := fun h => hk.2 (by rw [h])
        simp [t, h1, h2]
  rw [hprod] at hw
  have h0 : α1 (f A u) = 0 := poly_eq_zero_of_toLaurent_eq (α1 (f A u)) (α2 (f A u)) _ (by omega) hw
  rw [GlobalTheory.FlagTan.evR_eq hf.1 hα, ← hev, AlgHom.comp_apply, h0, map_zero]

end GlobalTheory.NonDomVanish
end
end

section
section
noncomputable section

namespace GlobalTheory.ArcQZ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem hasSum_evR_of_chart_natural (hL : GlobalTheory.Reg.EvLaws Xo c) (σ : c.F →+* ℂ) [Algebra c.F ℂ⸨X⸩]
    (hK : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    {v : ℂ} (hv : v ≠ 0) {R : Type} [CommRing R] [Algebra c.F R] (φ : R →ₐ[c.F] ℂ⸨X⸩) (ψ : R →ₐ[c.F] CAt σ)
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩)
    (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ)
    {y₀ : FrPt Xo c R} {y₁ y : FrPt Xo c ℂ⸨X⸩} {yw₁ yw : FrPt Xo c (CAt σ)}
    (h₁ : FrMap φ y₀ y₁) (hy : FrChg G s y₁ y) (hw₁ : FrMap ψ y₀ yw₁) (hyw : FrChg Gw sw yw₁ yw)
    (hφ : ∀ f, HasSum (fun n : ℤ => (φ f).coeff n * v ^ n) (toC (ψ f)))
    (hG : ∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * v ^ n) (toC (Gw τ i k)))
    (hs : HasSum (fun n : ℤ => s.coeff n * v ^ n) (toC sw))
    (hG' : ∀ τ, Summable fun n : ℤ => ((G τ).det⁻¹).coeff n * v ^ n)
    (hs' : Summable fun n : ℤ => (s⁻¹).coeff n * v ^ n) (F : Rul Xo c)
    (hF : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) F) :
    HasSum (fun m : ℤ => (evR Xo c F y).coeff m * v ^ m) (toC (evR Xo c F yw)) := by
  let A := ptRing σ hK hv
  let φA : R →ₐ[c.F] A := φ.codRestrict A fun f => (hφ f).summable
  let GA : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A :=
    fun τ i k => ⟨G τ i k, (hG τ i k).summable⟩
  let sA : A := ⟨s, hs.summable⟩
  obtain ⟨hu1, hu2⟩ := (frChg_exists_unique_units E H Dw l Xo c _ G s y₁).2.2.1 y hy
  have hdet : ∀ τ, ((GA τ).det : ℂ⸨X⸩) = (G τ).det := fun τ => A.val.map_det (GA τ)
  obtain ⟨u₁, hu₁⟩ := hL.bc _ _ φA y₀
  obtain ⟨u, hu⟩ := (frChg_exists_unique_units E H Dw l Xo c A GA sA u₁).1
    (fun τ => isUnit_ptRing σ hK hv _ (by rw [hdet]; exact (hu1 τ).ne_zero) (by rw [hdet]; exact hG' τ))
    (isUnit_ptRing σ hK hv sA hu2.ne_zero hs')
  have e₁ : FrMap A.val u y := frMap_of_frChg_map φA A.val GA sA hu₁ hu h₁ hy
  have eψ : (ptEv σ hK hv).comp φA = ψ := AlgHom.ext fun f => ptEv_eq σ hK hv _ (hφ f)
  have eG : (fun τ => (GA τ).map (ptEv σ hK hv)) = Gw := by
    funext τ
    ext i k
    exact ptEv_eq σ hK hv _ (hG τ i k)
  have es : ptEv σ hK hv sA = sw := ptEv_eq σ hK hv _ hs
  have e₂ : FrMap (ptEv σ hK hv) u yw :=
    frMap_of_frChg_map φA (ptEv σ hK hv) GA sA hu₁ hu (by rw [eψ]; exact hw₁) (by rw [eG, es]; exact hyw)
  rw [GlobalTheory.FlagMod.FlagCover.evR_frMap_of_isReduced hF e₁, GlobalTheory.FlagMod.FlagCover.evR_frMap_of_isReduced hF e₂]
  exact hasSum_ptEv σ hK hv _

theorem hasSum_evR_arc_natural : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ F : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) F → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (toC (evR Xo c F yw)) := by
  intro hL1 hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ y e th Θ z hL hK hχ hβ hP hth hy hz
  obtain ⟨pt, -, -, -, -, hpt1, hpt2, -⟩ := id hy
  have hpt3 : pt ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ⸨X⸩) := by
    rw [← cancel_mono (spMap β), Category.assoc, ← Y.jQ_over, Category.assoc, ← pullback.condition,
      ← Category.assoc Y.jQ, ← Category.assoc]
    show (pt ≫ Y.j) ≫ Y.s = _
    rw [hpt1, Category.assoc, hχ]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (hK (β x)).symm
  obtain ⟨p, j, y₀, hch, hmem⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hL1.secBaseChange E H Dw l Xo c (pt (IsLocalRing.closedPoint ℂ⸨X⸩))
  haveI := hch.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.ArcQ.exists_algHom_of_mem_range j hch.2.2 pt hpt3 hmem
  obtain ⟨y₁, hy₁⟩ := hL.bc _ _ φ y₀
  obtain ⟨G, s, hGs⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 y₁).2.2.2 y
    (by rw [hy₁.1, ← hch.2.1, ← Category.assoc, hφ, hpt2])
  obtain ⟨T₁, h₁⟩ := GlobalTheory.T.holArc_chart_coordinates_hasSum E H Dw l Xo c σ O β Y a χ W g ty Fu Ha p j φ hK hχ hβ hch.1 hch.2.2
    (by rw [← Category.assoc, hφ, hpt1])
  obtain ⟨T₂, h₂⟩ := GlobalTheory.T.frame_matrix_hasSum_alt hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th z p j y₀ φ y₁ G s
    hK hχ hβ hy hz hch hy₁ hGs
  obtain ⟨T₃, h₃⟩ := GlobalTheory.T.hasSum_thetaGenerator_chart_ratio hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th Θ p j y₀ φ y₁ G s
    hK hχ hβ hP hth hy hch hy₁ hGs
  have key : ∀ w : ℂ, max T₁ (max T₂ T₃) < w.im → ∀ yw, AnFr Ha Θ z w yw →
      ∃ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ : FrPt Xo c (CAt σ))
        (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ),
        FrMap ψ y₀ yw₁ ∧ FrChg Gw sw yw₁ yw ∧
        (∀ f, HasSum (fun n : ℤ => (φ f).coeff n * eTwoPi w ^ n) (toC (ψ f))) ∧
        (∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * eTwoPi w ^ n) (toC (Gw τ i k))) ∧
        HasSum (fun n : ℤ => s.coeff n * eTwoPi w ^ n) (toC sw) := by
    intro w hw yw hyw
    rw [max_lt_iff, max_lt_iff] at hw
    obtain ⟨ψ, hψ1, hψ2⟩ := h₁ w hw.1
    obtain ⟨yw₁, hyw₁⟩ := hL.bc _ _ ψ y₀
    obtain ⟨Gw, sw, hw'⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 yw₁).2.2.2 yw
      (by rw [hyw₁.1, ← hch.2.1, hψ1]; exact hyw.1.1)
    exact ⟨ψ, yw₁, Gw, sw, hyw₁, hw', hψ2, h₂ w hw.2.1 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1 hw',
      h₃ w hw.2.2 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1.1 hyw.2 hw'⟩
  by_cases hex : ∃ w : ℂ, max T₁ (max T₂ T₃) < w.im ∧ ∃ yw, AnFr Ha Θ z w yw
  · obtain ⟨w₀, hw₀, yw₀, hyw₀⟩ := hex
    obtain ⟨-, -, Gw₀, sw₀, -, -, -, hG₀, hs₀⟩ := key w₀ hw₀ yw₀ hyw₀
    have hv₀ := GlobalTheory.Conv.eTwoPi_ne_zero w₀
    have cs : s⁻¹ ∈ GlobalTheory.Conv.convLaurent :=
      inv_mem (GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ hs₀.summable)
    have cG : ∀ τ, (G τ).det⁻¹ ∈ GlobalTheory.Conv.convLaurent := fun τ => by
      refine inv_mem ?_
      rw [Matrix.det_apply']
      exact sum_mem fun π _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ =>
        GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ (hG₀ τ _ _).summable)
    obtain ⟨T₄, h₄⟩ := GlobalTheory.Conv.exists_forall_mem_halfRing
      (S := insert s⁻¹ (Set.range fun τ => (G τ).det⁻¹)) ((Set.finite_range _).insert _)
      (by rintro _ (rfl | ⟨τ, rfl⟩); exacts [cs, cG τ])
    refine ⟨max T₄ (max T₁ (max T₂ T₃)), fun w hw yw hyw F hF => ?_⟩
    rw [max_lt_iff] at hw
    obtain ⟨ψ, yw₁, Gw, sw, k₁, k₂, k₃, k₄, k₅⟩ := key w hw.2 yw hyw
    exact hasSum_evR_of_chart_natural hL σ hK (GlobalTheory.Conv.eTwoPi_ne_zero w) φ ψ G s Gw sw hy₁ hGs k₁ k₂ k₃ k₄ k₅
      (fun τ => h₄ _ (Or.inr ⟨τ, rfl⟩) w hw.1) (h₄ _ (Or.inl rfl) w hw.1) F hF
  · exact ⟨_, fun w hw yw hyw => absurd ⟨w, hw, yw, hyw⟩ hex⟩

end GlobalTheory.ArcQZ

namespace GlobalTheory.CuspFrom

section SecZ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Frames
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem evR_frChg_one_secZ {S : Type} [CommRing S] [Algebra c.F S] [IsLocalRing S] {ex : Ix Dw → ℤ}
    (hex : ex none = 0) {F : Rul Xo c} (hF : F ∈ GlobalTheory.AllWt.secZ Xo c ex) {s : S} {y y' : FrPt Xo c S}
    (h : FrChg (fun _ => 1) s y y') : evR Xo c F y' = evR Xo c F y := by
  obtain ⟨u, rfl⟩ := ((GlobalTheory.T.frameChange_exists_unique_invertible E H Dw l Xo c S _ s y).2.2.1 y' h).2
  let t : Ix Dw → Sˣ := fun i => i.elim u fun _ => 1
  have hb : FrBor t y y' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').2
      ⟨fun _ => 1, fun τ i => by simp [t], fun τ i j hij => Matrix.one_apply_ne hij.ne, h⟩
  rw [GlobalTheory.FlagTan.evR_frBor hF hb]
  simp [t, Fintype.prod_option, hex]

theorem exists_arc_secZ' [Algebra c.F ℂ⸨X⸩]
    (halg : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {ξ' : Fin r → E}
    (hξ : (U.X k).IsIso ξ') {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom)
    {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) :
    ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ),
      BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im →
        (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex,
          HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m)
            (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  letI := FractionRing.liftAlgebra ℂ ℂ
  haveI := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  have hK := GlobalTheory.ArcCM.known_holds
  have h1 := hK.laws
  have h2 := hK.laws2
  have hev := hK.ev E H Dw l Xo c
  obtain ⟨hp, hq⟩ := GlobalTheory.ArcCM.Exist.one_le_of_isIso hU hξ
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨aC, htie⟩ := GlobalTheory.CuspFrom.exists_input Uw hσ hU hξ hx
  obtain ⟨Wp, Y, h4, hpush⟩ := GlobalTheory.CuspFrom.exists_model Xo c (by omega)
  have hmono := mono_spMap_subtype (c.V Wp)
  obtain ⟨χ, hχ, -⟩ := h4 ℂ _ 1 (aC.restrict (c.V Wp).subtype) (Or.inl ⟨Field.toIsField ℂ, rfl⟩)
  obtain ⟨hover, hab, hj, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ _).1 hW
  have hty := (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 Dw Uw.g Uw.e
  obtain ⟨Ha⟩ := hK.n5 E H Dw l Xo c _ _ Y σ _ χ W Uw.g _ Uw.F hσ hty (GlobalTheory.ArcInTest.exists_values c Wp) hover
    (fun q hq => hj q (by simpa using hq))
  obtain ⟨T, s, d, z, hd, hz, hflow⟩ := htie _ _ Y χ W Ha
  obtain ⟨-, v₂, -, -⟩ := GlobalTheory.ExpTan.anVec_bijective h1.globalFns E H Dw l Xo c _ _ _ Y _ _ W _ _ Uw.F Ha
  choose e he using fun τ i => (v₂ (z τ i)).exists
  have hB := GlobalTheory.T.constant_vectors_lieBasis_of_complex_arc E H Dw l Xo c σ r U Uw _ _ Y _ χ W Ha e z hσ hz he
  obtain ⟨-, -, th, hth⟩ := GlobalTheory.ThetaOverField.nonzero_generates h1 h2 ℂ (aC.restrict (c.V Wp).subtype).D₀
    DVR.SecOps.secZero
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat h1 h2 E H Dw l Xo c σ _ _ Y _ χ W _ _ Uw.F Ha hty th hth
  have hc : (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ≫ Y.s = spMap (algebraMap c.F ℂ⸨X⸩) ≫ spMap (c.V Wp).subtype := by
    rw [Category.assoc, hover, GlobalTheory.ArcId.sp_comp, GlobalTheory.ArcId.sp_comp, GlobalTheory.ArcId.sp_comp]
    congr 1
    exact RingHom.ext fun t => (halg _).symm
  haveI := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ hc : Sp ℂ⸨X⸩ ⟶ gen Y) ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hab]
    intro hq
    have h0 : HahnSeries.ofPowerSeries ℤ ℂ PowerSeries.X ∈ q.asIdeal := hq
    rw [@Ideal.eq_bot_of_prime _ _ q.asIdeal q.isPrime, Ideal.mem_bot] at h0
    exact PowerSeries.X_ne_zero (HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm))
  let z₀ := IsOpenImmersion.lift Y.jQ _ hr
  have hz₀ : z₀ ≫ Y.jQ = _ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨y, -, hy⟩ := GlobalTheory.ArcQ.exists_isArcFr h1 h2 E H Dw l Xo c _ _ Y ℂ _ _ χ W _ e th hB hth (Or.inr hpush) ℂ⸨X⸩
    (HahnSeries.ofPowerSeries ℤ ℂ) z₀ (by unfold RingHom.Flat; infer_instance)
    (by rw [Model.j, ← Category.assoc, hz₀, pullback.lift_fst])
    (by
      rw [pullback.condition, ← Category.assoc, ← Y.jQ_over, ← Category.assoc, hz₀, pullback.lift_snd,
        GlobalTheory.ArcId.sp_comp]
      rfl)
    (fun τ t => halg _)
  have hbd := GlobalTheory.T.arc_framed_point_extends_to_model_boundary E H Dw l Xo c σ _ _ Y _ χ W e th y halg hover hmono hB hy (fun h =>
    (hab _).1 h (by
      change _ ∈ IsLocalRing.maximalIdeal _
      rw [PowerSeries.maximalIdeal_eq_span_X]
      exact Ideal.mem_span_singleton_self _))
  obtain ⟨T', hT'⟩ := GlobalTheory.ArcQZ.hasSum_evR_arc_natural h1 h2 E H Dw l Xo c σ _ _ Y _ χ W _ _ Uw.F Ha y e th Θ z hev halg hover
    hmono hpush hth hy he
  refine ⟨y, max T (max T' Ha.T), s, d, GlobalTheory.T.boundaryExtension_independent_of_model E H Dw l Xo c _ _ Z _ _ Y _ _ _ y
    (RingHom.ext fun t => (halg t).symm) hbd, hd, fun w hw => ?_⟩
  simp only [max_lt_iff] at hw
  obtain ⟨hxw, hlie⟩ := hflow w hw.1
  refine ⟨hxw, fun ex hex0 F hF => ?_⟩
  obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr h1 h2 E H Dw l Xo c σ r U Uw _ _ Y _ χ W Ha th Θ z hσ hz w
    hw.2.2
  obtain ⟨t, ht⟩ := GlobalTheory.ArcCoeff.frChg_of_anLie Uw.F Ha.i _ (Ha.period w hw.2.2) _ _ z hlie hyw.1
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have e1 := evR_frChg_one_secZ hex0 hF ht
  have := hT' w hw.2.1 yw hyw F hF.1
  rw [e1] at this
  convert this using 1
  exact dif_pos hxw

end SecZ

end GlobalTheory.CuspFrom

section Final

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

theorem GlobalTheory.CuspFrom.exists_arc_secZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) [Algebra c.F ℂ⸨X⸩], (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (ξ' : Fin r → E), (U.X k).IsIso ξ' → ∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r, x ∈ (U.X k).dom → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ), GlobalTheory.CuspFrom.BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im → (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex, HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  intro E _ _ _ H Dw l Xo c σ r U _ halg hσ hU k ξ' hξ x hx O _ β Z
  exact GlobalTheory.CuspFrom.exists_arc_secZ' halg hσ hU hξ hx Z

end Final
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) [Algebra c.F ℂ⸨X⸩], (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (ξ' : Fin r → E), (U.X k).IsIso ξ' → ∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r, x ∈ (U.X k).dom → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ), GlobalTheory.CuspFrom.BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im → (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex, HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  atlas_forward_decl GlobalTheory.CuspFrom.exists_arc_secZ
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenspaceFrame_flagCover_chart_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : FlagCover Y) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V), (algebraMap V K).comp φ = algebraMap c.F K → ∀ (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (yF : Sp K ⟶ Xo.XF c), yF ≫ pullback.snd _ _ = spMap (algebraMap c.F K) → (spMap (algebraMap V K) ≫ q) ≫ X.π = yF ≫ Y.j → ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (X.F.vecAt k q hz rfl τ i)).left := by
  first | exact @GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt | exact GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt | (intros; apply GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option autoImplicit false

namespace GlobalTheory.CompHS

theorem exists_generisation_of_mem_closure {T : Type} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T]
    {U : Set T} (hU : IsOpen U) {y : T} (hy : y ∈ closure U) : ∃ g ∈ U, g ⤳ y := by
  haveI : NoetherianSpace (closure U) := NoetherianSpace.set _
  haveI : QuasiSober (closure U) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  have hd : Dense (Subtype.val ⁻¹' U : Set (closure U)) := fun z => by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_right subset_closure]
    exact z.2
  have hC := irreducibleComponent_mem_irreducibleComponents (⟨y, hy⟩ : closure U)
  have hg := (isIrreducible_irreducibleComponent (x := (⟨y, hy⟩ : closure U))).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  obtain ⟨o, ho, hne, hle⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨p, hp, hpU⟩ := hd.inter_open_nonempty o ho hne
  have hU' : IsOpen (Subtype.val ⁻¹' U : Set (closure U)) := hU.preimage continuous_subtype_val
  exact ⟨_, (hg.mem_open_set_iff hU').2 ⟨p, hle hp, hpU⟩,
    (hg.specializes mem_irreducibleComponent).map continuous_subtype_val⟩

theorem exists_generic_generisation (X : Scheme.{0}) (x : X) (hd : IsDomain (X.presheaf.stalk x)) :
    ∃ ξ : X, ∀ y, y ⤳ x → ξ ⤳ y := by
  let η : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨X.fromSpecStalk x η, fun y hy => ?_⟩
  have : y ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨q, rfl⟩ := this
  exact ((PrimeSpectrum.le_iff_specializes η q).1 (show (⊥ : Ideal _) ≤ _ from bot_le)).map
    (X.fromSpecStalk x).continuous

theorem mem_barComp_of_specializes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (x : Xo.XF c), x ∈ (Z : Set (Xo.XF c)) → ∀ b : Y.X, Y.j x ⤳ b → b ∈ barComp Y Z := by
  intro E _ _ _ H Dw l Xo c Y Z x hx b hb
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str c.F N
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : IsNoetherian Y.X := {}
  intro hcl
  have hopen := Y.j.isOpenEmbedding.isOpenMap
  have hc := (TrivOrderTieCompare.isClopen_comp Z)
  obtain ⟨w, hw, hwb⟩ := exists_generisation_of_mem_closure (hopen _ hc.compl.isOpen) hcl
  obtain ⟨ξ, hξ⟩ := exists_generic_generisation Y.X b (Y.normal b).1
  obtain ⟨u, hu, rfl⟩ := (hξ w hwb).mem_open (hopen _ hc.compl.isOpen) hw
  obtain ⟨v, hv, hv'⟩ := (hξ _ hb).mem_open (hopen _ hc.isOpen) ⟨x, hx, rfl⟩
  exact hu (Y.j.isOpenEmbedding.injective hv' ▸ hv)

end GlobalTheory.CompHS
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_toroidalComponentClosure_of_specializes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (x : Xo.XF c), x ∈ (Z : Set (Xo.XF c)) → ∀ b : Y.X, Y.j x ⤳ b → b ∈ barComp Y Z := by
  atlas_forward_decl GlobalTheory.CompHS.mem_barComp_of_specializes
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

noncomputable section
namespace GlobalTheory.CuspOnTor

theorem evalPt_mem_maximalIdeal {Y : Scheme.{0}} {V : Type} [CommRing V] [IsLocalRing V] (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W)
    (hg : ger _ hy g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (x (IsLocalRing.closedPoint V)))) :
    TangentOrigin.evalPt x W h g ∈ IsLocalRing.maximalIdeal V := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have e : (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (ger _ hy g) = TangentOrigin.evalPt x W h g := by
    have := congrArg (fun φ => φ.hom g) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.trans ?_
    simp only [TangentOrigin.evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
    congr!
  intro hu
  exact hg (isUnit_of_map_unit (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom _ (e ▸ hu))

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens} {R : Type} [CommRing R]

theorem val_restr (h : O' ≤ O) (x : Sp R ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (f : H0 p B O) : H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

theorem val_congr {x x' : Sp R ⟶ Y} (e : x = x') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x' ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst e; rfl

theorem val_spMap {R' : Type} [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (hO' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ O) (hi' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val (spMap ψ ≫ x) i hO' hi' f = ψ (H0.val x i hO hi f) :=
  DFunLike.congr_fun (GlobalTheory.FlagMod.ev_spMap ψ x _ (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi')) (f.loc i)

open GlobalTheory.ShFam GlobalTheory.ShFam.Descent GlobalTheory.CuspFrom GlobalTheory.Toroidal

theorem evR_mem_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : AllWt.Weight Dw) (s : H0 (str₀ X Z) (L₀ X Z la) ⊤), s ∈ vanBd X Z la → ∀ f : GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0), sec₀ X Z _ f = H0.restr le_top s → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K), (algebraMap V K).comp φ = algebraMap c.F K → GlobalTheory.AllWt.LiesOn Z y → GlobalTheory.CuspFrom.BdExt Y φ y → ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f.1 y = algebraMap V K v := by
  intro E _ _ _ H Dw l Xo c Y X Z la s hs f hfs V K _ _ _ _ _ _ _ φ y hφ hZ hB
  classical
  obtain ⟨χ, g, hχ, hpt, hw, hbd⟩ := hB
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  have hfr : GlobalTheory.AllWt.ptF y = GlobalTheory.FlagMod.frX y := GlobalTheory.FlagMod.eq_frX y (Descent.ptF_fst y) (Descent.ptF_snd y)
  have hl := X.lies_ptY y
  have hp : X.ptY y ≫ X.π = spMap (algebraMap V K) ≫ χ ≫ genι Y := by
    rw [hl.1, ← hfr, Model.j, ← Category.assoc, hpt, Category.assoc]
  have : IsProper X.π := X.proper
  have hv : ValuativeCriterion.Existence X.π := by
    have h : UniversallyClosed X.π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨q, q1, q2⟩ : ∃ q : Sp V ⟶ X.YY, spMap (algebraMap V K) ≫ q = X.ptY y ∧ q ≫ X.π = χ ≫ genι Y := by
    obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨V, K, X.ptY y, χ ≫ genι Y, ⟨hp⟩⟩).exists_lift
    exact ⟨q, q1, q2⟩
  have hzy : spMap (algebraMap V K) ≫ q = X.ptY y := q1
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover q
  have hzk : ⊤ ≤ (spMap (algebraMap V K) ≫ q) ⁻¹ᵁ X.F.U k := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have hl' : X.F.Lies (spMap (algebraMap V K) ≫ q) y := hzy ▸ hl
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hl'.1 k hzk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl'

  have hsp : ∀ a : Sp V, a ⤳ IsLocalRing.closedPoint V := fun a => IsLocalRing.specializes_closedPoint a
  let s₀ : Sp K := IsLocalRing.closedPoint K
  have hxe : GlobalTheory.AllWt.ptF y ≫ Y.j = spMap (algebraMap V K) ≫ χ ≫ genι Y := by
    rw [Model.j, ← Category.assoc, hpt, Category.assoc]
  have hb : (χ ≫ genι Y) (IsLocalRing.closedPoint V) ∈ barComp Y Z := by
    refine GlobalTheory.T.mem_toroidalComponentClosure_of_specializes E H Dw l Xo c Y Z (GlobalTheory.AllWt.ptF y s₀) (hZ s₀) _ ?_
    have h1 := (hsp (spMap (algebraMap V K) s₀)).map (χ ≫ genι Y).continuous
    have h2 : Y.j (GlobalTheory.AllWt.ptF y s₀) = (χ ≫ genι Y) (spMap (algebraMap V K) s₀) := by
      have := congrArg (fun m => m s₀) hxe
      simpa only [Scheme.Hom.comp_apply] using this
    rw [h2]
    exact h1
  have hq0 : ∀ a : Sp V, q a ∈ X.π ⁻¹ᵁ barComp Y Z := fun a => by
    have h1 : X.π (q (IsLocalRing.closedPoint V)) ∈ barComp Y Z := by
      have h0 : (q ≫ X.π) (IsLocalRing.closedPoint V) ∈ barComp Y Z := q2 ▸ hb
      exact h0
    exact ((hsp a).map q.continuous).mem_open (X.π ⁻¹ᵁ barComp Y Z).isOpen h1
  have hr : Set.range q ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨_, hq0 a⟩, rfl⟩
  let w := IsOpenImmersion.lift (inc₀ X Z) q hr
  have hwq : w ≫ inc₀ X Z = q := IsOpenImmersion.lift_fac _ _ _

  have hbdy : w (IsLocalRing.closedPoint V) ∈ bd₀ X Z := by
    intro hU
    have h1 : X.π (inc₀ X Z (w (IsLocalRing.closedPoint V))) ∈ LogKS.interior Y := hU
    obtain ⟨x₀, hx₀⟩ := h1
    have h2 : (w ≫ inc₀ X Z ≫ X.π) (IsLocalRing.closedPoint V) = (χ ≫ genι Y) (IsLocalRing.closedPoint V) := by
      rw [← Category.assoc, hwq, q2]
    simp only [Scheme.Hom.comp_apply] at h2
    have h3 : genι Y (Y.jQ x₀) = genι Y (χ (IsLocalRing.closedPoint V)) := hx₀.trans h2
    refine (mem_genBd_iff.1 hbd) ?_
    rw [← h3]
    have h4 : Y.jQ x₀ ∈ pullback.fst Y.s (spMap (RingHom.id c.F)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨x₀, rfl⟩
    exact h4

  have hO : ⊤ ≤ (spMap (algebraMap V K) ≫ q) ⁻¹ᵁ flagOpen X := by
    rw [hzy, ← X.pt_inc y]; exact GlobalTheory.FlagMod.le_preimage_map (z := X.pt y) X.inc (top_le_inc X) le_top
  have a := evR_eq_val_secOf f hO hQ ht
  have hwK : (spMap (algebraMap V K) ≫ w) ≫ inc₀ X Z = spMap (algebraMap V K) ≫ q := by rw [Category.assoc, hwq]
  have hk' : ⊤ ≤ ((spMap (algebraMap V K) ≫ w) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := hwK ▸ hzk
  have hO' : ⊤ ≤ ((spMap (algebraMap V K) ≫ w) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hwK ▸ hO
  have hk₀ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := hwq ▸ hz
  have hU₀ : ⊤ ≤ (spMap (algebraMap V K) ≫ w) ⁻¹ᵁ U₀ X Z := fun a ha => hO' ha
  have hjK : ⊤ ≤ (spMap (algebraMap V K) ≫ w) ⁻¹ᵁ (LL₀ X Z (GlobalTheory.AllWt.exOf Dw la 0)).U (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) :=
    fun a ha => mem_pIdx.2 (hk' ha)
  have hj₀ : ⊤ ≤ w ⁻¹ᵁ (LL₀ X Z (GlobalTheory.AllWt.exOf Dw la 0)).U (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) :=
    fun a ha => mem_pIdx.2 (hk₀ ha)
  have b1 := H0.val_pull (inc₀ X Z) (le_refl (U₀ X Z)) (spMap (algebraMap V K) ≫ w)
    (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) hU₀ hjK hO' hk' (secOf X _ f)
  have b2 : H0.val (spMap (algebraMap V K) ≫ w) (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) hU₀ hjK (sec₀ X Z _ f) =
      algebraMap V K (H0.val w (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) le_top hj₀ s) := by
    rw [hfs, val_restr le_top _ _ le_top hU₀ hjK s]
    exact val_spMap _ w _ le_top hj₀ le_top hjK s
  have b3 : H0.val w (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) le_top hj₀ s ∈ IsLocalRing.maximalIdeal V := by
    have hi : w (IsLocalRing.closedPoint V) ∈ (LL₀ X Z (GlobalTheory.AllWt.exOf Dw la 0)).U (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) :=
      hj₀ (Set.mem_univ _)
    exact evalPt_mem_maximalIdeal w _ _ _ ⟨trivial, hi⟩ (hs _ hbdy _ hi)

  have hbc : Vanish.FrameBC Y := GlobalTheory.T.exists_lieEigenspaceFrame_localRing_baseChange E H Dw l Xo c _ _ Y
  obtain ⟨fC, hfC⟩ := GlobalTheory.T.exists_lieEigenspaceFrame_flagCover_chart_domain E H Dw l Xo c _ _ Y X V K φ hφ q k hz (GlobalTheory.FlagMod.frX y) (GlobalTheory.FlagMod.frX_snd y) hl'.1
  obtain ⟨g', hg'⟩ : ∃ g' : EigFrame Y φ (q ≫ X.π), ∀ τ i, g'.v τ i = g.v τ i := by
    rw [q2]; exact ⟨g, fun _ _ => rfl⟩
  obtain ⟨gk, hgk⟩ := hbc.at g' (algebraMap V K) (x' := spMap (algebraMap V K) ≫ q ≫ X.π) rfl
  obtain ⟨fK, hfK⟩ := hbc.at fC (algebraMap V K) (x' := spMap (algebraMap V K) ≫ q ≫ X.π) rfl
  have hTy : Comparison₂ y gk := ⟨hφ, by rw [q2]; exact hxe, fun τ i => by
    rw [hgk, hg']
    obtain ⟨w₁, w₂, w₃, w₄⟩ := hw τ i
    exact ⟨w₁, w₂, w₃, w₄⟩⟩
  have hQx : GlobalTheory.FlagMod.frX Q ≫ Y.j = spMap (algebraMap V K) ≫ q ≫ X.π := by
    rw [hQ.over, Category.assoc]
  have hfrQ : GlobalTheory.AllWt.ptF Q = GlobalTheory.FlagMod.frX Q := GlobalTheory.FlagMod.eq_frX Q (Descent.ptF_fst Q) (Descent.ptF_snd Q)
  have hTQ : Comparison₂ Q fK := ⟨hφ, by rw [hfrQ]; exact hQx, fun τ i => by
    have e1 : fK.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (GlobalTheory.FlagMod.frVec Y Q hQx τ i)).left := by
      rw [hfK, hfC, ← GlobalTheory.FlagMod.tanPull_left (algebraMap V K) rfl,
        GlobalTheory.FlagMod.Frames.tanPull_vecAt X.F k (algebraMap V K) q hz hzk rfl (Category.assoc _ _ _) rfl τ i,
        hQ.frVec_eq (Category.assoc _ _ _) hQx]
    rw [e1, hfrQ]
    obtain ⟨u, u₁, u₂, u₃⟩ := (GlobalTheory.FlagMod.toModel_eq_iff (GlobalTheory.FlagMod.frX Q) (GlobalTheory.FlagMod.frX_fst Q) hQx (Q.tan τ i) _).1 rfl
    exact ⟨u, u₁, u₂, u₃⟩⟩
  have hT1 := Comparison₂.tri_of_bm hTQ hTy (BM.of_frBor ht)
  have hd1 : spMap (dualMap (AlgHom.id c.F K).toRingHom) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have hF : fC.Tri (algebraMap V K) gk fun τ i => t (some ⟨τ, i⟩) := by
    refine ⟨rfl, rfl, fun τ i => ?_⟩
    obtain ⟨cf, c1, c2, c3⟩ := hT1.2.2 τ i
    refine ⟨cf, c1, c2, ?_⟩
    have e : (fun j => spMap (dualMap (algebraMap V K)) ≫ fC.v τ j) =
        fun j => spMap (dualMap (AlgHom.id c.F K).toRingHom) ≫ fK.v τ j := by
      funext j
      rw [hd1, Category.id_comp, hfK]
    rw [e]
    exact c3
  have hG : g'.Tri (algebraMap V K) gk 1 := by
    refine ⟨rfl, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩⟩
    have e : (fun j => spMap (dualMap (algebraMap V K)) ≫ g'.v τ j) = gk.v τ := funext fun j => (hgk τ j).symm
    rw [e]
    exact isCombAtG_single Y.t _ (gk.tan τ) i
  obtain ⟨uu, huu⟩ := CoordUniq.exists_unit_ratio fC g' hinj hF hG
  have hu' := huu (algebraMap V K) gk _ _ hF hG
  let Wn : Vˣ := ∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), uu x.1 x.2 ^ GlobalTheory.AllWt.exOf Dw la 0 (some x)
  have hW : ((∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix : Kˣ) : K) = algebraMap V K (Wn : V) := by
    have h0 : GlobalTheory.AllWt.exOf Dw la 0 none = 0 := rfl
    have : (∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix : Kˣ) = Units.map (algebraMap V K : V →* K) Wn := by
      simp only [Fintype.prod_option, h0, zpow_zero, one_mul, Wn, map_prod, map_zpow]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [show t (some x) = _ from hu' x.1 x.2]
      simp
    rw [this]; rfl
  refine ⟨Wn * H0.val w (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) le_top hj₀ s, Ideal.mul_mem_left _ _ b3, ?_⟩
  rw [a, hW, map_mul, ← b2]
  congr 1
  exact (val_congr hwK.symm _ _ _ _ _ _).trans (b1.symm)


end GlobalTheory.CuspOnTor
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.VanishingBound

theorem keySec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) : Nonempty (GlobalTheory.ShFam.KeySec Y.d.Xo₂ Y.d.c₂) := by
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf σ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F (by omega) hY.geo

theorem isSec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (la : AllWt.Weight (T.Q.Dw j)) (f : Rul Y.d.Xo₂ Y.d.c₂)
    (hf : f ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k) :
    ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k) := by
  have hU := hY.unf σ hσ
  by_cases hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ →
      (wtOf (T.Q.Dw j) la 0).1 (τ, j') ≤ (wtOf (T.Q.Dw j) la 0).1 (τ, i)
  · by_cases hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q
    · exact GlobalTheory.T.isSec_reading_decreasing_integer_exponents _ _ _ _ _ _ σ _ (Y.U σ) (keySec D T j Y e o hY σ hσ) hσ hU hpq _
        (AllWt.even_wtOf la 0) hdec f hf k
    · have hp : (T.Q.Dw j).p = 0 := by omega
      have hq : (T.Q.Dw j).q = 0 := by omega
      have hG : wtOf (T.Q.Dw j) la 0 = wtZ (fun _ => 0) 0 := by
        refine Prod.ext (funext fun x => ?_) ?_
        · simp only [wtOf, wtZ, hp, hq]
          split_ifs <;> first | (exfalso; omega) | simp
        · simp [wtOf, wtZ]
      rw [hG, AllWt.modelWt_wtZ]
      have hf' : f ∈ sec Y.d.Xo₂ Y.d.c₂ (fun _ => 0) 0 := by
        rw [← AllWt.secZ_nat, ← AllWt.exZ_wtZ, ← hG]
        exact hf
      exact hU.2.2.2.2.1 _ _ ⟨fun τ => fun a b _ => le_refl _, ⟨0, rfl⟩⟩ f hf' k
  · have hex : ∃ (τ : D.host.E →+* ℂ) (m : ℕ) (hm : m + 1 < (T.Q.Dw j).mult τ),
        (wtOf (T.Q.Dw j) la 0).1 (τ, m) < (wtOf (T.Q.Dw j) la 0).1 (τ, m + 1) := by
      by_contra hne
      push_neg at hne
      apply hdec
      intro τ i j' hij hj'
      revert hj'
      induction j', hij using Nat.le_induction with
      | base => intro _; exact le_refl _
      | succ n hn ih => intro hj'; exact (hne τ n hj').trans (ih (by omega))
    obtain ⟨τ, m, hm, hlt⟩ := hex
    have h0 : f = 0 := GlobalTheory.NonDomVanish.eq_zero_of_lt hf τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl hlt
    subst h0
    rw [map_zero]
    exact ⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩

open scoped LaurentSeries in

theorem fjZero (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (la : AllWt.Weight (T.Q.Dw j)) (s) (hs : s ∈ vanBd TF.X Z la)
    (f : GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (hfs : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ GlobalTheory.AllWt.suppOn Z) (hfsec : sec₀ TF.X Z _ f = H0.restr le_top s)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k)
    (hsec : ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k))
    (ξ) (hξ : ((Y.U σ).X k).IsIso ξ) (x) (hx : x ∈ ((Y.U σ).X k).dom) :
    ((Y.U σ).X k).fj (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) ξ 0 (rdU (Y.U σ) f k) x = 0 := by
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hU := hG.unf σ hσ
  letI : Algebra Y.d.c₂.F ℂ⸨X⸩ := (GlobalTheory.ArcId.cstL.comp σ).toAlgebra
  have halg : ∀ x : Y.d.c₂.F, algebraMap Y.d.c₂.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)) :=
    fun _ => rfl
  obtain ⟨y, T₀, s', d, hbd, hd, hw⟩ :=
    GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) halg hσ hU k ξ hξ x hx _ _ TF.Y
  have hc : (algebraMap (PowerSeries ℂ) ℂ⸨X⸩).comp ((PowerSeries.C (R := ℂ)).comp σ) = algebraMap Y.d.c₂.F ℂ⸨X⸩ :=
    RingHom.ext fun t => (halg t).symm
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 none = 0 := rfl
  have hcoef : ∀ m ≤ (0:ℤ), (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff m = 0 := by
    intro m hm
    by_cases hZ : GlobalTheory.AllWt.LiesOn Z y
    · obtain ⟨v, hv, hval⟩ :=
        GlobalTheory.CuspOnTor.evR_mem_maximalIdeal _ _ _ _ _ _ TF.Y TF.X Z la s hs f hfsec (PowerSeries ℂ) ℂ⸨X⸩ _ y hc hZ hbd
      rw [hval]; exact GlobalTheory.CuspFrom.coeff_eq_zero hv hm
    · rw [hfs ℂ⸨X⸩ y ((GlobalTheory.AllWt.liesOff_iff Z y).2 hZ)]; rfl
  exact GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line _ _ _ _ _ ξ x s' d T₀ (fun j => (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff j) hsec
    (GlobalTheory.CuspFrom.freqNonneg _ hf1 hsec) hξ hx hd hcoef fun w hw' => ⟨(hw w hw').1, (hw w hw').2 _ hex _ f.2⟩

end GlobalTheory.HSApp.VanishingBound

namespace GlobalTheory.HSApp

open GlobalTheory.HSApp.VanishingBound in

theorem vanBd_le_space : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), vanBd TF.X Z la ≤ space TF.X Z Y.U la := by
  intro D T j Y e o hG hf Z TF la s hs
  obtain ⟨f, hfZ, hfs⟩ := GlobalTheory.T.exists_supportedRule_of_flagComponentSection _ _ _ _ _ _ _ TF.X Z (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) (H0.restr le_top s)
  have hsec := isSec D T j Y e o hG la f.1 f.2
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hcusp : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0) := by
    refine ⟨GlobalTheory.AllWt.mem_cuspW.2 ⟨f.2, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩, hfZ⟩
    have h0 := fjZero D T j Y e o hG hf Z TF la s hs f hfZ hfs σ hσ k (hsec σ hσ k)
    have h3 := (GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ (hsec σ hσ k) (GlobalTheory.CuspFrom.isModerate _ hf1 (hsec σ hσ k)) h0).1.2
    exact ⟨⟨hsec σ hσ k, h3⟩, fun ξ hξ x hx => h0 ξ hξ x hx⟩
  exact ⟨⟨f.1, hcusp⟩, hfs⟩

end GlobalTheory.HSApp
end
