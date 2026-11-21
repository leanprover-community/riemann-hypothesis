import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMaximalLePrimeAddDim
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackHeightCompare

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

private theorem isHomogeneous_cast {φ : MvPolynomial (Fin 5) ℝ} {m k : ℕ} (h : φ.IsHomogeneous m) (e : m = k) :
    φ.IsHomogeneous k := e ▸ h

theorem powSum_sub_factor (t p q : MvPolynomial (Fin 5) ℝ)
    (ht : t.IsHomogeneous 1) (hp : p.IsHomogeneous 1) (hq : q.IsHomogeneous 1) (n : ℕ) :
    (∃ R : MvPolynomial (Fin 5) ℝ, R.IsHomogeneous n ∧
        t ^ (n + 2) + (p + q - t) ^ (n + 2) - p ^ (n + 2) - q ^ (n + 2) = (t - p) * (t - q) * R) ∧
      (∃ R : MvPolynomial (Fin 5) ℝ, R.IsHomogeneous (n + 1) ∧
        t ^ (n + 3) + (p + q - t) ^ (n + 3) - p ^ (n + 3) - q ^ (n + 3) = (t - p) * (t - q) * R) := by
  have hσ : (p + q).IsHomogeneous 1 := hp.add hq
  have hs : (p + q - t).IsHomogeneous 1 := hσ.sub ht
  induction n with
  | zero =>
    refine ⟨⟨1 + 1, (isHomogeneous_one (Fin 5) ℝ).add (isHomogeneous_one (Fin 5) ℝ), by ring⟩,
      ⟨(p + q) + (p + q) + (p + q), (hσ.add hσ).add hσ, by ring⟩⟩
  | succ n ih =>
    obtain ⟨⟨R₁, h₁, e₁⟩, ⟨R₂, h₂, e₂⟩⟩ := ih
    refine ⟨⟨R₂, h₂, e₂⟩, ⟨(p + q) * R₂ - t * (p + q - t) * R₁ + (p ^ (n + 2) + q ^ (n + 2)), ?_, ?_⟩⟩
    · have a₁ : ((p + q) * R₂).IsHomogeneous (n + 1 + 1) := isHomogeneous_cast (hσ.mul h₂) (by omega)
      have a₂ : (t * (p + q - t) * R₁).IsHomogeneous (n + 1 + 1) :=
        isHomogeneous_cast ((ht.mul hs).mul h₁) (by omega)
      have a₃ : (p ^ (n + 2) + q ^ (n + 2)).IsHomogeneous (n + 1 + 1) :=
        isHomogeneous_cast ((hp.pow (n + 2)).add (hq.pow (n + 2))) (by omega)
      exact (a₁.sub a₂).add a₃
    · linear_combination (p + q) * e₂ - t * (p + q - t) * e₁

theorem onLine_sub_onBase_factor (d : ℕ) (a b : ℤ) : ∃ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d ∧
    onLine d a b - onBase d a b = (X 0 - X 4) * (X 0 - X 3) * K := by
  have hX : ∀ i : Fin 5, (X i : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 := fun i => isHomogeneous_X ℝ i
  have hCX : ∀ (r : ℝ) (i : Fin 5), (C r * X i : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    fun r i => isHomogeneous_C_mul_X r i
  have ht : (C (a : ℝ) * X 0 + C (b : ℝ) * (X 3 + X 4 - X 0) + X 2 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    ((hCX _ 0).add (isHomogeneous_cast ((isHomogeneous_C (Fin 5) (b : ℝ)).mul (((hX 3).add (hX 4)).sub (hX 0)))
      (by omega))).add (hX 2)
  have hp : (C (a : ℝ) * X 4 + C (b : ℝ) * X 3 + X 2 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    ((hCX _ 4).add (hCX _ 3)).add (hX 2)
  have hq : (C (b : ℝ) * X 4 + C (a : ℝ) * X 3 + X 2 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    ((hCX _ 4).add (hCX _ 3)).add (hX 2)
  obtain ⟨R, hR, e⟩ := (powSum_sub_factor _ _ _ ht hp hq d).1
  refine ⟨(C (a : ℝ) - C (b : ℝ)) ^ 2 * R, isHomogeneous_cast
    ((((isHomogeneous_C (Fin 5) (a : ℝ)).sub (isHomogeneous_C (Fin 5) (b : ℝ))).pow 2).mul hR) (by omega), ?_⟩
  have hL : onLine d a b = (C (a : ℝ) * X 0 + C (b : ℝ) * (X 3 + X 4 - X 0) + X 2) ^ (d + 2) +
      (C (b : ℝ) * X 0 + C (a : ℝ) * (X 3 + X 4 - X 0) + X 2) ^ (d + 2) := by
    simp only [onLine, swapSum, lin, map_add, map_pow, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, map_one, one_mul]
  have hB : onBase d a b = (C (a : ℝ) * X 4 + C (b : ℝ) * X 3 + X 2) ^ (d + 2) +
      (C (b : ℝ) * X 4 + C (a : ℝ) * X 3 + X 2) ^ (d + 2) := by
    simp only [onBase, swapSum, lin, map_add, map_pow, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, map_one, one_mul]
  have hs : (C (b : ℝ) * X 0 + C (a : ℝ) * (X 3 + X 4 - X 0) + X 2 : MvPolynomial (Fin 5) ℝ) =
      (C (a : ℝ) * X 4 + C (b : ℝ) * X 3 + X 2) + (C (b : ℝ) * X 4 + C (a : ℝ) * X 3 + X 2) -
        (C (a : ℝ) * X 0 + C (b : ℝ) * (X 3 + X 4 - X 0) + X 2) := by ring
  rw [hL, hB, hs]
  linear_combination e

end GlobalTheory.CovTest.SwapLine
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_line_base_difference : ∀ (d : ℕ) (a b : ℤ), ∃ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d ∧
    onLine d a b - onBase d a b = (X 0 - X 4) * (X 0 - X 3) * K := by
  atlas_forward_decl GlobalTheory.CovTest.SwapLine.onLine_sub_onBase_factor
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_maximal_le_prime_add_dim : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] (P M : Ideal A) [P.IsPrime] [M.IsMaximal], (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  first | exact @GlobalTheory.FinTypeIntCatenary.height_maximal_le | exact GlobalTheory.FinTypeIntCatenary.height_maximal_le | (intros; apply GlobalTheory.FinTypeIntCatenary.height_maximal_le <;> assumption)
end

section
section
open scoped TensorProduct

namespace GlobalTheory.FibreMax

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem exists_isMaximal_height_ge (k : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    [CharZero k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [FaithfulSMul k A] (d : ℕ) (hd : ringKrullDim (FractionRing k ⊗[k] A) = d) :
    ∃ M : Ideal A, M.IsMaximal ∧ ((d + 1 : ℕ) : ℕ∞) ≤ M.height := by
  classical
  have hloc := IsLocalization.tensorRight (S := A) (FractionRing k) (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : IsDomain (FractionRing k ⊗[k] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hd.ge
  let f : PrimeSpectrum (FractionRing k ⊗[k] A) → PrimeSpectrum A :=
    PrimeSpectrum.comap (algebraMap A (FractionRing k ⊗[k] A))
  have hf : StrictMono f :=
    Monotone.strictMono_of_injective (fun _ _ h ↦ Ideal.comap_mono h)
      (PrimeSpectrum.localization_comap_injective _ (Algebra.algebraMapSubmonoid A (nonZeroDivisors k)))
  let q := f l.last
  have hq : ∀ c : k, c ≠ 0 → algebraMap k A c ∉ q.asIdeal := by
    intro c hc h
    have hu : IsUnit (algebraMap A (FractionRing k ⊗[k] A) (algebraMap k A c)) :=
      IsLocalization.map_units (FractionRing k ⊗[k] A)
        (⟨algebraMap k A c, c, mem_nonZeroDivisors_of_ne_zero hc, rfl⟩ :
          Algebra.algebraMapSubmonoid A (nonZeroDivisors k))
    exact l.last.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  have hne : q.asIdeal ≠ M := by
    intro heq
    haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
    haveI : Algebra.FiniteType ℤ k := inferInstance
    haveI : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance inferInstance
    letI := Ideal.Quotient.field M
    haveI : Module.Finite ℤ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ M)
    have hinj : Function.Injective (algebraMap ℤ (A ⧸ M)) := by
      refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
      have h1 : algebraMap ℤ (A ⧸ M) x = Ideal.Quotient.mk M (algebraMap k A (x : k)) := by simp
      rw [h1, Ideal.Quotient.eq_zero_iff_mem, ← heq] at hx
      by_contra hx0
      exact hq (x : k) (Int.cast_ne_zero.2 hx0) hx
    exact Int.not_isField ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))
  let Mp : PrimeSpectrum A := ⟨M, hM.isPrime⟩
  have hlt : (l.map f hf).last < Mp := by
    change q < Mp
    exact lt_of_le_of_ne hqM fun h ↦ hne (congrArg PrimeSpectrum.asIdeal h)
  let L := (l.map f hf).snoc Mp hlt
  have hlen : L.length = d + 1 := by simp [L, hl]
  refine ⟨M, hM, ?_⟩
  rw [show M = Mp.asIdeal from rfl, PrimeSpectrum.height_eq_orderHeight, ← hlen]
  exact Order.length_le_height (by simp [L])

end GlobalTheory.FibreMax
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_height_succ_dim : ∀ (k : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [CharZero k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [FaithfulSMul k A] (d : ℕ), ringKrullDim (FractionRing k ⊗[k] A) = d → ∃ M : Ideal A, M.IsMaximal ∧ ((d + 1 : ℕ) : ℕ∞) ≤ M.height := by
  atlas_forward_decl GlobalTheory.FibreMax.exists_isMaximal_height_ge
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.CodimOneDim

theorem le_of_add (D : ℕ) (a : ℕ∞) (r : WithBot ℕ∞) (ha : a = 1)
    (h : (((D + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) + r) : (D : WithBot ℕ∞) ≤ r := by
  subst ha
  induction r using WithBot.recBotCoe with
  | bot => simp at h
  | coe r =>
    induction r using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe r =>
      have : D + 1 ≤ 1 + r := by exact_mod_cast h
      exact_mod_cast (show D ≤ r by omega)

theorem topologicalKrullDim_eq_of_coheight_eq_one : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
    Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D := by
  intro k _ Y p D h Z i _ _ hz
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isIntegral
  obtain ⟨d, hd⟩ := h.exists_dim_eq i
  rw [hd]

  have hup : topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y :=
    GlobalTheory.DimCodim.dim_add_le_of_le_coheight (S := Y) (W := Z) i.continuous
      i.isClosedEmbedding.injective 1 fun w => by
        rw [← hz]
        exact Order.coheight_anti (genericPoint_specializes w |>.map i.continuous)
  rw [hd, h.dim_eq] at hup
  have hdD : d ≤ D := by
    have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hup
    have : d + 1 ≤ D + 1 := by exact_mod_cast this
    omega
  obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over p (i (genericPoint Z))
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h j hj
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance inferInstance
  have hst : ringKrullDim (Y.presheaf.stalk (j q)) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hq, hz]; rfl
  let x : Spec (.of A) := q
  have : IsIso (j.stalkMap x) := inferInstance
  have e := (asIso (j.stalkMap x) ≪≫ Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv
  have hq1 : (q.asIdeal.height : WithBot ℕ∞) = 1 := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv e, hst]
  obtain ⟨_, hKA⟩ := RegGenSmooth.ringKrullDim_chart h
    (IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))) j hj
  obtain ⟨M, _, hM⟩ := GlobalTheory.T.exists_maximal_height_succ_dim k A D hKA
  have h2 := GlobalTheory.T.height_maximal_le_prime_add_dim A q.asIdeal M
  have hM' : (((D + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
      (q.asIdeal.height : WithBot ℕ∞) + ringKrullDim (A ⧸ q.asIdeal) :=
    (WithBot.coe_le_coe.2 hM).trans h2
  have hq1' : q.asIdeal.height = 1 := by exact_mod_cast hq1
  have hDq := le_of_add D _ _ hq1' hM'
  have hsub : (Set.range j ∩ closure {j q} : Set Y) ⊆ Set.range i := fun y hy =>
    closure_minimal (s := {j q}) (Set.singleton_subset_iff.2 (⟨genericPoint Z, hq.symm⟩ : j q ∈ Set.range i))
      i.isClosedEmbedding.isClosed_range hy.2
  have e₁ := topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding
    (rfl : Set.range i = Set.range i)
  have h3 : topologicalKrullDim (Set.range j ∩ closure {j q} : Set Y) ≤ topologicalKrullDim Z := by
    rw [← e₁]
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j q, hd] at h3
  have h4 : (D : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := hDq.trans h3
  have h5 : D ≤ d := by exact_mod_cast h4
  rw [show d = D by omega]
end GlobalTheory.CodimOneDim
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_divisor_dimension : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
    Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D := by
  first | exact @GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one | exact GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one | (intros; apply GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one <;> assumption)
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.VertFun

noncomputable def iterD {ι : Type} : (m : ℕ) → (Fin m → ι) → (MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ)
  | 0, _ => LinearMap.id
  | m + 1, a => (MvPolynomial.pderiv (a 0)).toLinearMap ∘ₗ iterD m (Fin.tail a)

theorem pderiv_lin {ι : Type} [Fintype ι] (x : ι → ℝ) (j : ι) :
    MvPolynomial.pderiv j (lin x) = MvPolynomial.C (x j) := by
  rw [lin, map_sum, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [MvPolynomial.pderiv_X, Pi.single_apply, hb, hb.symm]
  · simp

theorem iterD_lin_pow {ι : Type} [Fintype ι] (x : ι → ℝ) (N : ℕ) : ∀ (m : ℕ) (a : Fin m → ι),
    iterD m a (lin x ^ N) = MvPolynomial.C ((N.descFactorial m : ℝ) * ∏ j, x (a j)) * lin x ^ (N - m)
  | 0, a => by simp [iterD]
  | m + 1, a => by
    rw [iterD, LinearMap.comp_apply, iterD_lin_pow x N m, Derivation.coeFn_coe, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_pow, pderiv_lin, Nat.descFactorial_succ, Fin.prod_univ_succ, Nat.sub_sub]
    simp only [Fin.tail, Nat.cast_mul, map_mul, map_natCast]
    ring

theorem exists_functional {ι : Type} [Fintype ι] (e : ℕ) (I : (Fin e → ι) → ℝ) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ x : ι → ℝ, T (lin x ^ e) = ∑ a : Fin e → ι, (∏ j, x (a j)) * I a := by
  refine ⟨∑ a : Fin e → ι, (I a / (e.factorial : ℝ)) • (MvPolynomial.lcoeff ℝ 0 ∘ₗ iterD e a), fun x => ?_⟩
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have he : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast e.factorial_ne_zero
  rw [LinearMap.smul_apply, LinearMap.comp_apply, iterD_lin_pow, Nat.sub_self, pow_zero, mul_one,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_zero_C, Nat.descFactorial_self, smul_eq_mul]
  field_simp

theorem topSelf_comb_pull {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {κ : Type} [Field κ]
    {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = D) (i : Z ⟶ X)
    {ι : Type} [Fintype ι] (N : ι → HermLB p) (n : ι → ℤ) :
    (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ) =
      ∑ a : Fin D → ι, (∏ j, (n (a j) : ℝ)) * (interNum κ (structureModule Z) (fun j => (N (a j)).B.pull i) : ℝ) := by
  have HD := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ Z) (structureModule Z) hp (d := D)
    (by rw [QCoh.suppDim_structureModule, hd])
  have hL : ∀ j, ((N j).B.pull i).IsLB := fun j => LB.isLB_pull (N j).isLB i
  have e := HD.interNum_of_cls_eq_sum (L := fun j => (N j).B.pull i) hL (Q := fun _ => (comb N n).B.pull i)
    (fun _ => LB.isLB_pull (comb N n).isLB i) (fun _ => n) fun _ => by
      rw [CechPic.cls_pull (comb N n).isLB, GenFibreSecs.cls_comb, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, CechPic.cls_pull (N j).isLB]
  rw [topSelf_def, e]
  push_cast
  rfl

theorem exists_vertical_functional : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra (ZMod ℓ) Γ(Z, ⊤)] (e : ℕ), topologicalKrullDim Z = e → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p),
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g →
      g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ e) := by
  intro k _ Y p D hY Z i _ _ ℓ _ _ e he ι _ L
  have hp := GlobalTheory.VertProj.isProjOver_strHom_zmod k Y p D hY Z i ℓ
  obtain ⟨T, hT⟩ := exists_functional e fun a : Fin e → ι =>
    (interNum (ZMod ℓ) (structureModule Z) (fun j => (L (a j)).B.pull i) : ℝ) * Real.log ℓ
  refine ⟨T, fun n g hg => ?_⟩
  rw [hg.vertical Z i (ZMod ℓ) e he, Nat.card_zmod, topSelf_comb_pull hp he i L n, hT, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

end GlobalTheory.VertFun
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_height_polynomial_in_degrees : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra (ZMod ℓ) Γ(Z, ⊤)] (e : ℕ), topologicalKrullDim Z = e → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p),
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g →
      g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ e) := by
  first | exact @GlobalTheory.VertFun.exists_vertical_functional | exact GlobalTheory.VertFun.exists_vertical_functional | (intros; apply GlobalTheory.VertFun.exists_vertical_functional <;> assumption)
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.SwapLine

theorem height_comb_horizontal (hC : ArCalc) {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}
    (hY : IsArithVar p D) {Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] {e : ℕ}
    (hc : CharZero Γ(Z, ⊤)) (he : topologicalKrullDim Z = (e + 1 : ℕ)) {ι : Type} [Fintype ι] (L : ι → HermLB p) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g →
      g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ (e + 1)) := by
  have hZ : IsArithVar (i ≫ p) e := hY.of_isClosedImmersion i hc he
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k Z (i ≫ p) e hZ).2 ι (fun j => (L j).restr i)).1
  refine ⟨Ψ, fun n g hg => ?_⟩
  have e₁ : ((comb L n).restr i).Isometric (comb (fun j => (L j).restr i) n) := by
    refine HermLB.icls_eq_iff.1 ?_
    rw [HermLB.icls_pull, icls_comb, icls_comb, map_sum]
    simp only [map_zsmul, ← HermLB.icls_pull]
  exact (e₁.isSelfInter hZ (hg.isSelfInter_restrict hY i rfl)).unique hZ (hΨ.1 n)

def moveExp (n : Fin 5 → ℤ) : Fin 5 → ℤ := ![0, 0, n 2, n 3 + n 0, n 4 + n 1]

theorem aeval_lin_moveExp (n : Fin 5 → ℤ) :
    aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) (lin fun j => (n j : ℝ)) =
      lin fun j => (moveExp n j : ℝ) := by
  simp [lin, Fin.sum_univ_five, moveExp, MvPolynomial.algebraMap_eq]
  ring

theorem sum_moveExp {G : Type*} [AddCommGroup G] (x : Fin 5 → G) (h₀ : x 0 = x 3) (h₁ : x 1 = x 4) (n : Fin 5 → ℤ) :
    ∑ j, n j • x j = ∑ j, moveExp n j • x j := by
  simp [Fin.sum_univ_five, moveExp, add_smul, h₀, h₁]
  try abel

theorem fam5_icls_tens (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B)
    (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2) (A : HermLB q) :
    (fam5 π w H flB fl A 0).icls + (fam5 π w H flB fl A 1).icls =
      (fam5 π w H flB fl A 3).icls + (fam5 π w H flB fl A 4).icls := by
  have a1 := GlobalTheory.T.rank_two_graded_determinant_isometric k Y p _ _ (H.pull π w) fl
  have a2 := VMetric.isometric_det_pull H π w
  have a3 := (GlobalTheory.T.rank_two_graded_determinant_isometric k B q E h H flB).pull π w
  have a4 := HermLB.isometric_pull_tens (VMetric.grLB flB 0 H) (VMetric.grLB flB 1 H) π w
  rw [← HermLB.icls_tens, ← HermLB.icls_tens]
  exact HermLB.icls_eq_iff.2 (a1.trans (a2.trans (a3.symm.trans a4)))

theorem mix_general (hC : ArCalc) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {d : ℕ}
    (hp : IsArithVar p (d + 1)) (L : Fin 5 → HermLB p)
    (hdet : (L 0).icls + (L 1).icls = (L 3).icls + (L 4).icls)
    (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ) (hΦ : IsArFun L (d + 1) Φ)
    (r : ((L 0).dual.tens (L 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((L 0).dual.tens (L 4)).B r)
    (hiso : ∀ z ∈ (((L 0).dual.tens (L 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((L 0).restr i).Isometric ((L 3).restr i))
    (F : MvPolynomial (Fin 5) ℝ) (hF : aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) F = 0)
    (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ) (hFs : F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1)) :
    Φ ((X 4 - X 0) * F) = -∑ n ∈ s, c n * (comb L n).archInt ((L 0).dual.tens (L 4)) (d + 1) hr := by
  have := hp.isLocallyNoetherian
  have := hp.isNoetherian

  let Aex : Option (Fin 5) → Fin 5 → ℤ := fun o => o.elim (Pi.single 4 1 - Pi.single 0 1) fun j => Pi.single j 1
  have hΦ' := ((hC.arIso k Y p (d + 1) hp).2 (Fin 5) L Φ hΦ).2.2 (Option (Fin 5))
    (fun o => o.elim ((L 0).dual.tens (L 4)) L) Aex
    (fun o => by
      cases o with
      | none =>
        refine HermLB.icls_eq_iff.1 ?_
        simp [Aex, icls_comb, HermLB.icls_tens, HermLB.icls_dual, Fin.sum_univ_five, Pi.single_apply]
        done
      | some j => exact isometric_comb_single L j)
  let Φ' := Φ ∘ₗ (aeval fun j => lin fun i => (Aex j i : ℝ) :
    MvPolynomial (Option (Fin 5)) ℝ →ₐ[ℝ] MvPolynomial (Fin 5) ℝ).toLinearMap
  have key (P : MvPolynomial (Fin 5) ℝ) : Φ' (X none * rename some P) = Φ ((X 4 - X 0) * P) := by
    have h1 : (lin fun i => (Aex none i : ℝ)) = X 4 - X 0 := by
      simp [Aex, lin, Fin.sum_univ_five, Pi.single_apply]
      ring
    have h2 : (fun j => lin fun i => (Aex (some j) i : ℝ)) = X := by
      funext j
      simp [Aex, lin, Pi.single_apply]
    simp only [Φ', LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, aeval_X, aeval_rename]
    rw [h1]
    congr 2
    exact (congrArg (fun f => aeval f P) h2).trans (aeval_X_left_apply P)

  have hex (n : Fin 5 → ℤ) : ∃ g : Y → ℝ, (comb L n).IsArithHeight g := (hC.arExists k Y p (d + 1) hp).1 (comb L n)
  choose ht hht using hex
  have hmix (n : Fin 5 → ℤ) := (hC.arMix k Y p (d + 1) hp (Fin 5) _ L Φ' hΦ' n (ht n) (hht n) r hr).2
  have hfin : (Function.support fun z => ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ)).Finite :=
    (((L 0).dual.tens (L 4)).div hr).finite_support_mult.subset fun z hz => by simpa using hz

  have hloc (z : Y) : ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ) * ∑ n ∈ s, c n * ht n z = 0 := by
    by_cases hz0 : (((L 0).dual.tens (L 4)).div hr).mult z = 0
    · simp [hz0]
    have hz1 : Order.coheight z = 1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz0
    have hzs : z ∈ (((L 0).dual.tens (L 4)).div hr).supp := CartierDiv.mem_supp_of_mult_ne_zero hz0
    obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    have e03 : ((L 0).restr i).Isometric ((L 3).restr i) := hiso _ hzs Z i rfl
    have e14 : ((L 1).restr i).icls = ((L 4).restr i).icls := by
      have h₁ := congrArg (HermLB.IsomClass.pull i rfl) hdet
      rw [map_add, map_add, ← HermLB.icls_pull, ← HermLB.icls_pull, ← HermLB.icls_pull, ← HermLB.icls_pull,
        HermLB.icls_eq_iff.2 e03] at h₁
      exact add_left_cancel h₁
    have hdim : topologicalKrullDim Z = (d + 1 : ℕ) := GlobalTheory.T.arithmetic_variety_divisor_dimension k Y p (d + 1) hp Z i hz1
    obtain ⟨T, hT⟩ : ∃ T : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ, ∀ (n : Fin 5 → ℤ) (g : Y → ℝ),
        (comb L n).IsArithHeight g → g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ (d + 1)) := by
      rcases hp.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arithmetic_height_polynomial_in_degrees k Y p (d + 1) hp Z i ℓ (d + 1) hdim (Fin 5) L
      · have he' : e + 1 = d + 1 := by
          have := he.symm.trans hdim
          exact_mod_cast this
        obtain ⟨T, hT⟩ := height_comb_horizontal hC hp i hc he L
        exact ⟨T, fun n g hg => (hT n g hg).trans (by rw [he'])⟩
    have hmove (n : Fin 5 → ℤ) : ((comb L n).restr i).Isometric ((comb L (moveExp n)).restr i) := by
      refine HermLB.icls_eq_iff.1 ?_
      rw [HermLB.icls_pull, HermLB.icls_pull, icls_comb, icls_comb, map_sum, map_sum]
      simp only [map_zsmul]
      exact sum_moveExp (fun j => HermLB.IsomClass.pull i rfl (L j).icls) (HermLB.icls_eq_iff.2 e03) e14 n
    have hsum : ∑ n ∈ s, c n * ht n (i (genericPoint Z)) = T (aeval (![X 3, X 4, X 2, X 3, X 4] :
        Fin 5 → MvPolynomial (Fin 5) ℝ) F) := by
      rw [hFs, map_sum, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, map_pow, aeval_lin_moveExp, map_smul, smul_eq_mul,
        GlobalTheory.AdjFlag.height_eq hp (hht n) (hht (moveExp n)) i (hmove n), hT _ _ (hht (moveExp n))]
    rw [hsum, hF, map_zero, mul_zero]

  have e₁ : Φ ((X 4 - X 0) * F) = ∑ n ∈ s, c n * Φ' (X none * rename some (lin fun i => (n i : ℝ)) ^ (d + 1)) := by
    rw [hFs, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, ← map_pow, key]
  have e₂ : ∑ n ∈ s, c n * ∑ᶠ z, ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ) * ht n z = 0 := by
    have hf (n : Fin 5 → ℤ) :
        (Function.support fun z => ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ) * ht n z).Finite :=
      hfin.subset (Function.support_mul_subset_left _ _)
    simp_rw [mul_finsum]
    rw [← finsum_sum_comm s _ fun n _ => (hf n).subset (Function.support_mul_subset_right _ _)]
    refine finsum_eq_zero_of_forall_eq_zero fun z => ?_
    rw [← hloc z, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e₁]
  simp_rw [hmix, mul_sub]
  rw [Finset.sum_sub_distrib, e₂, zero_sub]

theorem mix_dualTaut_tens_quotBase : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y]
    (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (w : π ≫ q = p)
    (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)
    (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ), IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ)
      (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ z ∈ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((fam5 π w H flB fl A 0).restr i).Isometric ((fam5 π w H flB fl A 3).restr i)) →
      ∀ F : MvPolynomial (Fin 5) ℝ, aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) F = 0 →
      ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
        Φ ((X 4 - X 0) * F) = -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt
          ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr := by
  intro hC k _ B Y _ _ q p d _ hp π w E h H flB fl A Φ hΦ r hr hiso F hF s c hFs
  exact mix_general hC hp (fam5 π w H flB fl A) (fam5_icls_tens k B Y q p π w E h H flB fl A) Φ hΦ r hr hiso F hF s c hFs

end GlobalTheory.CovTest.SwapLine

end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_function_swap_line_family : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules)
    (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)
    (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ), IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ)
      (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ z ∈ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((fam5 π w H flB fl A 0).restr i).Isometric ((fam5 π w H flB fl A 3).restr i)) →
      ∀ F : MvPolynomial (Fin 5) ℝ, aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) F = 0 →
      ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
        Φ ((X 4 - X 0) * F) = -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt
          ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr := by
  atlas_forward_decl GlobalTheory.CovTest.SwapLine.mix_dualTaut_tens_quotBase
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

private theorem isIso_of_sameStep {B Y : Scheme.{0}} (π : Y ⟶ B) (E : B.Modules) (n : ℕ) (flB : Vert.Flag E n)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (hF : IsFlagBundle π (fun _ : Unit => E) (fun _ => n) (fun _ => fl))
    (hs : ∀ i, fl.SameStep (flB.pull π) i) : IsIso π := by
  have key (T : Scheme.{0}) (g : T ⟶ B) (a : T ⟶ Y) (w : a ≫ π = g) (i : Fin (n + 1)) :
      ∃ e : (Scheme.Modules.pullback a).obj (fl.F i) ≅ (flB.pull g).F i,
        e.hom ≫ (flB.pull g).ι i = (Scheme.Modules.pullback a).map (fl.ι i) ≫
          (Scheme.Modules.pullbackComp a π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
    obtain ⟨e, he⟩ := hs i
    refine ⟨(Scheme.Modules.pullback a).mapIso e ≪≫ (Scheme.Modules.pullbackComp a π).app (flB.F i) ≪≫
      (Scheme.Modules.pullbackCongr w).app (flB.F i), ?_⟩
    have n₁ := (Scheme.Modules.pullbackComp a π).hom.naturality (flB.ι i)
    have n₂ := (Scheme.Modules.pullbackCongr w).hom.naturality (flB.ι i)
    rw [← he, Functor.map_comp, Category.assoc]
    refine (Category.assoc _ _ _).trans (congrArg _ ?_)
    refine Eq.trans ?_ ((congrArg (· ≫ (Scheme.Modules.pullbackCongr w).hom.app E) n₁).symm.trans (Category.assoc _ _ _))
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    exact congrArg _ n₂.symm
  have : Mono π := ⟨fun {T} a b hab => (hF T (b ≫ π) fun _ => flB.pull _).unique
    ⟨hab, fun _ i => key T _ a hab i⟩ ⟨rfl, fun _ i => key T _ b rfl i⟩⟩
  obtain ⟨s, ⟨hs, -⟩, -⟩ := hF B (𝟙 B) fun _ => flB.pull _
  have : IsSplitEpi π := ⟨⟨⟨s, hs⟩⟩⟩
  exact isIso_of_mono_of_isSplitEpi π

private theorem isometric_first {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules}
    {h : VMetric p E 2} (H : h.IsCInf) (fl : Vert.Flag E 2) :
    (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))).Isometric (VMetric.grLB fl 0 H) := by
  have H₀ : (h.stepMet fl 0).IsCInf := H.restrict _ _
  have hS₀ := VMetric.stepSeq_shortExact fl 0
  have i₂ : IsIso (VMetric.stepSeq fl 0).g :=
    hS₀.isIso_g_iff.2 (VB.isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  exact T.det_metric_isometric_of_isometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) H₀
      (H.grMet fl 0) (asIso (VMetric.stepSeq fl 0).g) ((VMetric.isIsometry_iff _).2 (VMetric.ext
        (funext fun σ => ChTwoModel.quot_eq_map ((h.stepMet fl 0).met σ) hS₀
          (fl.isVB (Fin.castSucc 0)) _)))

private theorem exists_ratSec_lines {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {V L Q L' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0} {l' : L' ⟶ V}
    (hS : (ShortComplex.mk l m w).ShortExact) (hL : VB.IsVB L 1) (hQ : VB.IsVB Q 1) (hL' : VB.IsVB L' 1)
    (hl : VB.IsSubbundle l) (hl' : VB.IsSubbundle l') {h : VMetric p V (1 + 1)} (H : h.IsCInf) (hs : l' ≫ m ≠ 0)
    {S M N : HermLB p} (e₂ : (VMetric.det (H.restrict hl' hL')).Isometric S)
    (e₃ : (VMetric.det (H.restrict hl hL)).Isometric M)
    (e₁ : (VMetric.det (VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H)).Isometric N) :
    ∃ (r : (S.dual.tens N).B.ι → X.functionFieldˣ) (hr : IsRatSec (S.dual.tens N).B r),
      (∀ z ∈ ((S.dual.tens N).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsIntegral Z], i (genericPoint Z) = z →
          (S.restr i).Isometric (M.restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq (h.met σ) l' l v ∧
        ∀ y ∈ offSupp p σ ((S.dual.tens N).div hr), v y < 1 ∧
          logNorm ((S.dual.tens N).φ σ) r y = Real.log (1 - v y) / 2 := by
  have HQ := VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H
  obtain ⟨r, hr, hv, hn⟩ := T.exists_ratSec_det_dual_tensor_support k X p L' Q (h.restrict hl' hL')
    (VMetric.quot (S := .mk l m w) h hS hL hQ) (H.restrict hl' hL') HQ (l' ≫ m) hs
  obtain ⟨r', hr', hd, hN⟩ := (e₂.dual.tens e₁).exists_isRatSec hr
  refine ⟨r', hr', ?_, fun σ => ?_⟩
  · rw [hd]
    rintro z hz Z i _ rfl
    exact ((e₂.pull i rfl).symm.trans
      (T.det_metric_restriction_vanishing_locus k X p V L Q L' l m w l' hS hQ hL hL' hl hl' h H Z i (hv _ hz)).symm).trans (e₃.pull i rfl)
  · obtain ⟨v, hc, -, -⟩ := T.exists_continuous_cosSq_angle_function k X p σ V L L' _ (h.met σ) l l' (H σ) hl hl' hL hL'
    refine ⟨v, hc.symm, ?_⟩
    rw [hd]
    intro y hy
    obtain ⟨U, t, t', ht, ht', hU⟩ := AdjFlag.exists_frames hL hL' y
    obtain ⟨n₁, n₂⟩ := hn σ y hy U t' ht' hU
    have e := AdjFlag.div_eq_one_sub hS hL hQ hL' hl hl' (h.met σ) hc ht ht' hU
    have := div_pos n₁ (AdjFlag.form_frame_pos ((h.met σ).restrict hl' hL') ht' hU)
    have h₁ : 0 < 1 - v y := this.trans_eq e
    exact ⟨by linarith, (hN σ hy).trans (n₂.trans (congrArg (Real.log · / 2) e))⟩

private theorem isometric_second {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules}
    {h : VMetric p E (1 + 1)} (H : h.IsCInf) (fl : Vert.Flag E 2) {Q : X.Modules} {m : E ⟶ Q} {w : fl.ι 1 ≫ m = 0}
    (hS : (ShortComplex.mk (fl.ι 1) m w).ShortExact) (hL : VB.IsVB (fl.F 1) 1) (hQ : VB.IsVB Q 1) :
    (VMetric.det (VMetric.IsCInf.quot (S := .mk (fl.ι 1) m w) hS hL hQ H)).Isometric (VMetric.grLB fl 1 H) := by
  have i₁ : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  have H₁ : (h.stepMet fl 1).IsCInf := H.restrict _ _
  have hI : (h.stepMet fl 1).IsIsometry h (asIso (fl.ι (Fin.succ 1))) := fun σ V s t y hy =>
    ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm
  have he : (Iso.refl (fl.F 1)).hom ≫ fl.ι 1 = (VMetric.stepSeq fl 1).f ≫ (asIso (fl.ι (Fin.succ 1))).hom :=
    (Category.id_comp _).trans (fl.step_ι 1).symm
  have e := T.det_metric_shortExact_iso_isometric k X p (VMetric.stepSeq fl 1) (.mk (fl.ι 1) m w) 1 1 (h.stepMet fl 1) h H₁ H
      (VMetric.stepSeq_shortExact fl 1) hS (fl.isVB (Fin.castSucc 1)) (fl.isVB_gr 1) hL hQ
      (Iso.refl (fl.F 1)) (asIso (fl.ι (Fin.succ 1))) he hI
  exact e.1.symm

private theorem exists_ratSec_flags {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {V : X.Modules} {h : VMetric p V 2} (H : h.IsCInf) (fl fl' : Vert.Flag V 2) (hne : ¬ fl.SameStep fl' 1)
    {M Q : HermLB p} (hM : (VMetric.grLB fl' 0 H).Isometric M) (hQ : (VMetric.grLB fl' 1 H).Isometric Q) :
    ∃ (r : ((VMetric.grLB fl 0 H).dual.tens Q).B.ι → X.functionFieldˣ)
      (hr : IsRatSec ((VMetric.grLB fl 0 H).dual.tens Q).B r),
      (∀ z ∈ (((VMetric.grLB fl 0 H).dual.tens Q).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsIntegral Z], i (genericPoint Z) = z →
          ((VMetric.grLB fl 0 H).restr i).Isometric (M.restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq (h.met σ) (fl.ι 1) (fl'.ι 1) v ∧
        ∀ y ∈ offSupp p σ (((VMetric.grLB fl 0 H).dual.tens Q).div hr), v y < 1 ∧
          logNorm (((VMetric.grLB fl 0 H).dual.tens Q).φ σ) r y = Real.log (1 - v y) / 2 := by
  have hL : VB.IsVB (fl'.F 1) 1 := fl'.isVB 1
  have hL' : VB.IsVB (fl.F 1) 1 := fl.isVB 1
  have hl := fl'.isSubbundle 1
  have hl' := fl.isSubbundle 1
  have hC : VB.IsVB (Limits.cokernel (fl'.ι 1)) 1 := fl'.isVB_cokernel 1
  have hC' : VB.IsVB (Limits.cokernel (fl.ι 1)) 1 := fl.isVB_cokernel 1
  have hS : (ShortComplex.mk (fl'.ι 1) _ (Limits.cokernel.condition (fl'.ι 1))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hS' : (ShortComplex.mk (fl.ι 1) _ (Limits.cokernel.condition (fl.ι 1))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hs : fl.ι 1 ≫ Limits.cokernel.π (fl'.ι 1) ≠ 0 := fun hs =>
    hne (T.iso_of_equal_sublines_shortExact X V _ _ _ _ _ _ _ _ _ _ hS hS' hC hC' hs)
  exact exists_ratSec_lines hS hL hC hL' hl hl' (h := h) H hs (isometric_first H fl)
    ((isometric_first H fl').trans hM) ((isometric_second H fl' hS hL hC).trans hQ)

theorem _root_.GlobalTheory.T.rank_two_flag_rational_sections : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q),
    ∃ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ z ∈ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((fam5 π w H flB fl A 0).restr i).Isometric ((fam5 π w H flB fl A 3).restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v ∧
        ∀ y ∈ offSupp p σ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr), v y < 1 ∧ logNorm (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).φ σ) r y = Real.log (1 - v y) / 2 := by
  intro k _ B Y _ _ q p d hB hY _ π w E h H flB fl hF A
  have hne : ¬ fl.SameStep (flB.pull π) 1 := fun h₁ => by
    have : IsIso π := isIso_of_sameStep π E 2 flB fl hF fun i => by
      fin_cases i
      exacts [AdjFlag.sameStep_of_end (Or.inl rfl), h₁, AdjFlag.sameStep_of_end (Or.inr rfl)]
    have e := IsHomeomorph.topologicalKrullDim_eq _ π.homeomorph.isHomeomorph
    rw [hB.dim_eq, hY.dim_eq] at e
    have e' : d + 1 + 1 = d + 1 := by exact_mod_cast e
    omega
  obtain ⟨r, hr, h₁, h₂⟩ := exists_ratSec_flags (H.pull π w) fl (flB.pull π) hne
    (VMetric.isometric_grLB_pull k B Y q p E 2 h H flB π w 0) (VMetric.isometric_grLB_pull k B Y q p E 2 h H flB π w 1)
  exact ⟨r, hr, fun z hz Z i _ _ hi => h₁ z hz Z i hi, h₂⟩
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.IntLinPow

theorem homog_eq_sum_pow_intLin : ∀ (D : ℕ) (F : MvPolynomial (Fin 5) ℝ), F.IsHomogeneous D →
    ∃ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D := by
  intro D F hF
  have hmem : F ∈ Submodule.span ℝ (Set.range fun n : Fin 5 → ℤ => lin (fun i => (n i : ℝ)) ^ D) := by
    by_contra hnot
    obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hkill : ∀ n : Fin 5 → ℤ, φ (lin (fun i => (n i : ℝ)) ^ D) = 0 := by
      intro n
      have hm : lin (fun i => (n i : ℝ)) ^ D ∈ Submodule.span ℝ
          (Set.range fun n : Fin 5 → ℤ => lin (fun i => (n i : ℝ)) ^ D) := Submodule.subset_span ⟨n, rfl⟩
      have h2 : φ (lin (fun i => (n i : ℝ)) ^ D) ∈ (Submodule.span ℝ
          (Set.range fun n : Fin 5 → ℤ => lin (fun i => (n i : ℝ)) ^ D)).map φ := Submodule.mem_map_of_mem hm
      rw [hφ] at h2
      exact (Submodule.mem_bot ℝ).mp h2
    have hP : PowLinSpan.polOf φ D = 0 := by
      refine eq_zero_of_eval_zero_at_prod_finset (PowLinSpan.polOf φ D)
        (fun _ => (Finset.range (D + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
      · intro x
        rw [Finset.card_image_of_injective _ Nat.cast_injective]
        simpa using Nat.lt_succ_of_le (PowLinSpan.degreeOf_polOf_le φ D x)
      · intro v hv
        have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
          intro i
          obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
          exact ⟨k, hk⟩
        choose k hk using hv'
        rw [PowLinSpan.eval_polOf]
        have h := hkill (fun i => (k i : ℤ))
        have he : (∑ x, C (v x) * X x : MvPolynomial (Fin 5) ℝ) = lin (fun i => (((k i : ℤ)) : ℝ)) := by
          simp only [lin, Int.cast_natCast, hk]
        rw [he]
        exact h
    exact hφF (PowLinSpan.homog_kill φ D hP F hF)
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  refine ⟨c.support, c, ?_⟩
  rw [← hc, Finsupp.sum]

end GlobalTheory.IntLinPow
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_form_powers_linear : ∀ (D : ℕ) (F : MvPolynomial (Fin 5) ℝ), F.IsHomogeneous D →
    ∃ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D := by
  first | exact @GlobalTheory.IntLinPow.homog_eq_sum_pow_intLin | exact GlobalTheory.IntLinPow.homog_eq_sum_pow_intLin | (intros; apply GlobalTheory.IntLinPow.homog_eq_sum_pow_intLin <;> assumption)
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.SwapLine

theorem core_exists : ArCalc → ∃ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, Homog G ∧
    ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ a b : ℤ, Φ (onLine d a b - onBase d a b) = Ψ (G (d + 1) a b) := by
  intro hC
  obtain ⟨G, hG, hAn⟩ := GlobalTheory.T.flag_bundle_pullback_height_compare hC
  refine ⟨G, hG, ?_⟩
  intro k _ B Y _ _ q p d hq hp hreg π w E h H flB fl hfl A Φ Ψ hΦ hΨ a b
  obtain ⟨K, hKh, hK⟩ := GlobalTheory.T.homogeneous_line_base_difference d a b
  have hF : onLine d a b - onBase d a b = (X 4 - X 0) * ((X 3 - X 0) * K) := by rw [hK]; ring
  have hFv : aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) ((X 3 - X 0) * K) = 0 := by
    simp
  have hFh : ((X 3 - X 0) * K : MvPolynomial (Fin 5) ℝ).IsHomogeneous (d + 1) := by
    have h1 : (X 3 - X 0 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
      (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
    simpa [add_comm] using h1.mul hKh
  obtain ⟨r, hr, hsupp, hnorm⟩ := GlobalTheory.T.rank_two_flag_rational_sections k B Y q p d hq hp hreg π w E h H flB fl hfl A
  obtain ⟨s, c, hpol⟩ := GlobalTheory.T.homogeneous_form_powers_linear (d + 1) _ hFh
  rw [hF, GlobalTheory.T.arithmetic_function_swap_line_family hC k B Y q p d hq hp π w E h H flB fl A Φ hΦ r hr hsupp _ hFv s c hpol]
  exact hAn k B Y q p d hq hp hreg π w E h H flB fl hfl A Ψ hΨ r hr hnorm a b _ hF.symm s c hpol

end GlobalTheory.CovTest.SwapLine

end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_base_rank_two_metric_family : ArCalc → ∃ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, Homog G ∧
    ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ a b : ℤ, Φ (onLine d a b - onBase d a b) = Ψ (G (d + 1) a b) := by
  atlas_forward_decl GlobalTheory.CovTest.SwapLine.core_exists
end

section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

theorem swapReg_exists : ArCalc → ∃ G, Homog G ∧ SwapReg G := by
  intro hC
  obtain ⟨G, hG, hcore⟩ := GlobalTheory.T.regular_base_rank_two_metric_family hC
  refine ⟨G, hG, ?_⟩
  intro k _ B Y _ _ q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ a b
  obtain ⟨flB⟩ := hflB
  set L5 := fam5 π w H flB fl A with hL5
  obtain ⟨Φ5, hΦ5⟩ := ((hC.arExists k Y p (d + 1) hp).2 (Fin 5) L5).1

  have e3 := GlobalTheory.VertForm.FormEx.arFun_eq_rename hC hp hΦ hΦ5 ![0, 1, 2] (fun i => by fin_cases i <;> rfl)

  have iso : ((L5 0).tens (L5 1)).Isometric ((L5 3).tens (L5 4)) := by
    have e₁ := GlobalTheory.T.rank_two_graded_determinant_isometric k Y p _ _ (H.pull π w) fl
    have e₂ := VMetric.isometric_det_pull H π w
    have e₃ := ((GlobalTheory.T.rank_two_graded_determinant_isometric k B q E h H flB).symm.pull π w).trans (HermLB.isometric_pull_tens _ _ π w)
    exact e₁.trans (e₂.trans e₃)
  have icl : (L5 1).icls = (L5 3).icls + (L5 4).icls - (L5 0).icls := by
    have := HermLB.icls_eq_iff.2 iso
    rw [HermLB.icls_tens, HermLB.icls_tens] at this
    rw [← this]
    abel

  let T : Fin 5 → Fin 5 → ℤ := fun j => if j = 1 then ![-1, 0, 0, 1, 1] else Pi.single j 1
  have hT : ∀ j, (comb L5 (T j)).Isometric (L5 j) := by
    intro j
    by_cases hj : j = 1
    · subst hj
      refine HermLB.icls_eq_iff.1 ?_
      rw [icls_comb, icl]
      simp [T, Fin.sum_univ_five]
      abel
    · simp only [T, hj, if_false]
      exact isometric_comb_single L5 j
  have hsub := ((hC.arIso k Y p (d + 1) hp).2 (Fin 5) L5 Φ5 hΦ5).2.2 (Fin 5) L5 T hT
  have e5 := GlobalTheory.ArInt.Model.isArFun_unique hp hΦ5 hsub
  have eline : Φ (lin ![(a : ℝ), b, 1] ^ (d + 2)) + Φ (lin ![(b : ℝ), a, 1] ^ (d + 2)) = Φ5 (onLine d a b) := by
    rw [← map_add, e3, LinearMap.comp_apply, AlgHom.toLinearMap_apply, e5, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    change Φ5 (aeval _ (rename _ (swapSum d a b))) = _
    rw [onLine, aeval_rename]
    congr 2
    congr 1
    funext i
    fin_cases i <;> simp [T, lin, Fin.sum_univ_five, Pi.single_apply] <;> ring

  have hdim : topologicalKrullDim (closure ({π (genericPoint Y)} : Set B)) < ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    refine (topologicalKrullDim_subspace_le B _).trans_lt ?_
    rw [hq.dim_eq]
    exact_mod_cast Nat.lt_succ_self (d + 1)
  let LB3 : Fin 3 → HermLB q := ![VMetric.grLB flB 1 H, VMetric.grLB flB 0 H, A]
  let L3 : Fin 3 → HermLB p := fun i => (LB3 i).pull π w
  obtain ⟨Φ3, hΦ3⟩ := ((hC.arExists k Y p (d + 1) hp).2 (Fin 3) L3).1
  have z3 : IsArFun L3 (d + 1) 0 := by
    refine ⟨fun n => ?_, fun _ _ _ _ => rfl⟩
    rw [LinearMap.zero_apply]
    exact (isometric_comb_pull LB3 n π w).symm.isSelfInter hp
      (GlobalTheory.ProjDrop.isSelfInter_zero_of_dim_lt hC k B Y q p d (d + 1) hq hp π w hdim (comb LB3 n))
  have e3' := GlobalTheory.VertForm.FormEx.arFun_eq_rename hC hp hΦ3 hΦ5 ![4, 3, 2] (fun i => by fin_cases i <;> rfl)
  have ebase : Φ5 (onBase d a b) = 0 := by
    have h0 := GlobalTheory.ArInt.Model.isArFun_unique hp hΦ3 z3
    have : onBase d a b = rename ![(4 : Fin 5), 3, 2] (swapSum d a b) := by
      rw [onBase, ← aeval_X_left_apply (rename _ _), aeval_rename]
      congr 2
      funext i
      fin_cases i <;> rfl
    rw [this, ← AlgHom.toLinearMap_apply, ← LinearMap.comp_apply, ← e3', h0, LinearMap.zero_apply]

  rw [eline, show onLine d a b = onBase d a b + (onLine d a b - onBase d a b) by ring, map_add, ebase, zero_add]
  exact hcore k B Y q p d hq hp hreg π w E h H flB fl hfl A Φ5 Ψ hΦ5 hΨ a b

end GlobalTheory.CovTest.SwapLine

end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_swap_regular : ArCalc → ∃ G, Homog G ∧ SwapReg G := by
  atlas_forward_decl GlobalTheory.CovTest.SwapLine.swapReg_exists
end
