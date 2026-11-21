import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocalIntegralOfSubstitution
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.ExistsLatticeAutomorphismApprox
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.DedekindLFunctions
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGen

section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Ball

variable {K : Type*} [Field K] [ValuativeRel K]

def InBall (c x : K) : Prop := ValuativeRel.valuation K x ≤ ValuativeRel.valuation K c

def ballS (c : K) : AddSubgroup K where
  carrier := {x | InBall c x}
  zero_mem' := by simp [InBall]
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, InBall] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq, InBall] at hx ⊢
    simpa [Valuation.map_neg] using hx

theorem mem_ballS {c x : K} : x ∈ ballS c ↔ valuation K x ≤ valuation K c := by
  show InBall c x ↔ _
  rfl

theorem ballS_isOpen [TopologicalSpace K] [IsValuativeTopology K] {c : K} (hc : c ≠ 0) :
    IsOpen (ballS c : Set K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hv : valuation K c ≠ 0 := by simpa using hc
  refine IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hv, fun y hy => ?_⟩
  have hy' : valuation K (y - x) < valuation K c := by simpa using hy
  rw [SetLike.mem_coe, mem_ballS]
  have e : y = (y - x) + x := by ring
  rw [e]
  exact Valuation.map_add_le _ hy'.le hx

theorem ballS_mul {c x : K} (hc : c ≠ 0) (hx : x ∈ ballS c) : ∃ β ∈ 𝒪[K], x = c * β := by
  refine ⟨x / c, ?_, by field_simp⟩
  rw [Valuation.mem_integer_iff, map_div₀]
  exact div_le_one_of_le₀ (mem_ballS.1 hx) zero_le'

end Ball

section Ad

open Formalism.MainNotions.S.Loc PI.StrongApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)

theorem sa_lat (T : Finset (HeightOneSpectrum (𝓞 F))) (x : ∀ p, (L p).Ep) (c : ∀ p, (L p).Fp)
    (hc : ∀ p ∈ T, c p ≠ 0) :
    ∃ t : E, (∀ p ∈ T, ∃ y ∈ (L p).O, (L p).ιE t - x p = algebraMap (L p).Fp (L p).Ep (c p) * y) ∧
      ∀ p, p ∉ T → (L p).ιE t ∈ (L p).O := by
  classical
  obtain ⟨n, b, hbint, hbspan⟩ := intSpan' F E
  choose α hα using fun p => local_span_holds F E sig p (L p) n b hbspan (x p)
  set c' : ∀ p, (L p).Fp := fun p => if p ∈ T then c p else 1 with hc'
  have hc'0 : ∀ p, c' p ≠ 0 := by
    intro p
    by_cases hp : p ∈ T
    · simp only [hc', if_pos hp]; exact hc p hp
    · simp only [hc', if_neg hp]; exact one_ne_zero
  have hVo : ∀ p, IsOpen (ballS (c' p) : Set (L p).Fp) := by
    intro p
    have := (L p).lf
    exact ballS_isOpen (hc'0 p)
  choose a ha using fun p (i : Fin n) => local_dense_embedding F E sig p (L p) (ballS (c' p)) (hVo p) (α p i)
  choose d hd0 hd using fun p => local_neighbourhood_small F E sig p (L p) (ballS (c' p)) (hVo p)
  choose t ht1 ht2 using fun i : Fin n => strong_approximation_finite_places F T (fun p => a p i) d (fun p _ => hd0 p)
  refine ⟨∑ i, t i • b i, fun p hp => ?_, fun p hp => ?_⟩
  · have hιE : (L p).ιE (∑ i, t i • b i) = ∑ i, (L p).ιF (t i) • (L p).ιE (b i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)
    have h1 : (L p).ιE (∑ i, t i • b i) - x p = ∑ i, ((L p).ιF (t i) - α p i) • (L p).ιE (b i) := by
      rw [hιE]
      conv_lhs => rw [hα p]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    have hmem : ∀ i, (L p).ιF (t i) - α p i ∈ ballS (c' p) := by
      intro i
      have h2 : (L p).ιF (t i) - α p i = (L p).ιF (t i - a p i) + ((L p).ιF (a p i) - α p i) := by
        rw [map_sub]; ring
      rw [h2]
      exact (ballS (c' p)).add_mem (hd p _ (ht1 i p hp)) (ha p i)
    have hcp : c' p = c p := by simp only [hc', if_pos hp]
    choose β hβO hβ using fun i => ballS_mul (hc'0 p) (hmem i)
    have hbO : ∀ i, (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := local_integral_of_substitution F E sig p (L p) 1 (b i) (by simp) (hbint i)
      simpa using this
    have hβE : ∀ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := (L p).lf
      have hA : IsIntegral 𝒪[(L p).Fp] (algebraMap (L p).Fp (L p).Ep (β i)) :=
        isIntegral_algebraMap (R := 𝒪[(L p).Fp]) (A := (L p).Ep) (x := ⟨β i, hβO i⟩)
      exact (L p).O.mul_mem (((L p).O_def _).mpr hA) (hbO i)
    refine ⟨∑ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i), (L p).O.sum_mem fun i _ => hβE i, ?_⟩
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ i, ← hcp, Algebra.smul_def, map_mul, mul_assoc]
  · rw [map_sum]
    refine (L p).O.sum_mem fun i _ => ?_
    rw [existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)]
    exact local_integral_of_substitution F E sig p (L p) (t i) (b i) (ht2 i p hp) (hbint i)

end Ad

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Loc

open Formalism.MainNotions.S.Loc PI.StrongApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} (L : LocAt F E sig p)

def latS (c : L.Fp) : AddSubgroup L.Ep where
  carrier := {x | ∃ y ∈ L.O, x = algebraMap L.Fp L.Ep c * y}
  zero_mem' := ⟨0, L.O.zero_mem, by simp⟩
  add_mem' := by
    rintro x x' ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', L.O.add_mem hy hy', by ring⟩
  neg_mem' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, L.O.neg_mem hy, by ring⟩

variable {L}

theorem mem_latS {c : L.Fp} {x : L.Ep} : x ∈ latS L c ↔ ∃ y ∈ L.O, x = algebraMap L.Fp L.Ep c * y := Iff.rfl

theorem alg_mem_O {s : L.Fp} (hs : s ∈ 𝒪[L.Fp]) : algebraMap L.Fp L.Ep s ∈ L.O := by
  refine (L.O_def _).mpr ?_
  first
  | exact isIntegral_algebraMap (x := (⟨s, hs⟩ : 𝒪[L.Fp]))
  | exact (IsScalarTower.algebraMap_apply (𝒪[L.Fp]) L.Fp L.Ep ⟨s, hs⟩) ▸ isIntegral_algebraMap

theorem latS_mul {c c' : L.Fp} {x y : L.Ep} (hx : x ∈ latS L c) (hy : y ∈ latS L c') : x * y ∈ latS L (c * c') := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, L.O.mul_mem ha hb, by rw [map_mul]; ring⟩

theorem O_mul_latS {c : L.Fp} {x y : L.Ep} (hy : y ∈ L.O) (hx : x ∈ latS L c) : y * x ∈ latS L c := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨y * a, L.O.mul_mem hy ha, by ring⟩

theorem latS_mono {c c' : L.Fp} (hc' : c' ∈ 𝒪[L.Fp]) {x : L.Ep} (hx : x ∈ latS L (c * c')) : x ∈ latS L c := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨algebraMap L.Fp L.Ep c' * a, L.O.mul_mem (alg_mem_O hc') ha, by rw [map_mul]; ring⟩

theorem bounded_Fp (a : L.Fp) : ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ s * a ∈ 𝒪[L.Fp] := by
  by_cases ha : a ∈ 𝒪[L.Fp]
  · exact ⟨1, one_ne_zero, one_mem _, by rw [one_mul]; exact ha⟩
  · have h0 : a ≠ 0 := by
      rintro rfl
      exact ha (zero_mem _)
    refine ⟨a⁻¹, inv_ne_zero h0, ?_, by rw [inv_mul_cancel₀ h0]; exact one_mem _⟩
    rw [Valuation.mem_integer_iff] at ha ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))

theorem bounded (x : L.Ep) : ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ algebraMap L.Fp L.Ep s * x ∈ L.O := by
  classical
  obtain ⟨n, b, hbint, hbspan⟩ := intSpan' F E
  obtain ⟨α, hα⟩ := local_span_holds F E sig p L n b hbspan x
  choose s hs0 hsO hsa using fun i => bounded_Fp (L := L) (α i)
  have hbO : ∀ i, L.ιE (b i) ∈ L.O := by
    intro i
    have := local_integral_of_substitution F E sig p L 1 (b i) (by simp) (hbint i)
    simpa using this
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, Subring.prod_mem _ fun i _ => hsO i, ?_⟩
  rw [hα, Finset.mul_sum]
  refine L.O.sum_mem fun i _ => ?_
  have e : algebraMap L.Fp L.Ep (∏ j, s j) * (α i • L.ιE (b i)) =
      algebraMap L.Fp L.Ep ((∏ j ∈ Finset.univ.erase i, s j) * (s i * α i)) * L.ιE (b i) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    ring_nf
  rw [e]
  exact L.O.mul_mem (alg_mem_O (Subring.mul_mem _ (Subring.prod_mem _ fun j _ => hsO j) (hsa i))) (hbO i)

theorem bounded_mat {n : ℕ} (B : Matrix (Fin n) (Fin n) L.Ep) :
    ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O := by
  choose s hs0 hsO hsB using fun (p : Fin n × Fin n) => bounded (B p.1 p.2)
  refine ⟨∏ p, s p, Finset.prod_ne_zero_iff.mpr fun p _ => hs0 p, prod_mem fun p _ => hsO p, ?_⟩
  intro i j
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ (i, j)), map_mul, mul_comm (algebraMap L.Fp L.Ep (s (i, j))), mul_assoc]
  exact L.O.mul_mem (alg_mem_O (prod_mem fun p _ => hsO p)) (hsB (i, j))

theorem entIn_mul_left {n : ℕ} {B : Matrix (Fin n) (Fin n) L.Ep} {s : L.Fp}
    (hs : ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O) {c : L.Fp} {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L (s * c)) X) : EntIn (latS L c) (B * X) := by
  intro i j
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  obtain ⟨y, hy, hxy⟩ := hX k j
  refine ⟨algebraMap L.Fp L.Ep s * B i k * y, L.O.mul_mem (hs i k) hy, ?_⟩
  rw [hxy, map_mul]
  ring

theorem entIn_mul_right {n : ℕ} {B : Matrix (Fin n) (Fin n) L.Ep} {s : L.Fp}
    (hs : ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O) {c : L.Fp} {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L (s * c)) X) : EntIn (latS L c) (X * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  obtain ⟨y, hy, hxy⟩ := hX i k
  refine ⟨algebraMap L.Fp L.Ep s * B k j * y, L.O.mul_mem (hs k j) hy, ?_⟩
  rw [hxy, map_mul]
  ring

theorem latS_mul_self {c : L.Fp} (hc : c ∈ 𝒪[L.Fp]) {x y : L.Ep} (hx : x ∈ latS L c) (hy : y ∈ latS L c) :
    x * y ∈ latS L c := latS_mono hc (latS_mul hx hy)

end Loc

end Formalism.L2.SG.Pf.ProdEApprox
end
end
