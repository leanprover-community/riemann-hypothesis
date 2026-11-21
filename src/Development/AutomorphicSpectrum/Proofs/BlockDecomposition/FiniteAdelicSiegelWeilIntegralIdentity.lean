import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDelta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLattice
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolution
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBound
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfPowNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLocalOrbitalIntegralBounded

section
open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem integrable_of_summable_quotient_periodic :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by
  intro G H _ _ _ _ _ _ _ ν _ U hUo hUc ι hι f hf hs
  let r : H ⧸ U.comap ι → G := fun x => ι (Quotient.out x)
  let c : H ⧸ U.comap ι → Set G := fun x => (fun g => g - r x) ⁻¹' (U : Set G)
  have hcopen : ∀ x, IsOpen (c x) := fun x => hUo.preimage (by fun_prop)
  have hcov : ⋃ x, c x = univ := by
    refine eq_univ_of_forall fun g => mem_iUnion.2 ?_
    obtain ⟨h, hh⟩ := hι g
    refine ⟨(QuotientAddGroup.mk h : H ⧸ U.comap ι), ?_⟩
    have h1 : -h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι) ∈ U.comap ι :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
    have h2 : ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι)) ∈ U := h1
    have h3 := U.sub_mem hh h2
    have h4 : g - ι h - ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι))
        = g - r (QuotientAddGroup.mk h : H ⧸ U.comap ι) := by
      simp only [r, map_add, map_neg]; abel
    change g - r _ ∈ U
    rwa [h4] at h3
  have hdisj : Pairwise (Function.onFun Disjoint c) := by
    intro x y hxy
    refine Set.disjoint_left.2 fun g hgx hgy => hxy ?_
    have hgx' : g - r x ∈ U := hgx
    have hgy' : g - r y ∈ U := hgy
    have h1 : ι (-Quotient.out x + Quotient.out y) ∈ U := by
      have h3 := U.sub_mem hgx' hgy'
      have h4 : g - r x - (g - r y) = ι (-Quotient.out x + Quotient.out y) := by
        simp only [r, map_add, map_neg]; abel
      rwa [h4] at h3
    have h2 : (QuotientAddGroup.mk (Quotient.out x) : H ⧸ U.comap ι) = QuotientAddGroup.mk (Quotient.out y) :=
      QuotientAddGroup.eq.2 h1
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h2
  have hne : ∀ x, (c x).Nonempty := fun x => ⟨r x, by
    change r x - r x ∈ U
    simp⟩
  have hcount : Countable (H ⧸ U.comap ι) := by
    have hinj : Function.Injective c := by
      intro x y hxy
      by_contra hne'
      obtain ⟨g, hg⟩ := hne x
      exact Set.disjoint_left.1 (hdisj hne') hg (hxy ▸ hg)
    have hpd : (range c).PairwiseDisjoint id := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      exact hdisj (fun h => hxy (by rw [h]))
    have := hpd.countable_of_isOpen (by rintro _ ⟨x, rfl⟩; exact hcopen x)
      (by rintro _ ⟨x, rfl⟩; exact hne x)
    have := this.to_subtype
    exact Function.Injective.countable (f := Set.rangeFactorization c)
      (fun x y h => hinj (congrArg Subtype.val h))
  have hconst : ∀ x, ∀ g ∈ c x, f g = f (r x) := by
    intro x g hg
    have := hf (r x) (g - r x) hg
    rw [← this]; congr 1; abel
  have hcont : Continuous f := by
    refine IsLocallyConstant.continuous ?_
    refine (IsLocallyConstant.iff_exists_open f).2 fun g => ?_
    refine ⟨(fun y => y - g) ⁻¹' (U : Set G), hUo.preimage (by fun_prop), by simp, ?_⟩
    intro y hy
    have := hf g (y - g) hy
    rw [← this]; congr 1; abel
  have hmeas : ∀ x, ν (c x) = ν (U : Set G) := by
    intro x
    have : c x = (fun g => g + (- r x)) ⁻¹' (U : Set G) := by
      ext g; simp [c, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
  have hUfin : ν (U : Set G) < ⊤ := hUc.measure_lt_top
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hsum : ∑' x, ‖f (r x)‖ₑ < ⊤ := by
    have h1 : ∑' x, ‖f (r x)‖ₑ = ∑' x, ENNReal.ofReal ‖f (r x)‖ := by
      simp [ofReal_norm_eq_enorm]
    rw [h1]
    exact hs.tsum_ofReal_lt_top
  have hint : ∫⁻ g, ‖f g‖ₑ ∂ν = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := by
    calc ∫⁻ g, ‖f g‖ₑ ∂ν = ∫⁻ g in ⋃ x, c x, ‖f g‖ₑ ∂ν := by rw [hcov, Measure.restrict_univ]
      _ = ∑' x, ∫⁻ g in c x, ‖f g‖ₑ ∂ν :=
          lintegral_iUnion (fun x => (hcopen x).measurableSet) hdisj _
      _ = ∑' x, ‖f (r x)‖ₑ * ν (U : Set G) := by
          refine tsum_congr fun x => ?_
          rw [setLIntegral_congr_fun (hcopen x).measurableSet
            (g := fun _ => ‖f (r x)‖ₑ) (fun g hg => by simp only [hconst x g hg]),
            setLIntegral_const, hmeas]
      _ = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := ENNReal.tsum_mul_right
  change ∫⁻ g, ‖f g‖ₑ ∂ν < ⊤
  rw [hint]
  exact ENNReal.mul_lt_top hsum hUfin

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_over_lattice_quotient_locally_constant : ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

theorem summable_comp_of_injective_prod {X Y Q : Type*} [Finite Q] {d : Y → ℝ}
    (hd : ∀ y, 0 ≤ d y) (hs : Summable d) (y : X → Y) (q : X → Q)
    (hinj : Function.Injective fun x => (y x, q x)) : Summable fun x => d (y x) := by
  have h1 : Summable (fun p : Y × Q => d p.1 * (fun _ : Q => (1 : ℝ)) p.2) :=
    Summable.mul_of_nonneg hs (Summable.of_finite) hd (fun _ => zero_le_one)
  have h2 := h1.comp_injective hinj
  simpa [Function.comp_def] using h2

theorem finite_quot_nsmul {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] {τ : ℕ} (hτ : 0 < τ) :
    Finite (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
  haveI : Module.Finite ℤ (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' _).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H m =>
    refine ⟨⟨(τ : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hτ.ne')⟩, ?_⟩
    have : ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range))
        = ((τ • m : M) : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
      rw [natCast_zsmul]; rfl
    show ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range)) = 0
    rw [this, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_hermO_iff (σ : E →ₐ[F] E) (n : ℕ) (c : hermE σ n) :
    c ∈ hermO σ n ↔ ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b := Iff.rfl

def toInt (σ : E →ₐ[F] E) (n : ℕ) : hermO σ n →+ Matrix (Fin n) (Fin n) (𝓞 E) where
  toFun c := Matrix.of fun a b => Classical.choose ((mem_hermO_iff σ n c.1).1 c.2 a b)
  map_zero' := by
    ext a b
    have h := Classical.choose_spec ((mem_hermO_iff σ n (0 : hermO σ n).1).1 (0 : hermO σ n).2 a b)
    refine Eq.trans h ?_
    change _ = algebraMap (𝓞 E) E 0
    rw [map_zero]
    rfl
  map_add' := by
    intro c d
    ext a b
    have h1 := Classical.choose_spec ((mem_hermO_iff σ n (c + d).1).1 (c + d).2 a b)
    have h2 := Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)
    have h3 := Classical.choose_spec ((mem_hermO_iff σ n d.1).1 d.2 a b)
    refine Eq.trans h1 ?_
    change _ = algebraMap (𝓞 E) E (_ + _)
    rw [map_add]
    exact Eq.trans rfl (Eq.symm (Eq.trans (congrArg₂ (· + ·) h2 h3) rfl))

theorem algebraMap_toInt (σ : E →ₐ[F] E) (n : ℕ) (c : hermO σ n) (a b : Fin n) :
    algebraMap (𝓞 E) E (toInt σ n c a b) = c.1.1 a b :=
  Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)

theorem toInt_injective (σ : E →ₐ[F] E) (n : ℕ) : Function.Injective (toInt σ n) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  ext a b
  rw [← algebraMap_toInt σ n c a b, ← algebraMap_toInt σ n d a b, h]

theorem finite_hermO (σ : E →ₐ[F] E) (n : ℕ) : Module.Finite ℤ (hermO σ n) :=
  Module.Finite.of_injective (toInt σ n).toIntLinearMap (toInt_injective σ n)

theorem Kc_le_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : Kc c ≤ Kc (c + l) := by
  intro y hy i
  obtain ⟨o, ho⟩ := hy i
  choose m hm using hl
  refine ⟨o + ∑ j, m i j * y j, ?_⟩
  rw [Matrix.add_mulVec, Pi.add_apply, map_add, ho]
  congr 1
  simp [Matrix.mulVec, dotProduct, hm]

theorem delta_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : delta (c + l) = delta c := by
  have h1 := Kc_le_add c l hl
  have h2 := Kc_le_add (c + l) (-l) (fun a b => by
    obtain ⟨o, ho⟩ := hl a b
    exact ⟨-o, by simp [ho]⟩)
  rw [add_neg_cancel_right] at h2
  unfold delta
  rw [le_antisymm h2 h1]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare in

theorem summable_quot_of_le_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Λ : AddSubgroup (hermE σ n)) (t : F), t ≠ 0 → ∀ τ : ℕ, 0 < τ →
    (∀ c ∈ hermO σ n, ((τ : F) / t) • c ∈ Λ) →
    ∀ g : hermE σ n → ℝ, (∀ c, 0 ≤ g c) → (∀ c, ∀ l ∈ Λ, g (c + l) = g c) →
    ∀ C s : ℝ, (∀ c, g c ≤ C * (delta (t • c).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ Λ => g (Quotient.out x)) := by
  intro F E _ _ _ _ _ σ n Λ t ht τ hτ hΛ g hg hper C s hb hsum
  haveI : Module.Finite ℤ (hermO σ n) := finite_hermO σ n
  haveI := finite_quot_nsmul (M := hermO σ n) hτ
  let y : hermE σ n ⧸ Λ → hermE σ n ⧸ hermO σ n :=
    fun x => QuotientAddGroup.mk (t • Quotient.out x)
  have hmem : ∀ x, t • Quotient.out x - Quotient.out (y x) ∈ hermO σ n := by
    intro x
    have h : (QuotientAddGroup.mk (Quotient.out (y x)) : hermE σ n ⧸ hermO σ n)
        = QuotientAddGroup.mk (t • Quotient.out x) := QuotientAddGroup.out_eq' (y x)
    have := QuotientAddGroup.eq.1 h
    rwa [neg_add_eq_sub] at this
  let w : hermE σ n ⧸ Λ → hermO σ n := fun x => ⟨_, hmem x⟩
  let q : hermE σ n ⧸ Λ → hermO σ n ⧸ (nsmulAddMonoidHom τ : hermO σ n →+ hermO σ n).range :=
    fun x => QuotientAddGroup.mk (w x)
  have hinj : Function.Injective fun x => (y x, q x) := by
    intro x x' h
    have hy : y x = y x' := congrArg Prod.fst h
    have hq : q x = q x' := congrArg Prod.snd h
    obtain ⟨c, hc⟩ := QuotientAddGroup.eq.1 hq
    have hc' : τ • (c.1 : hermE σ n) = t • (Quotient.out x' - Quotient.out x) := by
      have := congrArg Subtype.val hc
      simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg,
        AddSubgroup.coe_nsmul] at this
      rw [this]
      simp only [w, hy, smul_sub]
      abel
    have hd : Quotient.out x' - Quotient.out x = ((τ : F) / t) • (c.1 : hermE σ n) := by
      rw [div_eq_inv_mul, mul_smul, Nat.cast_smul_eq_nsmul F τ, hc', smul_smul,
        inv_mul_cancel₀ ht, one_smul]
    have hmemΛ : Quotient.out x' - Quotient.out x ∈ Λ := hd ▸ hΛ _ c.2
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x']
    apply QuotientAddGroup.eq.2
    rwa [neg_add_eq_sub]
  have hdnn : ∀ z : hermE σ n ⧸ hermO σ n,
      0 ≤ (delta (Quotient.out z).1 : ℝ) ^ (-s) := fun z => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_comp_of_injective_prod hdnn hsum y q hinj
  refine Summable.of_nonneg_of_le (fun x => hg _) (fun x => ?_) (hs.mul_left |C|)
  have hdelta : delta (t • Quotient.out x).1 = delta (Quotient.out (y x)).1 := by
    have hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (w x).1.1 a b := (w x).2
    rw [← delta_add (Quotient.out (y x)).1 (w x).1.1 hl]
    congr 1
    simp [w]
  refine (hb _).trans ?_
  rw [hdelta]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (hdnn _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_periodic_bound_by_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Λ : AddSubgroup (hermE σ n)) (t : F), t ≠ 0 → ∀ τ : ℕ, 0 < τ →
    (∀ c ∈ hermO σ n, ((τ : F) / t) • c ∈ Λ) →
    ∀ g : hermE σ n → ℝ, (∀ c, 0 ≤ g c) → (∀ c, ∀ l ∈ Λ, g (c + l) = g c) →
    ∀ C s : ℝ, (∀ c, g c ≤ C * (delta (t • c).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ Λ => g (Quotient.out x)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.summable_quot_of_le_delta_rpow
end

section
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem blk_mulVec_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) (a : Fin m) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) a.castSucc = (c *ᵥ y) a + u a * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

theorem blk_mulVec_last {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) (Fin.last m) =
      ∑ j, σ (u j) * y j + d * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

variable [NumberField E]

theorem mem_lastFib_blk {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y l : Fin m → 𝓞 E) (s : 𝓞 E)
    (h : ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) a + u a * algebraMap (𝓞 E) E s =
      algebraMap (𝓞 E) E (l a)) :
    (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + d * algebraMap (𝓞 E) E s) ∈
      lastFib (blk σ c u d) := by
  have hvI : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (y j))
      (algebraMap (𝓞 E) E s) : Fin (m + 1) → E) ∈ intVec E (m + 1) := by
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨s, by simp⟩
    · exact ⟨y a, by simp⟩
  have h1 := Submodule.mem_sup_right (S := intVec E (m + 1))
    (Submodule.mem_map_of_mem (f := (blk σ c u d).mulVecLin.restrictScalars (𝓞 E)) hvI)
  have h2 : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (l j)) 0 :
      Fin (m + 1) → E) ∈ lam (blk σ c u d) := by
    refine Submodule.mem_sup_left ?_
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨0, by simp⟩
    · exact ⟨l a, by simp⟩
  have h3 := (lam (blk σ c u d)).sub_mem h1 h2
  show LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m) _ ∈ lam (blk σ c u d)
  convert h3 using 1
  ext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp [blk_mulVec_last]
  · have hne : a.castSucc ≠ Fin.last m := Fin.castSucc_ne_last a
    simp [blk_mulVec_castSucc, h a, hne]

theorem one_le_lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (1 : Submodule (𝓞 E) E) ≤ lastFib C := by
  intro x hx
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hx
  refine Submodule.mem_sup_left (show _ ∈ intVec E (m + 1) from ?_)
  intro i
  by_cases hi : i = Fin.last m
  · subst hi
    exact ⟨o, by simp⟩
  · exact ⟨0, by simp [hi]⟩

theorem lastFib_fg {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (lastFib C).FG := by
  have hfg : (lam C).FG := (GlobalTheory.T.lam_is_lattice E (m + 1) C).1
  have hmap : ((lastFib C).map
      (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))).FG :=
    Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
  exact Submodule.fg_of_fg_map_injective (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))
    (fun a b h => by simpa using congrFun h (Fin.last m)) hmap

theorem tor_decomp {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (t : 𝓞 E)
    (ht : t ∈ tor c u) :
    ∃ yo lo : Fin m → 𝓞 E, ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) a +
      u a * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E (lo a) := by
  have h : t • u ∈ lam c := by
    have h0 := (Ideal.mem_torsionOf_iff _ _).1 ht
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨l, hl, z, ⟨y, hy, rfl⟩, hz⟩ := Submodule.mem_sup.1 h
  choose lo hlo using hl
  choose yo hyo using hy
  refine ⟨-yo, lo, fun a => ?_⟩
  have h1 := congrFun hz a
  have hy' : (fun j => algebraMap (𝓞 E) E ((-yo) j)) = -y := by
    funext j
    simp [hyo j]
  rw [hy', Matrix.mulVec_neg, hlo a]
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Pi.add_apply, Pi.smul_apply,
    Algebra.smul_def] at h1
  simp only [Pi.neg_apply]
  linear_combination -h1
end

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  intro F E _ _ _ _ _ σ hCM m c hc u t ht ht0
  obtain ⟨hinv, hfix, hsO, hN⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hCM
  obtain ⟨yo, lo, hyl⟩ := LocalBound.tor_decomp c u t ht
  have hf0 : σ (-∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j)) =
      -∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
    have hs : ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j * σ (algebraMap (𝓞 E) E (yo j)) := by
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hc]
      ring
    rw [map_neg, map_sum]
    simp only [map_mul, hinv]
    rw [hs]
  obtain ⟨f, hf⟩ := hfix _ hf0
  refine ⟨f, fun d => ?_⟩
  have hT : tor c u ≠ ⊥ := fun h => ht0 (by simpa [h] using ht)
  have hsOt : sO σ t ≠ 0 := by
    intro h0
    apply ht0
    have h1 : σ (algebraMap (𝓞 E) E t) = 0 := by
      have := hsO t
      rw [h0] at this
      simpa using this.symm
    have h2 : algebraMap (𝓞 E) E t = 0 := by
      rw [← hinv (algebraMap (𝓞 E) E t), h1, map_zero]
    exact (map_eq_zero_iff _ (RingOfIntegers.coe_injective)).1 h2
  have hmem : ∀ t' ∈ tor c u, sO σ t' ∈ (tor c u).map (sO σ) :=
    fun t' h' => Ideal.mem_map_of_mem _ h'
  have h𝔱 : (tor c u).map (sO σ) ≠ ⊥ := by
    intro h0
    have := hmem t ht
    rw [h0] at this
    exact hsOt (by simpa using this)
  have hw := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) yo lo t hyl
  have hinvb : ∀ b : E, (∀ a ∈ (tor c u).map (sO σ), (a : E) * b ∈ (1 : Submodule (𝓞 E) E)) →
      b ∈ lastFib (blk σ c u (algebraMap F E d)) := by
    intro b hb
    obtain ⟨y, hy, hby⟩ := GlobalTheory.T.torsion_orthogonality_integral_solution F E σ hCM m c hc u b (fun t' h' => by
      have := hb _ (hmem t' h')
      rwa [show ((sO σ t' : 𝓞 E) : E) = σ (t' : E) from hsO t'] at this)
    choose lo' hlo' using hy
    have h1 := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) y lo' 0 (fun a => by
      rw [hlo' a]
      simp)
    have h2 := LocalBound.one_le_lastFib (blk σ c u (algebraMap F E d)) hby
    have h3 := Submodule.add_mem _ h1 h2
    have h4 : (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + algebraMap F E d * algebraMap (𝓞 E) E 0) +
        (b - ∑ j, σ (u j) * (y j : E)) = b := by
      simp only [map_zero, mul_zero, add_zero]
      exact add_sub_cancel _ _
    rwa [h4] at h3
  have hnorm := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hCM t).1
  have hkey : ((sO σ t : 𝓞 E) : E) * (∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) +
      algebraMap F E d * algebraMap (𝓞 E) E t) -
      algebraMap F E (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d) ∈ (1 : Submodule (𝓞 E) E) := by
    refine Submodule.mem_one.2 ⟨∑ j, sO σ (lo j) * yo j, ?_⟩
    have hsum : σ (algebraMap (𝓞 E) E t) * ∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) -
          ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hyl j, map_add, map_mul]
      ring
    have hs2 : algebraMap (𝓞 E) E (∑ j, sO σ (lo j) * yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (hsO (lo j))
    rw [hs2, show ((sO σ t : 𝓞 E) : E) = σ (algebraMap (𝓞 E) E t) from hsO t, map_add, map_mul,
      hf, hnorm]
    have hnorm' : (t : E) = algebraMap (𝓞 E) E t := rfl
    rw [hnorm']
    linear_combination -hsum
  have hmain := GlobalTheory.T.denominator_index_bound E ((tor c u).map (sO σ)) h𝔱
    (lastFib (blk σ c u (algebraMap F E d))) (LocalBound.lastFib_fg _)
    (LocalBound.one_le_lastFib _) hinvb (sO σ t) _ _ (hmem t ht) hw hkey
  rw [hN, GlobalTheory.T.denominator_norm_quadratic_extension F E hCM.2.2.1] at hmain
  rw [GlobalTheory.T.delta_block_matrix_multiplicative F E σ m c u (algebraMap F E d)]
  calc delta c * Ideal.absNorm (tor c u) ^ 2 *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2
      = delta c * Ideal.absNorm (tor c u) * (Ideal.absNorm (tor c u) *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hmain
end
end

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_lower_bound_torsion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound
end

section
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD

theorem fibres (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (hρ : ρ ≠ 0) (a : FQ F) (b : FQ F) :
    Finite {D : FQ F // a + ρ • D = b} ∧
      Nat.card {D : FQ F // a + ρ • D = b} ≤ Ideal.absNorm (Ideal.span {ρ}) := by
  have hne : Ideal.span {ρ} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hρ
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow F 1 (intVec F 1) (isLat_intVec 1) (Ideal.span {ρ}) hne
  rw [pow_one] at hcard
  by_cases hb : ∃ D₀ : FQ F, a + ρ • D₀ = b
  · obtain ⟨D₀, hD₀⟩ := hb
    let φ : {D : FQ F // a + ρ • D = b} → {x : FQ F // ∀ r ∈ Ideal.span {ρ}, r • x = 0} :=
      fun D => ⟨D.1 - D₀, by
        intro r hr
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h1 : ρ • (D.1 - D₀) = 0 := by
          have h2 : a + ρ • D.1 = a + ρ • D₀ := D.2.trans hD₀.symm
          rw [smul_sub, sub_eq_zero]
          exact add_left_cancel h2
        rw [mul_smul, h1, smul_zero]⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h3 : x.1 - D₀ = y.1 - D₀ := congrArg Subtype.val hxy
      exact Subtype.ext (sub_left_inj.1 h3)
    have hF : Finite {D : FQ F // a + ρ • D = b} := Finite.of_injective φ hφ
    exact ⟨hF, (Nat.card_le_card_of_injective φ hφ).trans hcard⟩
  · have hE : IsEmpty {D : FQ F // a + ρ • D = b} := ⟨fun D => hb ⟨D.1, D.2⟩⟩
    exact ⟨inferInstance, by simp⟩

theorem den_eq (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (f : F) (D : FQ F) :
    den F (f + ((ρ : 𝓞 F) : F) * (Quotient.out D : Fin 1 → F) 0) =
      Ideal.torsionOf (𝓞 F) (FQ F)
        ((Submodule.Quotient.mk (fun _ => f) : FQ F) + ρ • D) := by
  unfold den
  congr 1
  have hD : D = Submodule.Quotient.mk (Quotient.out D : Fin 1 → F) :=
    (Quotient.out_eq D).symm
  conv_rhs => rw [hD]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [Algebra.smul_def]

theorem term_le (A δ N n : ℕ) (s : ℝ) (hs : 0 < s) (hδ : δ ≠ 0) (hN : N ≠ 0) (hn : n ≠ 0)
    (h : δ * N ^ 2 * n ^ 2 ≤ A) :
    (A : ℝ) ^ (-s) ≤ (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hle : (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ A := by exact_mod_cast h
  have hpos : (0 : ℝ) < (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hsq : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (-s) = x ^ (-(2 * s)) := by
    intro x hx
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  calc (A : ℝ) ^ (-s) ≤ ((δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    _ = (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hsq _ hN', hsq _ hn']

theorem sum_delta_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨C, hC, hmink⟩ := GlobalTheory.T.ideal_principal_element_norm_bound E
  refine ⟨C, hC, ?_⟩
  intro m c hc u s hs
  have hT : tor c u ≠ ⊥ :=
    GlobalTheory.T.lattice_quotient_torsion_nonzero E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) (Submodule.Quotient.mk u)
  obtain ⟨t, htT, ht0, htC⟩ := hmink (tor c u) hT
  obtain ⟨f, hf⟩ := GlobalTheory.T.delta_block_lower_bound_torsion F E σ hσ m c hc u t htT ht0
  have hkt : Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) =
      Ideal.absNorm (Ideal.span {t}) := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hσ t).2
  have hNt : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa [Ideal.span_singleton_eq_bot] using ht0
  have hρ : RingOfIntegers.norm F t ≠ 0 := by
    intro h0
    rw [h0] at hkt
    apply hNt
    rw [← hkt]
    simp
  generalize hρdef : RingOfIntegers.norm F t = ρ at hf hkt hρ
  have hδ : delta c ≠ 0 := (GlobalTheory.T.delta_eq_lattice_index E m c).1
  have hN : Ideal.absNorm (tor c u) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hT
  have hδ' : (0 : ℝ) < delta c := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < Ideal.absNorm (tor c u) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs0 : 0 < s := by linarith
  obtain ⟨hsum, hzeta⟩ := GlobalTheory.T.torsion_norm_zeta_bound F 1 (intVec F 1) (isLat_intVec 1) (2 * s - 1) (by linarith)
  have hexp : (((1 : ℕ) : ℝ) + (2 * s - 1)) = 2 * s := by
    push_cast
    ring
  rw [hexp] at hsum hzeta
  let g : FQ F → ℝ := fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) x) : ℝ) ^ (-(2 * s))
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let a : FQ F := Submodule.Quotient.mk (fun _ => f)
  let π : FQ F → FQ F := fun D => a + ρ • D
  obtain ⟨hsum2, hle2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le (FQ F) (FQ F) π (Ideal.absNorm (Ideal.span {ρ}))
    (fun b => fibres F ρ hρ a b) g hg0 hsum
  let P : ℝ := (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s))
  have hP : 0 ≤ P := by positivity
  have hterm : ∀ D : FQ F,
      (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤
        P * g (π D) := by
    intro D
    have h1 := hf ((Quotient.out D : Fin 1 → F) 0)
    rw [den_eq F ρ f D] at h1
    have hn : Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) (π D)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact GlobalTheory.T.lattice_quotient_torsion_nonzero F 1 (intVec F 1) (isLat_intVec 1) (π D)
    exact term_le _ _ _ _ s hs0 hδ hN hn h1
  have hnn : ∀ D : FQ F,
      0 ≤ (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) :=
    fun D => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsumP : Summable (fun D : FQ F => P * g (π D)) := hsum2.mul_left P
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsumP, ?_⟩
  have hS : 0 ≤ ∑' x, g x := tsum_nonneg hg0
  have hZ : 0 ≤ zetaR F (2 * s - 1) := hS.trans hzeta
  have hkC : (Ideal.absNorm (Ideal.span {ρ}) : ℝ) ≤ C * Ideal.absNorm (tor c u) := by
    rw [hkt]
    exact htC
  have hpow : (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s)) * (Ideal.absNorm (tor c u) : ℝ) =
      (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
    rw [show (1 - 2 * s) = -(2 * s) + 1 by ring, Real.rpow_add hN', Real.rpow_one]
  calc ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)
      ≤ ∑' D : FQ F, P * g (π D) :=
        (Summable.of_nonneg_of_le hnn hterm hsumP).tsum_le_tsum hterm hsumP
    _ = P * ∑' D : FQ F, g (π D) := tsum_mul_left
    _ ≤ P * ((Ideal.absNorm (Ideal.span {ρ}) : ℝ) * ∑' x, g x) :=
        mul_le_mul_of_nonneg_left hle2 hP
    _ ≤ P * ((C * Ideal.absNorm (tor c u)) * zetaR F (2 * s - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        exact mul_le_mul hkC hzeta hS (by positivity)
    _ = C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) *
          (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
        rw [← hpow]
        simp only [P]
        ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD
end
end

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_series_zeta_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

theorem zetaR_nonneg (K : Type) [Field K] [NumberField K] (r : ℝ) : 0 ≤ zetaR K r :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (m : ℕ) (s : ℝ) (hs : (m : ℝ) + 1 < s)
    (ih : Summable (fun x : hermE σ m ⧸ hermO σ m => (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)))) :
    Summable (fun x : hermE σ (m + 1) ⧸ hermO σ (m + 1) =>
      (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.delta_block_series_zeta_bound F E σ hσ
  obtain ⟨ι, hinj, hι⟩ := GlobalTheory.T.delta_block_quotient_injection F E σ hσ m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs1 : 1 < s := by linarith
  set G : (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F → ℝ := fun p =>
    (delta (blk σ (Quotient.out p.1).1 (Quotient.out p.2.1)
      (algebraMap F E ((Quotient.out p.2.2 : Fin 1 → F) 0))) : ℝ) ^ (-s) with hG
  have hG0 : 0 ≤ G := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set r : ℝ := 2 * s - 1 - m with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hexp : 1 - 2 * s = -((m : ℝ) + r) := by rw [hr]; ring

  have hin : ∀ (x : hermE σ m ⧸ hermO σ m) (U : (Fin m → E) ⧸ intVec E m),
      Summable (fun D : FQ F => G (x, U, D)) ∧
      ∑' D : FQ F, G (x, U, D) ≤ C * zetaR F (2 * s - 1) * (delta (Quotient.out x).1 : ℝ) ^ (-s) *
        (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) := by
    intro x U
    have := hD m (Quotient.out x).1 (Quotient.out x).2 (Quotient.out U) s hs1
    rw [hexp] at this
    exact this
  set A : ℝ := C * zetaR F (2 * s - 1) with hA
  have hA0 : 0 ≤ A := mul_nonneg hC.le (zetaR_nonneg _ _)
  have hmid : ∀ x : hermE σ m ⧸ hermO σ m,
      Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) ∧
      ∑' q : ((Fin m → E) ⧸ intVec E m) × FQ F, G (x, q) ≤
        A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
    intro x
    obtain ⟨hU, hUle⟩ := GlobalTheory.T.torsion_sum_zeta_bound_delta E m (Quotient.out x).1 r hr1
    have hδ : (0 : ℝ) < delta (Quotient.out x).1 :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (GlobalTheory.T.delta_eq_lattice_index E m _).1)
    set B : ℝ := A * (delta (Quotient.out x).1 : ℝ) ^ (-s) with hB
    have hB0 : 0 ≤ B := mul_nonneg hA0 (Real.rpow_nonneg hδ.le _)
    have hsum : Summable (fun U : (Fin m → E) ⧸ intVec E m => ∑' D : FQ F, G (x, U, D)) :=
      Summable.of_nonneg_of_le (fun U => tsum_nonneg fun D => hG0 _) (fun U => (hin x U).2)
        (hU.mul_left B)
    have hS : Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) :=
      (summable_prod_of_nonneg (fun q => hG0 (x, q))).mpr ⟨fun U => (hin x U).1, hsum⟩
    refine ⟨hS, ?_⟩
    rw [hS.tsum_prod' (fun U => (hin x U).1)]
    calc ∑' U : (Fin m → E) ⧸ intVec E m, ∑' D : FQ F, G (x, U, D)
        ≤ ∑' U : (Fin m → E) ⧸ intVec E m, B *
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          hsum.tsum_le_tsum (fun U => (hin x U).2) (hU.mul_left B)
      _ = B * ∑' U : (Fin m → E) ⧸ intVec E m,
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          tsum_mul_left
      _ ≤ B * (delta (Quotient.out x).1 * zetaR E r) := mul_le_mul_of_nonneg_left hUle hB0
      _ = A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
          have : (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) =
              (delta (Quotient.out x).1 : ℝ) ^ (-s) * delta (Quotient.out x).1 := by
            rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
          rw [this, hB]
          ring
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun x => (hmid x).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun x => tsum_nonneg fun q => hG0 _) (fun x => (hmid x).2)
      (ih.mul_left _)
  refine (hGs.comp_injective hinj).congr fun x => ?_
  simp only [Function.comp, hG, hι x]

theorem summable_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro s _
    haveI : Subsingleton (hermE σ 0) := ⟨fun a b => Subtype.ext (Matrix.ext fun i => i.elim0)⟩
    haveI : Subsingleton (hermE σ 0 ⧸ hermO σ 0) := QuotientAddGroup.mk_surjective.subsingleton
    exact summable_of_finite_support (Set.toFinite _)
  | succ n ih =>
    intro s hs
    push_cast at hs
    exact step σ hσ n s hs (ih (s - 1) (by linarith))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_denominator_power_of_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Period

def HasCO (G : Type) [AddGroup G] [TopologicalSpace G] : Prop :=
  ∀ W ∈ 𝓝 (0 : G), ∃ P : AddSubgroup G, IsOpen (P : Set G) ∧ IsCompact (P : Set G) ∧ (P : Set G) ⊆ W

theorem HasCO.pi {ι : Type} [Finite ι] {G : ι → Type} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)] (h : ∀ i, HasCO (G i)) : HasCO (∀ i, G i) := by
  intro W hW
  rw [nhds_pi] at hW
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.1 hW
  choose P hPo hPc hPW using fun i => h i (t i) (ht i)
  have hcoe : ((AddSubgroup.pi Set.univ P : AddSubgroup (∀ i, G i)) : Set (∀ i, G i)) =
      Set.univ.pi fun i => (P i : Set (G i)) := by
    ext x
    simp [AddSubgroup.mem_pi]
  refine ⟨AddSubgroup.pi Set.univ P, ?_, ?_, ?_⟩
  · rw [hcoe]
    exact isOpen_set_pi Set.finite_univ fun i _ => hPo i
  · rw [hcoe]
    exact isCompact_univ_pi hPc
  · intro x hx
    rw [hcoe] at hx
    exact hsub fun i _ => hPW i (hx i (Set.mem_univ i))

theorem HasCO.comap {G H : Type} [AddGroup G] [TopologicalSpace G] [AddGroup H] [TopologicalSpace H]
    (h : HasCO H) (f : G →+ H) (hf : IsHomeomorph f) : HasCO G := by
  intro W hW
  let e : G ≃ₜ H := hf.homeomorph f
  have he : ∀ x, e x = f x := fun _ => rfl
  have h0 : e.symm 0 = 0 := by
    apply e.injective
    rw [e.apply_symm_apply, he, map_zero]
  have hW' : e.symm ⁻¹' W ∈ 𝓝 (0 : H) := by
    apply e.symm.continuous.continuousAt.preimage_mem_nhds
    rwa [h0]
  obtain ⟨P, hPo, hPc, hPW⟩ := h _ hW'
  refine ⟨P.comap f, hPo.preimage hf.continuous, ?_, ?_⟩
  · have : ((P.comap f : AddSubgroup G) : Set G) = e.symm '' (P : Set H) := by
      ext x
      constructor
      · intro hx
        exact ⟨e x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        change f (e.symm y) ∈ P
        rw [← he]
        simpa using hy
    rw [this]
    exact hPc.image e.symm.continuous
  · intro x hx
    have h1 : e.symm (e x) ∈ W := hPW (by rw [he]; exact hx)
    rwa [e.symm_apply_apply] at h1

theorem HasCO.sub {G : Type} [AddGroup G] [TopologicalSpace G] (h : HasCO G) (S : AddSubgroup G)
    (hS : IsClosed (S : Set G)) : HasCO S := by
  intro W hW
  obtain ⟨W', hW', hsub⟩ := mem_nhds_subtype (S : Set G) 0 W |>.1 hW
  obtain ⟨P, hPo, hPc, hPW⟩ := h W' hW'
  refine ⟨P.comap S.subtype, hPo.preimage continuous_subtype_val, ?_, ?_⟩
  · have hemb : Topology.IsClosedEmbedding (Subtype.val : S → G) := hS.isClosedEmbedding_subtypeVal
    exact hemb.isCompact_preimage hPc
  · intro x hx
    exact hsub (hPW hx)

theorem small_pow {z : ℂ} (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1 / 2) : z = 1 :=
  by apply _root_.UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near <;> assumption

end GlobalTheory.CompanionTheory.SiegelND.Integ.Period

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Period

open GlobalTheory.CompanionTheory.SW.Core in
theorem hasCO_Af (F : Type) [Field F] [NumberField F] : HasCO (Af F) := by
  obtain ⟨h1, h2, h3, hOc, hOo, -, -, hB, -, hNo⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hadd : ∀ x ∈ Oh F, ∀ y ∈ Oh F, x + y ∈ Oh F := fun x hx y hy v =>
    add_mem (hx v) (hy v)
  have hneg : ∀ x ∈ Oh F, -x ∈ Oh F := fun x hx v => neg_mem (hx v)
  have hz : (0 : Af F) ∈ Oh F := fun v => zero_mem _
  intro W hW
  obtain ⟨N, hN, hNW⟩ := hB W hW
  let P : AddSubgroup (Af F) :=
    { carrier := {x | ∃ y ∈ Oh F, x = (N : Af F) * y}
      zero_mem' := ⟨0, hz, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, hadd x hx y hy, by ring⟩
      neg_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨-x, hneg x hx, by ring⟩ }
  refine ⟨P, hNo N hN, ?_, ?_⟩
  · have : (P : Set (Af F)) = (fun y => (N : Af F) * y) '' Oh F := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [this]
    exact hOc.image (continuous_const.mul continuous_id)
  · rintro _ ⟨y, hy, rfl⟩
    exact hNW y hy

theorem psiFin_add (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (x y : Af F) :
    psiFin F ψ (x + y) = psiFin F ψ x * psiFin F ψ y := by
  have : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y :=
    Prod.ext (show (0 : Ainf F) = 0 + 0 by simp) rfl
  simp only [psiFin]
  rw [this, AddChar.map_add_eq_mul]

theorem psiFin_trivial (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : ∃ V : AddSubgroup (Af F), IsOpen (V : Set (Af F)) ∧
      ∀ y ∈ V, psiFin F ψ y = 1 := by
  have hc : Continuous (psiFin F ψ) := by
    have : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
    exact hψ.1.comp this
  have h0 : psiFin F ψ 0 = 1 := by
    have : pairA F 0 (0 : Af F) = 0 := rfl
    simp [psiFin, this]
  have hB : {y | ‖psiFin F ψ y - 1‖ < 1 / 2} ∈ 𝓝 (0 : Af F) := by
    have : IsOpen {y | ‖psiFin F ψ y - 1‖ < 1 / 2} :=
      isOpen_lt ((hc.sub continuous_const).norm) continuous_const
    exact this.mem_nhds (by simp [h0])
  obtain ⟨P, hPo, -, hPB⟩ := hasCO_Af F _ hB
  refine ⟨P, hPo, fun y hy => small_pow fun k => ?_⟩
  have hk : psiFin F ψ (k • y) = psiFin F ψ y ^ k := by
    induction k with
    | zero =>
      simpa using h0
    | succ k ih =>
      rw [succ_nsmul, psiFin_add, ih, pow_succ]
  rw [← hk]
  exact hPB (P.nsmul_mem hy k)

theorem hasCO_herm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n : ℕ) : HasCO (HermR (Af F) σ n) := by
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨-, -, -, -, -, -, hh, -, hcl, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let c : (Af F ⊗[F] E) →+ (Fin (Module.finrank F E) → Af F) :=
    { toFun := fun y k => (Algebra.TensorProduct.basis (Af F) b).repr y k
      map_zero' := by
        funext k
        simp
      map_add' := by
        intro x y
        funext k
        simp }
  have hT : HasCO (Af F ⊗[F] E) :=
    HasCO.comap (HasCO.pi fun _ => hasCO_Af F) c (hh _ b)
  have hM : HasCO (Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    HasCO.pi (G := fun _ : Fin n => Fin n → Af F ⊗[F] E) fun _ => HasCO.pi fun _ => hT
  exact hM.sub _ (hcl n)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Period

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Period

theorem tube_zero {H Y A : Type} [AddGroup H] [TopologicalSpace H] [TopologicalSpace Y]
    [TopologicalSpace A] (ph : H → Y → A) (hph : Continuous fun p : H × Y => ph p.1 p.2)
    {V : Set A} (hV : IsOpen V) (h0 : ∀ X, ph 0 X ∈ V) {K : Set Y} (hK : IsCompact K) :
    ∃ W ∈ 𝓝 (0 : H), ∀ u ∈ W, ∀ X ∈ K, ph u X ∈ V := by
  have hsub : ({0} : Set H) ×ˢ K ⊆ (fun p : H × Y => ph p.1 p.2) ⁻¹' V := by
    rintro ⟨u, X⟩ ⟨hu, -⟩
    have hu0 : u = 0 := hu
    subst hu0
    exact h0 X
  obtain ⟨W, W', hWo, -, h0W, hKW, hWW⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hV.preimage hph) hsub
  exact ⟨W, hWo.mem_nhds (h0W rfl), fun u hu X hX => hWW (Set.mk_mem_prod hu (hKW hX))⟩

set_option maxHeartbeats 1000000 in

theorem starLoc_periodic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ U : AddSubgroup (HermR (Af F) σ n), IsOpen (U : Set (HermR (Af F) σ n)) ∧
      IsCompact (U : Set (HermR (Af F) σ n)) ∧
      ∀ b, ∀ u ∈ U, starLoc (Af F) σ J (psiFin F ψ) μ Q (b + u) = starLoc (Af F) σ J (psiFin F ψ) μ Q b := by
  intro F E _ _ _ _ _ σ hσ M J n ψ hψ μ _ Q hQ
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨t1, -, -, -, -, htr, -, -, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := t1
  obtain ⟨V, hVo, hV⟩ := psiFin_trivial F ψ hψ
  let ph : HermR (Af F) σ n → (Fin n → Fin M → Af F ⊗[F] E) → Af F := fun u X =>
    algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace ((u : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gramR (Af F) σ J X))
  have hph : Continuous fun p : HermR (Af F) σ n × (Fin n → Fin M → Af F ⊗[F] E) => ph p.1 p.2 := by
    refine continuous_const.mul (htr.comp (Continuous.matrix_trace (Continuous.matrix_mul ?_ ?_)))
    · exact continuous_subtype_val.comp continuous_fst
    · exact (hG n M J).comp continuous_snd
  have hK : IsCompact (tsupport Q) := hQ.2
  have h0 : ∀ X, ph 0 X ∈ (V : Set (Af F)) := fun X => by
    simp [ph, V.zero_mem]
  obtain ⟨W, hW0, hWW⟩ := tube_zero ph hph hVo h0 hK
  obtain ⟨U, hUo, hUc, hUW⟩ := hasCO_herm F E σ hσ n W hW0
  refine ⟨U, hUo, hUc, fun b u hu => ?_⟩
  unfold starLoc
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  by_cases hX : X ∈ tsupport Q
  · have hsplit : ph (b + u) X = ph b X + ph u X := by
      simp only [ph, AddSubgroup.coe_add, add_mul, Matrix.trace_add, map_add, mul_add]
    have hm : ph u X ∈ V := hWW u (hUW (SetLike.mem_coe.2 hu)) X hX
    have h1 : psiFin F ψ (ph u X) = 1 := hV (ph u X) hm
    change Q X * psiFin F ψ (ph (b + u) X) = Q X * psiFin F ψ (ph b X)
    rw [hsplit, psiFin_add, h1, mul_one]
  · have hq : Q X = 0 := image_eq_zero_of_notMem_tsupport hX
    simp [hq]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Period
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_integral_invariant_open_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ U : AddSubgroup (HermR (Af F) σ n), IsOpen (U : Set (HermR (Af F) σ n)) ∧
      IsCompact (U : Set (HermR (Af F) σ n)) ∧
      ∀ b, ∀ u ∈ U, starLoc (Af F) σ J (psiFin F ψ) μ Q (b + u) = starLoc (Af F) σ J (psiFin F ψ) μ Q b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Period.starLoc_periodic
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

theorem sig_sig_of_isCM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) :
    sigR R σ (sigR R σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (h : F) (t : R ⊗[F] E) :
    sigR R σ (h • t) = h • sigR R σ t :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id F R) σ) h t

theorem inclR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (h : F) (e : E) : inclR (F := F) R (h • e) = h • inclR (F := F) R e :=
  map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) h e

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem denseRange_inclR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] (hd : DenseRange (algebraMap F R)) :
    DenseRange (inclR R : E →+* R ⊗[F] E) := by
  haveI : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have hφ := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R).2.2.2.2.2.2.1 _ b
  let φ := hφ.homeomorph
  have hpi : DenseRange (Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    DenseRange.piMap fun _ => hd
  have hc : DenseRange (φ.symm ∘ Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    φ.symm.surjective.denseRange.comp hpi φ.symm.continuous
  refine hc.mono ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨b.equivFun.symm a, ?_⟩
  apply φ.injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  funext k
  show (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (b.equivFun.symm a)) k = _
  simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, apply_ite]

theorem hermE_dense_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  intro F E _ _ _ _ _ σ hCM n U hU g
  obtain ⟨hlc, hsc, ht2, -, -, hden, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨hTR, -, -, -, hsig, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  have hincl := denseRange_inclR F E σ hCM (Af F) hden
  have hσ := sig_sig_of_isCM σ hCM

  have hmat : DenseRange (fun c : Matrix (Fin n) (Fin n) E => c.map (inclR (Af F))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hincl))

  let h : F := 1 / 2
  let Pm : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun m a b => h • (m a b + sigR (Af F) σ (m b a))
  have hPm : ∀ m, Pm m ∈ HermR (Af F) σ n := by
    intro m a b
    show sigR (Af F) σ (h • (m b a + sigR (Af F) σ (m a b))) = h • (m a b + sigR (Af F) σ (m b a))
    rw [sigR_smul, map_add, sigR_sigR _ _ hσ, add_comm]
  have hsmul : Continuous fun x : Af F ⊗[F] E => h • x := by
    simp_rw [Algebra.smul_def]
    exact continuous_const.mul continuous_id
  have hPc : Continuous Pm := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact hsmul.comp ((continuous_id.matrix_elem a b).add
      (hsig.comp (continuous_id.matrix_elem b a)))
  let P : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → HermR (Af F) σ n := fun m => ⟨Pm m, hPm m⟩
  have hP : Continuous P := hPc.subtype_mk hPm
  have hW : IsOpen {m | g - P m ∈ U} :=
    hU.preimage (continuous_const.sub hP)
  have hg : P g.1 = g := by
    apply Subtype.ext
    ext a b
    show h • (g.1 a b + sigR (Af F) σ (g.1 b a)) = g.1 a b
    rw [g.2 a b, ← two_smul F, smul_smul]
    norm_num [h]
  have hne : ({m | g - P m ∈ U} : Set _).Nonempty := ⟨g.1, by simp [hg, U.zero_mem]⟩
  obtain ⟨c₀, hc₀⟩ := hmat.exists_mem_open hW hne
  let c : Matrix (Fin n) (Fin n) E := fun a b => h • (c₀ a b + σ (c₀ b a))
  have hc : c ∈ hermE σ n := by
    intro a b
    show σ (h • (c₀ b a + σ (c₀ a b))) = h • (c₀ a b + σ (c₀ b a))
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def, map_add, hσ, add_comm]
  refine ⟨⟨c, hc⟩, ?_⟩
  have hcP : hermIn (Af F) σ n ⟨c, hc⟩ = P (c₀.map (inclR (Af F))) := by
    apply Subtype.ext
    ext a b
    show inclR (Af F) (h • (c₀ a b + σ (c₀ b a))) =
      h • (inclR (Af F) (c₀ a b) + sigR (Af F) σ (inclR (Af F) (c₀ b a)))
    rw [inclR_smul, map_add, sigR_inclR]
  rw [hcP]
  exact hc₀

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_finite_adeles_dense_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open Topology

theorem exists_den {F : Type} [Field F] [NumberField F] (y : F) :
    ∃ D : ℕ, 0 < D ∧ ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y := by
  have hal : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨z, hz, hint⟩ := hal.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_⟩
  have hint' : IsIntegral ℤ ((z.natAbs : F) * y) := by
    rcases Int.natAbs_eq z with h | h
    · have : ((z.natAbs : F) * y) = z • y := by
        rw [zsmul_eq_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rwa [this]
    · have : ((z.natAbs : F) * y) = -(z • y) := by
        rw [zsmul_eq_mul, ← neg_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rw [this]
      exact hint.neg
  exact ⟨IsIntegralClosure.mk' (𝓞 F) _ hint', IsIntegralClosure.algebraMap_mk' _ _ _⟩

theorem exists_common_den {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (y : ι → F) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y i := by
  choose D hD r hr using fun i => exists_den (y i)
  refine ⟨∏ i, D i, Finset.prod_pos fun i _ => hD i, fun i => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  refine ⟨(m : 𝓞 F) * r i, ?_⟩
  rw [hm, map_mul, hr, map_natCast]
  push_cast
  ring

theorem coords_den {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (o : 𝓞 E) (k : Fin d), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = (D : F) * b.repr (algebraMap (𝓞 E) E o) k := by
  let e := RingOfIntegers.basis E
  obtain ⟨D, hD, h⟩ := exists_common_den (F := F)
    (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d => b.repr (algebraMap (𝓞 E) E (e p.1)) p.2)
  refine ⟨D, hD, fun o k => ?_⟩
  choose r hr using h
  refine ⟨∑ i, (e.repr o i) • r (i, k), ?_⟩
  have ho : algebraMap (𝓞 E) E o = ∑ i, (e.repr o i) • algebraMap (𝓞 E) E (e i) := by
    conv_lhs => rw [← e.sum_repr o]
    simp [map_sum]
  rw [ho, map_sum, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, Finsupp.smul_apply, hr (i, k)]
  simp only [zsmul_eq_mul]
  ring

theorem nhds_unif {ι Y : Type} [Finite ι] [TopologicalSpace Y] (y0 : Y) (W : Set (ι → Y))
    (hW : W ∈ 𝓝 (fun _ => y0)) : ∃ V ∈ 𝓝 y0, ∀ y : ι → Y, (∀ i, y i ∈ V) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr ht, fun y hy => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hy i) i

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open Topology

theorem exists_smul_mem_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  intro F E _ _ _ _ _ σ hcm n U hU t ht
  obtain ⟨-, hSC, hT2, -, -, -, hF, hN, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : SecondCountableTopology (Af F) := hSC
  haveI : T2Space (Af F) := hT2
  haveI : LocallyCompactSpace (Af F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).1
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Af F)
  let b := Module.finBasis F E
  have hh := hH _ b
  set h := hh.homeomorph with hdef
  have happ : ∀ (y : Af F ⊗[F] E) k, h y k = (Algebra.TensorProduct.basis (Af F) b).repr y k :=
    fun _ _ => rfl
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.mp hU
  let G : (Fin n × Fin n × Fin (Module.finrank F E) → Af F) →
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun x a c => h.symm (fun k => x (a, c, k))
  have hG : Continuous G := by
    refine continuous_matrix fun a c => ?_
    exact h.symm.continuous.comp (continuous_pi fun k => continuous_apply _)
  have hG0 : G (fun _ => 0) = 0 := by
    ext a c
    apply h.injective
    show h (h.symm _) = h 0
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    simp
  have h0 : (0 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ U' := by
    have h1 : (0 : HermR (Af F) σ n) ∈ (U : Set (HermR (Af F) σ n)) := U.zero_mem
    rw [← hU'] at h1
    exact h1
  have hW : G ⁻¹' U' ∈ 𝓝 (fun _ => (0 : Af F)) :=
    (hU'o.preimage hG).mem_nhds (by rw [Set.mem_preimage, hG0]; exact h0)
  obtain ⟨V, hV, hVW⟩ := nhds_unif _ _ hW
  obtain ⟨N, hNpos, hNV⟩ := hN V hV
  obtain ⟨D₁, hD₁, p, hp⟩ := exists_den (t⁻¹)
  obtain ⟨D₂, hD₂, hco⟩ := coords_den b
  refine ⟨D₁ * D₂ * N, by positivity, fun c hc => ?_⟩
  let y : Fin n × Fin n × Fin (Module.finrank F E) → Af F := fun q =>
    algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 q.1 q.2.1) q.2.2)
  have hy : ∀ q, y q ∈ V := by
    rintro ⟨a, a', k⟩
    obtain ⟨o, ho⟩ := hc a a'
    obtain ⟨r, hr⟩ := hco o k
    have hval : b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k
        = (N : F) * (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) := by
      have : (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a')
          = (((D₁ * D₂ * N : ℕ) : F) / t) • algebraMap (𝓞 E) E o := by
        rw [ho]; rfl
      rw [this, map_smul, Finsupp.smul_apply, hp, hr, smul_eq_mul, div_eq_mul_inv]
      push_cast
      ring
    have hmem : algebraMap F (Af F) (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) ∈
        GlobalTheory.CompanionTheory.SW.Core.Oh F := (hF _).mpr ⟨p * r, by simp⟩
    have := hNV _ hmem
    show algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k) ∈ V
    rw [hval, map_mul, map_natCast]
    exact this
  have hGy : G y ∈ U' := hVW y hy
  have heq : G y = (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 := by
    ext a a'
    apply h.injective
    show h (h.symm _) = _
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    show y (a, a', k) = _
    have hentry : (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 a a' =
        (1 : Af F) ⊗ₜ[F] (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') := rfl
    rw [hentry, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, one_smul, Finsupp.mapRange_apply]
    rfl
  have hfin : hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c) ∈ (U : Set (HermR (Af F) σ n)) := by
    rw [← hU']
    show _ ∈ U'
    rw [← heq]
    exact hGy
  exact hfin

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_integral_hermitian_in_open_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

theorem integrable_starLoc_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Af F) σ n), ν.IsAddHaarMeasure →
  ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    Integrable (starLoc (Af F) σ J (psiFin F ψ) μ Q) ν := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ μ hμ ν hν Q hQ
  obtain ⟨hLC, hSC, hT2, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTR, -, hSC2, -, -, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  haveI := hTR
  haveI := hSC2
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af F ⊗[F] E))
  haveI : SecondCountableTopology (HermR (Af F) σ n) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (HermR (Af F) σ n) := inferInstance
  obtain ⟨U, hUo, hUc, hUp⟩ := GlobalTheory.T.finite_adelic_integral_invariant_open_subgroup F E σ hCM M J n ψ hψ μ hμ Q hQ
  obtain ⟨C, t, ht, hb⟩ := GlobalTheory.T.finite_local_orbital_integral_bounded F E σ hCM M J hJ n ψ hψ μ hμ Q hQ
  obtain ⟨τ, hτ, hc⟩ := GlobalTheory.T.scaled_integral_hermitian_in_open_subgroup F E σ hCM n U hUo t ht
  have hs : (n : ℝ) < (M : ℝ) / 2 := by
    have : ((2 * n : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hn
    push_cast at this
    linarith
  have hsum := GlobalTheory.T.summable_periodic_bound_by_denominator F E σ n (U.comap (hermIn (Af F) σ n)) t ht τ hτ hc
    (fun c => ‖starLoc (Af F) σ J (psiFin F ψ) μ Q (hermIn (Af F) σ n c)‖) (fun _ => norm_nonneg _)
    (fun c l hl => by
      show ‖_‖ = ‖_‖
      rw [map_add, hUp _ _ hl]) C ((M : ℝ) / 2) hb (GlobalTheory.T.summable_denominator_power_of_lt F E σ hCM n _ hs)
  exact GlobalTheory.T.summable_over_lattice_quotient_locally_constant _ _ ν U hUo hUc (hermIn (Af F) σ n) (GlobalTheory.T.hermitian_finite_adeles_dense_rational F E σ hCM n U hUo) _ (fun g u hu => hUp g u hu) hsum

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_siegel_weil_integral_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Af F) σ n), ν.IsAddHaarMeasure →
  ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    Integrable (starLoc (Af F) σ J (psiFin F ψ) μ Q) ν := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.integrable_starLoc_fin
end
