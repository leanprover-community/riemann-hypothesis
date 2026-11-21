import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpace

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  first | exact @GlobalTheory.NabStab.polyAction_mem_locP_nabStd | exact GlobalTheory.NabStab.polyAction_mem_locP_nabStd | (intros; apply GlobalTheory.NabStab.polyAction_mem_locP_nabStd <;> assumption)
end

section
namespace GlobalTheory.TestLat

theorem weyl_rowAct_mem_of_isUnit_det :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
      ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g.det →
        ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν,
          Formalism.GradedWeylDivisibility.rowAct R g f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν := by
  intro R _ _ n ν _ g hg f hf
  exact Formalism.UG.P.wlocal_main (le_refl n) ν n 0 (by omega) g g⁻¹ (Matrix.nonsing_inv_mul g hg)
    (fun _ _ hj => absurd hj (Nat.not_lt_zero _)) f hf

end GlobalTheory.TestLat
end

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.WeylLocal

variable {K : Type} [Field K] [NumberField K]

abbrev locRing (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors

theorem mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ w.asIdeal.primeCompl),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

theorem isLocalRing_locRing (w : HeightOneSpectrum (𝓞 K)) : IsLocalRing (locRing w) :=
  IsLocalization.AtPrime.isLocalRing (locRing w) w.asIdeal

theorem ne_zero_of_mem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∈ w.asIdeal.primeCompl) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have h0 : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])
  exact hs (by rw [h0]; exact w.asIdeal.zero_mem)

theorem smul_mem_locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {a : K} (ha : a ∈ locRing w) {y : Z}
    (hy : y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) : a • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
  obtain ⟨s, hs, hsy⟩ := hy
  obtain ⟨r, t, ht, hat⟩ := (mem_locRing w a).mp ha
  refine ⟨t * s, mul_mem ht hs, ?_⟩
  have ht0 := ne_zero_of_mem w ht
  have he : (t * s) • (a • y) = r • (s • y) := by
    rw [hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
      ← algebraMap_smul K s, smul_smul, smul_smul]
    congr 1
    rw [map_mul]
    field_simp
  rw [he]
  exact M.smul_mem r hsy

theorem le_locP {Z : Type} [AddCommGroup Z] [Module (𝓞 K) Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {y : Z} (hy : y ∈ M) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M :=
  ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hy⟩

theorem coord_of_mem_colLat {n : ℕ} (B : GL (Fin n) K) {x : Fin n → K} (hx : x ∈ colLat B) (i : Fin n) :
    (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have h : (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        fun a => (B : Matrix (Fin n) (Fin n) K) a j) i =
        (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) i j := rfl
    rw [h, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ hy

theorem coord_of_mem_locP {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K) {x : Fin n → K}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B)) (i : Fin n) :
    (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) i ∈ locRing w := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨a, ha⟩ := coord_of_mem_colLat B hsx i
  rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def] at ha
  refine (mem_locRing w _).mpr ⟨a, s, hs, ?_⟩
  have hs0 := ne_zero_of_mem w hs
  rw [ha]
  field_simp

theorem entries_mem {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (h : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B')) (i j : Fin n) :
    ((B⁻¹ * B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ locRing w := by
  have hx : (fun a => (B' : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) := by
    rw [h]
    exact le_locP w _ (Submodule.subset_span ⟨j, rfl⟩)
  exact coord_of_mem_locP w B hx i

theorem exists_lift {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ g₀ : Matrix (Fin n) (Fin n) (locRing w), IsUnit g₀.det ∧
      g₀.map (algebraMap (locRing w) K) = (g : Matrix (Fin n) (Fin n) K) := by
  have h1 := entries_mem w 1 g h
  have h2 := entries_mem w g 1 h.symm
  rw [inv_one, one_mul] at h1
  rw [mul_one] at h2
  let g₀ : Matrix (Fin n) (Fin n) (locRing w) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let g₁ : Matrix (Fin n) (Fin n) (locRing w) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have e0 : g₀.map (algebraMap (locRing w) K) = (g : Matrix (Fin n) (Fin n) K) := rfl
  have e1 : g₁.map (algebraMap (locRing w) K) = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  refine ⟨g₀, ?_, e0⟩
  have hm : g₀ * g₁ = 1 := by
    apply Matrix.map_injective (f := algebraMap (locRing w) K) Subtype.val_injective
    simp only
    rw [Matrix.map_mul, e0, e1, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_right_inverse hm

theorem map_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (ν : Fin n → ℕ)
    {f : MvPolynomial (Fin n × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν) :
    map φ f ∈ Formalism.GradedWeylDivisibility.weyl S n n le_rfl ν := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem toK_apply {σ : Type} (f : MvPolynomial σ (𝓞 K)) : toK K σ f = map (algebraMap (𝓞 K) K) f := rfl

theorem map_weyl_mem_locP (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ν : Fin n → ℕ)
    {f : MvPolynomial (Fin n × Fin n) (locRing w)} (hf : f ∈ Formalism.GradedWeylDivisibility.weyl (locRing w) n n le_rfl ν) :
    map (algebraMap (locRing w) K) f ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K _)) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine le_locP w _ ⟨_, Submodule.subset_span ⟨v, rfl⟩, ?_⟩
    simp only
    rw [toK_apply, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map,
      ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact smul_mem_locP w _ a.2 hy

theorem sqAct_mem_locP (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (lam : DomWeight n) (g : GL (Fin n) K)
    (h : IsBasisAt w (colLat 1) g) {f : MvPolynomial (Fin n × Fin n) K}
    (hf : f ∈ (delSq (𝓞 K) n lam).map (toK K _)) :
    sqAct K n lam g f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n lam).map (toK K _)) := by
  obtain ⟨g₀, hu, e0⟩ := exists_lift w g h
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  haveI := isLocalRing_locRing w
  have h1 := map_mem_weyl (algebraMap (𝓞 K) (locRing w)) lam.natW hf₀
  have h2 := GlobalTheory.TestLat.weyl_rowAct_mem_of_isUnit_det (locRing w) n lam.natW (natW_antitone lam) g₀ᵀ (by rwa [Matrix.det_transpose]) _ h1
  have h3 := map_weyl_mem_locP w lam.natW h2
  rw [Formalism.GradedWeylDivisibility.ldtwist_map_rowAct, map_map, ← IsScalarTower.algebraMap_eq, Matrix.transpose_map, e0] at h3
  refine smul_mem_locP w _ ?_ h3
  have hd : Matrix.GeneralLinearGroup.det g = Units.map (algebraMap (locRing w) K).toMonoidHom hu.unit := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← e0, Units.coe_map, IsUnit.unit_spec]
    exact ((algebraMap (locRing w) K).map_det g₀).symm
  rw [detPow, hd, ← map_zpow, Units.coe_map]
  exact Subtype.property _

theorem ten_mem_locP (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] {n : ℕ}
    (M : ι → Submodule (𝓞 K) (MvPolynomial (Fin n × Fin n) K)) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (M τ)) :
    ten f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.GradedWeylDivisibility.tensorLat (𝓞 K) K M) := by
  choose s hs hsf using hf
  refine ⟨∏ τ, s τ, prod_mem fun τ _ => hs τ, Submodule.subset_span ⟨fun τ => s τ • f τ, hsf, ?_⟩⟩
  rw [ten, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact ((Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap.map_smul_of_tower (s τ) (f τ)).symm

theorem polyAction_mem_locP_delStd : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  intro K _ _ ι _ n lam w g hg F hF
  have key : ∀ P ∈ delStd K lam, actP lam g P ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      have h := actTen K ι n lam g f
      rw [ten] at h
      rw [h]
      exact ten_mem_locP w _ _ fun τ => sqAct_mem_locP w (lam τ) (g τ) (hg τ) (hf τ)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ hy
  obtain ⟨s, hs, hsF⟩ := hF
  obtain ⟨t, ht, h⟩ := key _ hsF
  rw [LinearMap.map_smul_of_tower] at h
  exact ⟨t * s, mul_mem ht hs, (mul_smul t s (actP lam g F)).symm ▸ h⟩

end GlobalTheory.TestLat.WeylLocal
end
end

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyAction_mem_locP_delStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  first | exact @GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd | exact GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd | (intros; apply GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd <;> assumption)
end

section
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.TestLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem isBasisAt_inv_mul (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (B B' : GL (Fin n) K)
    (h : IsBasisAt w M B) (h' : IsBasisAt w M B') : IsBasisAt w (colLat 1) (B'⁻¹ * B) := by
  rw [← isBasisAt_gLat w B', ← colLat_mul, mul_one, mul_inv_cancel_left]
  exact h'.symm.trans h

theorem indep_of_stable (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (T : Submodule (𝓞 K) (Pol K ι n))
    (hT : ∀ g : ι → GL (Fin n) K, (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ T, actP lam g F ∈ T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K)
    (h : ∀ τ, IsBasisAt w (M τ) (B τ)) (h' : ∀ τ, IsBasisAt w (M τ) (B' τ)) (F : Pol K ι n) :
    actP lam B⁻¹ F ∈ T ↔ actP lam B'⁻¹ F ∈ T := by
  constructor
  · intro hF
    have := hT (B'⁻¹ * B) (fun τ => isBasisAt_inv_mul w (M τ) (B τ) (B' τ) (h τ) (h' τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this
  · intro hF
    have := hT (B⁻¹ * B') (fun τ => isBasisAt_inv_mul w (M τ) (B' τ) (B τ) (h' τ) (h τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this

theorem nabIndep_and_delIndep : NabIndep ∧ DelIndep :=
  ⟨fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt K ι n lam w) M B B' h h' F,
    fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (GlobalTheory.T.polyAction_mem_locP_delStd_of_isBasisAt K ι n lam w) M B B' h h' F⟩

end GlobalTheory.TestLat
end

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nabIndep_and_delIndep_local_conditions : NabIndep ∧ DelIndep := by
  atlas_forward_decl GlobalTheory.TestLat.nabIndep_and_delIndep
end

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TransLoc

section General

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem_of_mem_span (N : Submodule (𝓞 K) V) {x : V} (hx : x ∈ Submodule.span K (N : Set V)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ N := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (N : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩

theorem exists_smul_le_of_fg (N N' : Submodule (𝓞 K) V) (hfg : N'.FG)
    (h : ∀ x ∈ N', x ∈ Submodule.span K (N : Set V)) : ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ x ∈ N', a • x ∈ N := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  have h1 : ∀ y : s, ∃ a : 𝓞 K, a ≠ 0 ∧ a • (y : V) ∈ N := fun y =>
    exists_smul_mem_of_mem_span N (h y (Submodule.subset_span y.2))
  choose a ha0 ha using h1
  refine ⟨∏ y, a y, Finset.prod_ne_zero_iff.mpr fun y _ => ha0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨y, hy⟩ : s)), mul_smul]
    exact N.smul_mem _ (ha ⟨y, hy⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact N.smul_mem _ hy

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem mem_of_forall_locP (N : Submodule (𝓞 K) V) {x : V}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N) : x ∈ N := by
  by_contra hx
  have hI : N.comap (LinearMap.toSpanSingleton (𝓞 K) V x) ≠ ⊤ := by
    intro h1
    have : (1 : 𝓞 K) ∈ N.comap (LinearMap.toSpanSingleton (𝓞 K) V x) := h1 ▸ Submodule.mem_top
    exact hx (by simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hm0⟩
  exact hs (hle (by simpa using hsx))

omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem localization_le_of_smul_mem (w : HeightOneSpectrum (𝓞 K)) {N N' : Submodule (𝓞 K) V} {a : 𝓞 K} (ha : a ∉ w.asIdeal)
    (h : ∀ x ∈ N', a • x ∈ N) : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨a * s, Submonoid.mul_mem _ ha hs, by rw [mul_smul]; exact h _ hx⟩

theorem exists_dvd_mul {w w' : HeightOneSpectrum (𝓞 K)} (hw : w' ≠ w) {d : 𝓞 K} (hd : d ≠ 0) :
    ∃ s ∉ w.asIdeal, ∃ u ∉ w'.asIdeal, d ∣ u * s := by
  classical
  have hI : Ideal.span {d} ≠ ⊥ := by simpa using hd
  obtain ⟨Q, hQ, hdQ⟩ := Ideal.eq_prime_pow_mul_coprime hI w'.asIdeal (hpm := w'.isMaximal)
  set k := Multiset.count w'.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {d}))
  have h1 : ¬ w'.asIdeal ^ k ≤ w.asIdeal := by
    intro h
    have h2 := Ideal.IsPrime.le_of_pow_le (hP := w.isPrime) h
    exact hw (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top h2))
  have h2 : ¬ Q ≤ w'.asIdeal := by
    intro h
    rw [sup_eq_left.mpr h] at hQ
    exact w'.isPrime.ne_top hQ
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp h1
  obtain ⟨u, hu, hu'⟩ := SetLike.not_le_iff_exists.mp h2
  refine ⟨s, hs', u, hu', ?_⟩
  rw [← Ideal.mem_span_singleton, hdQ, mul_comm u]
  exact Ideal.mul_mem_mul hs hu

end General

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem span_colLat_one : Submodule.span K (colLat (1 : GL (Fin n) K) : Set (Fin n → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  refine Submodule.subset_span ⟨j, ?_⟩
  funext a
  simp [Matrix.one_apply, Pi.single_apply]

theorem exists_isBasisAt_one (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 K), a ∉ w.asIdeal → IsBasisAt w M 1 := by
  obtain ⟨a, ha0, ha⟩ := exists_smul_le_of_fg (colLat (1 : GL (Fin n) K)) M hM.fg
    (fun x _ => by rw [span_colLat_one]; trivial)
  obtain ⟨b, hb0, hb⟩ := exists_smul_le_of_fg M (colLat (1 : GL (Fin n) K))
    (Submodule.fg_span (Set.finite_range _)) (fun x _ => by rw [hM.span_eq_top]; trivial)
  refine ⟨a * b, mul_ne_zero ha0 hb0, fun w hw => le_antisymm ?_ ?_⟩
  · exact localization_le_of_smul_mem w (fun h => hw (w.asIdeal.mul_mem_right _ h)) ha
  · exact localization_le_of_smul_mem w (fun h => hw (w.asIdeal.mul_mem_left _ h)) hb

theorem polyAction_smul_int (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (a : 𝓞 K) (F : Pol K ι n) :
    actP lam g (a • F) = a • actP lam g F :=
  ((actP lam g).restrictScalars (𝓞 K)).map_smul a F

theorem mem_VV_of_locP (lam : ι → DomWeight n) {T : Submodule (𝓞 K) (Pol K ι n)}
    (hT : Submodule.span K (T : Set (Pol K ι n)) = VV K lam) (w : HeightOneSpectrum (𝓞 K))
    (B : ι → GL (Fin n) K) {F : Pol K ι n} (hF : actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) : F ∈ VV K lam := by
  obtain ⟨s, hs, hx⟩ := hF
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    rintro rfl
    exact hs w.asIdeal.zero_mem
  have h1 : algebraMap (𝓞 K) K s • actP lam B⁻¹ F ∈ VV K lam := by
    rw [algebraMap_smul, ← hT]
    exact Submodule.subset_span hx
  have h2 := polyAction_mem_VV lam B (((VV K lam).smul_mem_iff hs0).mp h1)
  rwa [← polyAction_mul, mul_inv_cancel, polyAction_one₂] at h2

theorem mem_map_actP (lam : ι → DomWeight n) (B : ι → GL (Fin n) K) (N : Submodule (𝓞 K) (Pol K ι n))
    (F : Pol K ι n) : F ∈ N.map ((actP lam B).restrictScalars (𝓞 K)) ↔ actP lam B⁻¹ F ∈ N := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show actP lam B⁻¹ (actP lam B y) ∈ _
    rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    show actP lam B (actP lam B⁻¹ F) = F
    rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]

theorem mem_transLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (F : Pol K ι n) :
    F ∈ transLat lam T M ↔ ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K),
      (∀ τ, IsBasisAt w (M τ) (B τ)) → actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
  simp only [transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

theorem transLat_colLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) (B : ι → GL (Fin n) K)
    (hI : ∀ (w : HeightOneSpectrum (𝓞 K)) (B' : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat (B τ)) (B' τ)) →
      ∀ F : Pol K ι n, actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T → actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) :
    transLat lam T (fun τ => colLat (B τ)) = T.map ((actP lam B).restrictScalars (𝓞 K)) := by
  ext F
  rw [mem_map_actP, mem_transLat]
  constructor
  · intro h
    exact mem_of_forall_locP T fun w => h w B fun _ => rfl
  · intro h w B' hB'
    exact hI w B' hB' F ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact h⟩

theorem locP_transLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (hT : Submodule.span K (T : Set (Pol K ι n)) = VV K lam)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ))
    (hI : ∀ (w : HeightOneSpectrum (𝓞 K)) (B B' : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      (∀ τ, IsBasisAt w (M τ) (B' τ)) → ∀ F : Pol K ι n,
      (actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T ↔ actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T))
    (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K) (hB : ∀ τ, IsBasisAt w (M τ) (B τ)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T M) =
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T).map ((actP lam B).restrictScalars (𝓞 K)) := by
  classical
  ext F
  rw [mem_map_actP]
  constructor
  · rintro ⟨s, hs, hF⟩
    obtain ⟨t, ht, h⟩ := (mem_transLat lam T M _).mp hF w B hB
    refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
    rw [mul_smul]
    exact (congrArg (fun x => t • x ∈ T) (polyAction_smul_int lam B⁻¹ s F)).mp h
  · intro hF
    have hV : F ∈ VV K lam := mem_VV_of_locP lam hT w B hF
    have hd : ∀ g : ι → GL (Fin n) K, ∃ d : 𝓞 K, d ≠ 0 ∧ d • actP lam g F ∈ T := fun g =>
      exists_smul_mem_of_mem_span T (hT ▸ polyAction_mem_VV lam g hV)
    choose a ha0 ha using fun τ => exists_isBasisAt_one (M τ) (hM τ)
    obtain ⟨d, hd0, hdF⟩ := hd (1 : ι → GL (Fin n) K)⁻¹
    have hc0 : Ideal.span {d * ∏ τ, a τ} ≠ 0 := by
      simpa using mul_ne_zero hd0 (Finset.prod_ne_zero_iff.mpr fun τ _ => ha0 τ)
    have hfin := Ideal.finite_factors hc0
    have hloc : ∀ w' : HeightOneSpectrum (𝓞 K), ∃ s ∉ w.asIdeal, ∀ B' : ι → GL (Fin n) K,
        (∀ τ, IsBasisAt w' (M τ) (B' τ)) → s • actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal T := by
      intro w'
      by_cases hw : w' = w
      · subst hw
        refine ⟨1, (Ideal.ne_top_iff_one _).mp w'.isPrime.ne_top, fun B' hB' => ?_⟩
        exact Submodule.smul_mem _ _ ((hI w' B B' hB hB' F).mp hF)
      by_cases hex : ∃ B₀ : ι → GL (Fin n) K, ∀ τ, IsBasisAt w' (M τ) (B₀ τ)
      · obtain ⟨B₀, hB₀⟩ := hex
        obtain ⟨e, he0, heF⟩ := hd B₀⁻¹
        obtain ⟨s, hs, u, hu, c, hc⟩ := exists_dvd_mul hw he0
        refine ⟨s, hs, fun B' hB' => ?_⟩
        rw [← polyAction_smul_int]
        refine (hI w' B₀ B' hB₀ hB' _).mp ⟨u, hu, ?_⟩
        erw [polyAction_smul_int, ← mul_smul, hc, mul_comm, mul_smul]
        exact T.smul_mem _ heF
      · exact ⟨1, (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top, fun B' hB' => absurd ⟨B', hB'⟩ hex⟩
    choose s hs hsF using hloc
    refine ⟨∏ w' ∈ hfin.toFinset, s w', Submonoid.prod_mem _ fun w' _ => hs w', ?_⟩
    rw [mem_transLat]
    intro w' B' hB'
    erw [polyAction_smul_int]
    by_cases hw' : w' ∈ hfin.toFinset
    · erw [← Finset.prod_erase_mul _ _ hw', mul_smul]
      exact Submodule.smul_mem _ _ (hsF w' B' hB')
    · refine Submodule.smul_mem _ _ ?_
      have hn : d * ∏ τ, a τ ∉ w'.asIdeal := by
        simpa [Ideal.dvd_span_singleton] using hw'
      have h1 : ∀ τ, IsBasisAt w' (M τ) ((1 : ι → GL (Fin n) K) τ) := fun τ =>
        ha τ w' fun h => hn (w'.asIdeal.mul_mem_left _
          (w'.asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem a (Finset.mem_univ τ)) h))
      exact (hI w' 1 B' h1 hB' F).mp ⟨d, fun h => hn (w'.asIdeal.mul_mem_right _ h), hdF⟩

theorem nabDelLoc_free_leVV : NabDelLoc ∧ NabDelFree ∧ NabLeVV := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ _ ι _ n lam M hM w B hB
    exact ⟨locP_transLat lam _ (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).2.2.1 M hM
        (fun w B B' => GlobalTheory.T.nabIndep_and_delIndep_local_conditions.1 K ι n lam w M B B') w B hB,
      locP_transLat lam _ (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).2.2.2 M hM
        (fun w B B' => GlobalTheory.T.nabIndep_and_delIndep_local_conditions.2 K ι n lam w M B B') w B hB⟩
  · intro K _ _ ι _ n lam B
    exact ⟨transLat_colLat lam _ B fun w B' hB' F =>
        (GlobalTheory.T.nabIndep_and_delIndep_local_conditions.1 K ι n lam w _ B B' (fun _ => rfl) hB' F).mp,
      transLat_colLat lam _ B fun w B' hB' F =>
        (GlobalTheory.T.nabIndep_and_delIndep_local_conditions.2 K ι n lam w _ B B' (fun _ => rfl) hB' F).mp⟩
  · intro K _ _ ι _ n lam M hM F hF
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
    have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
    let w : HeightOneSpectrum (𝓞 K) := ⟨m, hm.isPrime, hm0⟩
    choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
    exact mem_VV_of_locP lam (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).2.2.1 w B ((mem_transLat lam _ M F).mp hF w B hB)

end GlobalTheory.TransLoc
end
