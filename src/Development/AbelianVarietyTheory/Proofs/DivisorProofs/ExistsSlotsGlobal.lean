import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGapNonemptyAndRecordNonempty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwFonCmpTies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAddPiSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsOverLettersOfCrysWith
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeightsFromJumpsIff
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixFrameAtPrimitiveRootFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankReducedLetterMatrixEqRankModMaximal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
import Development.AbelianVarietyTheory.Definitions.Divisors.HeightTrivialParameterEqZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

section
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachFrame

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f) {T : LocLat G Qp LL O} {n : ℕ}

theorem γD_smulA (g : W.Gam) (a : LetA O f) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O f) W.EE a) x
  rwa [algebraMap_smul, W.γE_ext, algebraMap_smul] at this

theorem coe_eq_sum (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (y : ↥(W.N T)) :
    (y : W.DD T) = ∑ m, b.repr y m • (b m : W.DD T) := by
  have h1 := congrArg Subtype.val (b.sum_repr y)
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h1
  exact h1.symm

theorem coord_fixed (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) (hy : W.γD T δ (y : W.DD T) = y) (m : Fin n) :
    W.γA δ (b.repr y m) = b.repr y m := by
  have e : ∑ m, W.γA δ (b.repr y m) • b m = y := by
    apply Subtype.ext
    have h1 : W.γD T δ (y : W.DD T) = ∑ m, W.γA δ (b.repr y m) • (b m : W.DD T) := by
      conv_lhs => rw [coe_eq_sum W b y, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [γD_smulA, (hb m).2 δ hδ]
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    exact h1.symm.trans hy
  have h2 := congrFun (b.repr_sum_self fun m => W.γA δ (b.repr y m)) m
  rw [e] at h2
  exact h2.symm

variable (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]

theorem exists_inc (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (hy : ∀ δ ∈ W.DelF, W.γD T δ (y : W.DD T) = y) (m : Fin n) (i : ZMod f) :
    ∃ z, inc l O z = b.repr y m i :=
  hI _ fun δ hδ => congrFun (coord_fixed W b hb y δ hδ (hy δ hδ) m) i

theorem exists_phi_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (hφ : ∀ x ∈ W.N T, W.φD T x ∈ W.N T) :
    ∃ Pm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.φD T (b k : W.DD T) =
      ∑ m, (fun i => inc l O (Pm i m k) : LetA O f) • (b m : W.DD T) := by
  have h : ∀ i m k, ∃ z, inc l O z = b.repr ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩ m i := fun i m k =>
    exists_inc W l hI b hb _ (fun δ hδ => by
      change W.γD T δ (W.φD T (b k : W.DD T)) = W.φD T (b k : W.DD T)
      rw [← W.φγ_comm, (hb k).2 δ hδ]) m i
  choose Pm hPm using h
  refine ⟨fun i => Matrix.of (Pm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hPm i m k).symm

theorem exists_gam_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (γ : W.Gam) :
    ∃ Dm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.γD T γ (b k : W.DD T) =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • Dm i) m k) : LetA O f) • (b m : W.DD T) := by
  have hγ : ∀ k, W.γD T γ (b k : W.DD T) ∈ W.N T := fun k => W.N_Γ T γ _ (b k).2
  have h : ∀ i m k, ∃ d : O⟦X⟧, inc l O ((1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k + X * d) =
      b.repr ⟨W.γD T γ (b k : W.DD T), hγ k⟩ m i := by
    intro i m k
    obtain ⟨z, hz⟩ := exists_inc W l hI b hb ⟨W.γD T γ (b k : W.DD T), hγ k⟩ (fun δ hδ => by
      change W.γD T δ (W.γD T γ (b k : W.DD T)) = W.γD T γ (b k : W.DD T)
      rw [← W.γD_mul, mul_comm, W.γD_mul, (hb k).2 δ hδ]) m i
    obtain ⟨y, hy, e⟩ := W.N_π T γ _ (b k).2
    have e1 : (⟨W.γD T γ (b k : W.DD T), hγ k⟩ : ↥(W.N T)) = b k + (letπ : LetA O f) • (⟨y, hy⟩ : ↥(W.N T)) :=
      Subtype.ext (eq_add_of_sub_eq' e)
    have e2 : constantCoeff (z - (1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k) = 0 := by
      rw [map_sub, ← (pi0Subst_laws_hold l O).2.2.2.2.2.1 z, hz, e1, map_add, map_smul, b.repr_self]
      by_cases hmk : m = k
      · subst hmk
        simp [letπ]
      · simp [letπ, hmk, Finsupp.single_eq_of_ne hmk]
    obtain ⟨d, hd⟩ := X_dvd_iff.2 e2
    exact ⟨d, by rw [← hd, add_sub_cancel, hz]⟩
  choose Dm hDm using h
  refine ⟨fun i => Matrix.of (Dm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.γD T γ (b k : W.DD T), hγ k⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hDm i m k).symm

theorem mem_of_letters (x : W.DD T) (h : ∀ i, (letE i : LetA O f) • x ∈ W.N T) : x ∈ W.N T := by
  haveI := GlobalTheory.WachLettersCompare.neZero_letters W
  have e : (∑ i, letE i : LetA O f) = 1 := Finset.univ_sum_single (1 : LetA O f)
  rw [← one_smul (LetA O f) x, ← e, Finset.sum_smul]
  exact Submodule.sum_mem _ fun i _ => h i

theorem phi_mem (hH : GlobalTheory.WachUse.Heights W) (U : ZMod f → Multiset ℤ)
    (hU : GlobalTheory.AdmLoc.CrysWith PD W.emb T.ρ U) (hpos : ∀ i, ∀ u ∈ U i, 0 ≤ u) :
    ∀ x ∈ W.N T, W.φD T x ∈ W.N T := by
  intro x hx
  refine mem_of_letters W _ fun i => ?_
  have := (hH T U (fun _ => 0) (fun i => ((U i).map Int.toNat).sum) hU (fun i u hu => ?_) i).1 x hx
  · simpa using this
  · refine ⟨by simpa using hpos i u hu, ?_⟩
    have h1 : u.toNat ≤ ((U i).map Int.toNat).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hu)
    exact (Int.self_le_toNat u).trans (by exact_mod_cast h1)

end Generic

theorem exists_rem {l : ℕ} [Fact l.Prime] (LL : FinExt l) (g : (↥(OL LL))⟦X⟧) :
    ∃ a : ↥(OL LL), (X - C (l : ↥(OL LL))) ∣ g - C a := by
  obtain ⟨_, hc, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨g₁, a, e⟩ := (linear_division_holds ↥(OL LL) (maximalIdeal ↥(OL LL)) (l : ↥(OL LL))
    ((mem_maximalIdeal _).2 hl)).1 g
  exact ⟨a, g₁, by rw [e, add_sub_cancel_right]⟩

theorem exists_frame : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n : ℕ), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) → Module.finrank ↥(OL LL) ↥T.L.T = n → ∀ γ : ((HW l).W K 1 LL hA.2.2).Gam, ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N := by
  intro D HW F Cm l _ K LL hA T U n hU hpos hn γ
  have hR := GlobalTheory.T.wachRingFacts_unramified_levelOne (HW l) K LL hA
  have hJ := (GlobalTheory.HeightsClauseCompare.heights_iff D HW F Cm).2
    ⟨GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm, GlobalTheory.NL.SandJumps.main D HW F Cm⟩
  have hH := GlobalTheory.WachUse.HeightsProof.heights_of_caseA (D.locA l) (HW l) (F l) (Cm l) ⟨D.locT l⟩
    ((GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff l _ _ _ _ _).2 (hJ l)) K LL hA
  obtain ⟨b₀⟩ := GlobalTheory.WachFree.wach_free (D.loc l) (HW l) K 1 LL hA.2.2 T hU.1
  obtain ⟨b, hb⟩ := GlobalTheory.WachTie.exists_invariant_basis _ T hR.2.2.2.2.2 ⟨b₀.reindex (finCongr hn)⟩
  obtain ⟨Pm, hP⟩ := exists_phi_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb (phi_mem _ hH U hU hpos)
  obtain ⟨Dm, hD⟩ := exists_gam_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb γ
  choose Th hTh using fun i a c => exists_rem LL (Dm i a c)
  exact ⟨b, ⟨Pm, Dm, fun i => Matrix.of (Th i)⟩, hb, hP, hD, hTh⟩

end GlobalTheory.WachFrame

end
end

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_wachModule_basis_of_nonneg_jumps : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n : ℕ), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) → Module.finrank ↥(OL LL) ↥T.L.T = n → ∀ γ : ((HW l).W K 1 LL hA.2.2).Gam, ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N := by
  atlas_forward_decl GlobalTheory.WachFrame.exists_frame
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace.FrameHeight

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f)

theorem φD_smul_A (T : LocLat G Qp LL O) (a : LetA O f) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O f) W.EE a) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul] at this

theorem φpull_le_span {n : ℕ} (T : LocLat G Qp LL O) (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) :
    W.φpull T ≤ Submodule.span (LetA O f) (Set.range fun j => W.φD T (b j : W.DD T)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at e
  rw [← e, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [φD_smul_A]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_inv {n : ℕ} (T : LocLat G Qp LL O) (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T))
    (PA : Matrix (Fin n) (Fin n) (LetA O f))
    (hφ : ∀ k, W.φD T (b k : W.DD T) = ∑ m, PA m k • (b m : W.DD T)) (h : ℕ) (i : ZMod f)
    (h5 : ∀ y ∈ W.Nl T i, W.Q ^ h • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1))) :
    ∃ Qm : Matrix (Fin n) (Fin n) (PowerSeries O),
      (PA.map fun a => a i) * Qm = (W.Q i ^ h) • (1 : Matrix (Fin n) (Fin n) (PowerSeries O)) := by
  have hsp : ∀ k, ∃ c : Fin n → LetA O f,
      ∑ j, c j • W.φD T (b j : W.DD T) = W.Q ^ h • (letE i : LetA O f) • (b k : W.DD T) := by
    intro k
    have hy : (letE i : LetA O f) • (b k : W.DD T) ∈ W.Nl T i :=
      Submodule.mem_map_of_mem (b k).2
    have h1 := h5 _ hy
    have hle : Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1)) ≤ W.φpull T :=
      Submodule.span_mono (Set.image_mono (by
        rintro _ ⟨x, hx, rfl⟩
        exact (W.N T).smul_mem _ hx))
    exact (Submodule.mem_span_range_iff_exists_fun (LetA O f)).1 (φpull_le_span W T b (hle h1))
  choose c hc using hsp
  have hli : LinearIndependent (LetA O f) fun m => (b m : W.DD T) :=
    b.linearIndependent.map' (W.N T).subtype (Submodule.ker_subtype _)
  have key : ∀ k m, ∑ j, c k j * PA m j = if m = k then W.Q ^ h * (letE i : LetA O f) else 0 := by
    intro k
    have e1 : ∑ m, (∑ j, c k j * PA m j - if m = k then W.Q ^ h * (letE i : LetA O f) else 0) •
        (b m : W.DD T) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, Finset.sum_smul, mul_smul]
      rw [← hc k, sub_eq_zero, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hφ, Finset.smul_sum]
    intro m
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ e1 m)
  refine ⟨Matrix.of fun j k => c k j i, ?_⟩
  refine Matrix.ext fun m k => ?_
  have e2 := congrFun (key k m) i
  simp only [Finset.sum_apply, Pi.mul_apply] at e2
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [show (∑ j, PA m j i * c k j i) = ∑ j, c k j i * PA m j i from
    Finset.sum_congr rfl fun j _ => mul_comm _ _, e2]
  by_cases hmk : m = k
  · simp [hmk, letE]
  · simp [hmk]

end Generic

end GlobalTheory.WachPlace.FrameHeight

namespace GlobalTheory.WachPlace.FrameHeight

theorem frame_height : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n h : ℕ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ (h : ℤ)) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → ∀ i, ∃ Q : Mx (PowerSeries ↥(OL LL)) n n, (N.P i).map (inc l ↥(OL LL)) * Q = (q l ↥(OL LL) ^ h) • (1 : Mx (PowerSeries ↥(OL LL)) n n) := by
  intro D HW F Cm l _ K LL hA T U n h γ b N hU hb hfr i
  have hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet ((HW l).W K 1 LL hA.2.2) T (fun _ => 0) (fun _ => h) := by
    intro τ i' hτ a ha
    haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1
    have h1 := (GlobalTheory.Per.JumpMult.jump_iff_of_finite ((D.loc l).PD K) T.ρ τ a).2.2.1 ha
    rw [hU.2 i' τ (fun x => DFunLike.congr_fun hτ x) a] at h1
    have h2 := hb i' a (Multiset.count_ne_zero.1 (by exact_mod_cast h1))
    exact ⟨by simpa using h2.1, h2.2⟩
  have h5 := (GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm l K 1 LL hA.2.2 T (fun _ => 0) (fun _ => h)
    hU.1 hJ).2.1 i
  obtain ⟨Qm, hQm⟩ := exists_inv ((HW l).W K 1 LL hA.2.2) T b
    (fun m k => fun i => inc l ↥(OL LL) (N.P i m k)) hfr.2.1 h i h5
  have hq : ((HW l).W K 1 LL hA.2.2).Q i = q l ↥(OL LL) := by
    have e1 : ((HW l).W K 1 LL hA.2.2).Q = ((HW l).W K 1 LL hA.2.2).q := by
      unfold LocWach.Q
      rw [(HW l).W_s K 1 LL hA.2.2]
      rfl
    rw [e1]
    change ((HW l).W K 1 LL hA.2.2).q₀ = q l ↥(OL LL)
    have e2 := ((HW l).W K 1 LL hA.2.2).q₀_def
    rw [(D.loc l).PD_p K, ← (q_multiplicative_holds l ↥(OL LL)).1] at e2
    refine PowerSeries.ext fun j => ?_
    have e3 := congrArg (PowerSeries.coeff (j + 1)) e2
    simpa only [PowerSeries.coeff_succ_X_mul] using e3
  refine ⟨Qm, ?_⟩
  rw [← hq]
  exact hQm

end GlobalTheory.WachPlace.FrameHeight

end
end

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusMatrix_cofactor_eq_q_pow_frame : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n h : ℕ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ (h : ℤ)) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → ∀ i, ∃ Q : Mx (PowerSeries ↥(OL LL)) n n, (N.P i).map (inc l ↥(OL LL)) * Q = (q l ↥(OL LL) ^ h) • (1 : Mx (PowerSeries ↥(OL LL)) n n) := by
  atlas_forward_decl GlobalTheory.WachPlace.FrameHeight.frame_height
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachMap

section Gen

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M} {n : ℕ}

theorem coeff_unique (b : Module.Basis (Fin n) R S) {c d : Fin n → R}
    (h : ∑ j, c j • (b j : M) = ∑ j, d j • (b j : M)) : c = d := by
  have h' : ∑ j, c j • b j = ∑ j, d j • b j := Subtype.ext (by simpa using h)
  exact (b.repr_sum_self c).symm.trans ((congrArg (fun y => ⇑(b.repr y)) h').trans (b.repr_sum_self d))

theorem exists_coeff (b : Module.Basis (Fin n) R S) {x : M} (hx : x ∈ S) :
    ∃ c : Fin n → R, x = ∑ j, c j • (b j : M) := by
  refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at e
  exact e.symm

theorem sum_smul_sum {m : ℕ} (a : Fin m → R) (B : Fin m → Fin n → R) (e : Fin n → M) :
    ∑ k, a k • ∑ j, B k j • e j = ∑ j, (∑ k, a k * B k j) • e j := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

end Gen

def incHom (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] : O⟦X⟧ →+* O⟦X⟧ where
  toFun := inc l O
  map_one' := by simpa using (pi0Subst_laws_hold l O).2.2.1 1
  map_mul' := (pi0Subst_laws_hold l O).2.1
  map_zero' := by simpa using (pi0Subst_laws_hold l O).2.2.1 0
  map_add' := (pi0Subst_laws_hold l O).1

theorem incHom_apply (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (y : O⟦X⟧) :
    incHom l O y = inc l O y := rfl

theorem map_one_add_X_smul {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (D : Mx R⟦X⟧ m m) :
    (1 + (X : R⟦X⟧) • D).map (PowerSeries.map f) = 1 + (X : S⟦X⟧) • D.map (PowerSeries.map f) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

end GlobalTheory.WachMap

namespace GlobalTheory.WachMap

theorem coeff_comm {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {S' : Submodule R M'} {n n' : ℕ} (e : Fin n → M) (b' : Module.Basis (Fin n') R S')
    (g : M →+ M') (u : M →+ M) (u' : M' →+ M') (σ : R → R) (hg : ∀ (a : R) x, g (a • x) = a • g x)
    (hu' : ∀ (a : R) x, u' (a • x) = σ a • u' x) (hc : ∀ x, g (u x) = u' (g x))
    (p : Fin n → Fin n → R) (p' : Fin n' → Fin n' → R) (A : Fin n' → Fin n → R)
    (hp : ∀ k, u (e k) = ∑ m, p m k • e m) (hp' : ∀ k, u' (b' k : M') = ∑ m, p' m k • (b' m : M'))
    (hA : ∀ k, g (e k) = ∑ m, A m k • (b' m : M')) (j : Fin n') (k : Fin n) :
    ∑ m, p m k * A j m = ∑ m, σ (A m k) * p' j m := by
  have h1 : g (u (e k)) = ∑ j, (∑ m, p m k * A j m) • (b' j : M') := by
    rw [hp k, map_sum]
    simp only [hg, hA]
    exact sum_smul_sum (fun m => p m k) (fun m j => A j m) (fun j => (b' j : M'))
  have h2 : u' (g (e k)) = ∑ j, (∑ m, σ (A m k) * p' j m) • (b' j : M') := by
    rw [hA k, map_sum]
    simp only [hu', hp']
    exact sum_smul_sum (fun m => σ (A m k)) (fun m j => p' j m) (fun j => (b' j : M'))
  have hc' := coeff_unique (c := fun j => ∑ m, p m k * A j m) (d := fun j => ∑ m, σ (A m k) * p' j m) b'
    ((h1.symm.trans (hc (e k))).trans h2)
  exact congrFun hc' j

theorem mul_eq_of_inc {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (hl : l ≠ 2) {n n' : ℕ}
    (P : Mx O⟦X⟧ n n) (P' : Mx O⟦X⟧ n' n') (A A' : Mx O⟦X⟧ n' n)
    (h : ∀ j k, ∑ m, inc l O (P m k) * inc l O (A j m) = ∑ m, inc l O (A' m k) * inc l O (P' j m)) :
    P' * A' = A * P := by
  refine Matrix.ext fun j k => ?_
  apply (pi0Subst_laws_hold l O).2.2.2.2.2.2.2 hl
  simp only [Matrix.mul_apply]
  show incHom l O (∑ m, P' j m * A' m k) = incHom l O (∑ m, A j m * P m k)
  simp only [map_sum, map_mul, incHom_apply]
  rw [Finset.sum_congr rfl fun m _ => mul_comm (inc l O (P' j m)) (inc l O (A' m k)), ← h j k]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {L O : Type} [Field L] [Algebra Qp L]
    [CommRing O] [Algebra O L] [TopologicalSpace L] {v : AddValuation L (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD L O v f)

theorem phiD_smul (T : LocLat G Qp L O) (a : LetA O f) (x : W.DD T) :
    W.φD T (a • x) = letφ W.φ₀ a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]

theorem gamD_smul (T : LocLat G Qp L O) (γ : W.Gam) (a : LetA O f) (x : W.DD T) :
    W.γD T γ (a • x) = letγ (W.γ₀ γ) a • W.γD T γ x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

theorem map_smul_letA {T T' : LocLat G Qp L O} (g : LatHom T.L T'.L) (a : LetA O f)
    (x : W.DD T) : W.map g (a • x) = a • W.map g x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

variable {T T' : LocLat G Qp L O} {n n' : ℕ}
  (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (b' : Module.Basis (Fin n') (LetA O f) ↥(W.N T'))
  {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O]

theorem exists_mapMat (RF : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (g : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (hb' : ∀ k, (b' k : W.DD T') ∈ W.NΔ T') :
    ∃ A : ZMod f → Mx O⟦X⟧ n' n, ∀ k, W.map g (b k : W.DD T) =
      ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T') := by
  classical
  have key : ∀ k, ∃ c : Fin n' → LetA O f, W.map g (b k : W.DD T) = ∑ m, c m • (b' m : W.DD T') ∧
      ∀ m i, ∀ δ ∈ W.DelF, W.γ₀ δ (c m i) = c m i := by
    intro k
    have hk : (b k : W.DD T) ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (b k : W.DD T) = b k := hb k
    have hy : W.map g (b k : W.DD T) ∈ W.N T' := W.map_N g hT hT' _ hk.1
    obtain ⟨c, hc⟩ := exists_coeff b' hy
    refine ⟨c, hc, fun m i δ hδ => ?_⟩
    have hb2 : ∀ m, W.γD T' δ (b' m : W.DD T') = b' m := fun m =>
      (show (b' m : W.DD T') ∈ W.N T' ∧ ∀ δ ∈ W.DelF, W.γD T' δ (b' m : W.DD T') = b' m from hb' m).2 δ hδ
    have e1 : W.γD T' δ (W.map g (b k : W.DD T)) = W.map g (b k : W.DD T) := by
      rw [← W.map_γ, hk.2 δ hδ]
    rw [hc, map_sum] at e1
    simp only [gamD_smul, hb2] at e1
    have e2 := coeff_unique (c := fun m => letγ (W.γ₀ δ) (c m)) (d := c) b' e1
    exact congrFun (congrFun e2 m) i
  choose c hc hinv using key
  refine ⟨fun i m k => Classical.choose (RF (c k m i) (fun δ hδ => hinv k m i δ hδ)), fun k => ?_⟩
  rw [hc k]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  funext i
  exact (Classical.choose_spec (RF (c k m i) (fun δ hδ => hinv k m i δ hδ))).symm

variable {F : Type} [Field F] [Algebra ℤ_[l] F] [CharP F l] (red : O →+* F)

theorem red_frob (hl : l ≠ 2) (hred : ∀ z : ℤ_[l], red (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] F z)
    (hφ : ∀ a, W.φ₀ a = phi l O a) (g : LatHom T.L T'.L) (P : ZMod f → Mx O⟦X⟧ n n) (P' : ZMod f → Mx O⟦X⟧ n' n')
    (A : ZMod f → Mx O⟦X⟧ n' n)
    (hP : ∀ k, W.φD T (b k : W.DD T) = ∑ m, (fun i => inc l O (P i m k) : LetA O f) • (b m : W.DD T))
    (hP' : ∀ k, W.φD T' (b' k : W.DD T') = ∑ m, (fun i => inc l O (P' i m k) : LetA O f) • (b' m : W.DD T'))
    (hA : ∀ k, W.map g (b k : W.DD T) = ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T'))
    (i : ZMod f) :
    (P' i).map (PowerSeries.map red) * ((A (i - 1)).map (PowerSeries.map red)).map (frob0 l) =
      (A i).map (PowerSeries.map red) * (P i).map (PowerSeries.map red) := by
  classical
  have hc := fun j k => coeff_comm (fun k => (b k : W.DD T)) b'
    (W.map g).toAddMonoidHom (W.φD T).toAddMonoidHom (W.φD T').toAddMonoidHom (letφ W.φ₀)
    (fun a x => map_smul_letA W g a x) (fun a x => phiD_smul W T' a x) (fun x => W.map_φ g x)
    (fun m k => (fun i => inc l O (P i m k) : LetA O f)) (fun m k => (fun i => inc l O (P' i m k) : LetA O f))
    (fun m k => (fun i => inc l O (A i m k) : LetA O f)) hP hP' hA j k
  have hred' : ∀ y : O⟦X⟧, (∃ y', phi l O (inc l O y) = inc l O y') ∧
      ∀ y', phi l O (inc l O y) = inc l O y' → PowerSeries.map red y' = frob0 l (PowerSeries.map red y) :=
    frobenius_on_pi0Subst_holds l O F red hl hred
  let Y : Mx O⟦X⟧ n' n := fun m k => Classical.choose (hred' (A (i - 1) m k)).1
  have hY : ∀ m k, phi l O (inc l O (A (i - 1) m k)) = inc l O (Y m k) := fun m k =>
    Classical.choose_spec (hred' (A (i - 1) m k)).1
  have hi : ∀ j k, ∑ m, inc l O (P i m k) * inc l O (A i j m) = ∑ m, inc l O (Y m k) * inc l O (P' i j m) := by
    intro j k
    have e := congrFun (hc j k) i
    rw [Finset.sum_apply, Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun m _ => ?_)
    show W.φ₀ (inc l O (A (i - 1) m k)) * inc l O (P' i j m) = _
    rw [hφ, hY m k]
  have hM : P' i * Y = A i * P i := mul_eq_of_inc hl (P i) (P' i) (A i) Y hi
  have hYr : Y.map (PowerSeries.map red) = ((A (i - 1)).map (PowerSeries.map red)).map (frob0 l) := by
    refine Matrix.ext fun m k => ?_
    exact (hred' (A (i - 1) m k)).2 _ (hY m k)
  rw [← hYr, ← Matrix.map_mul, hM, Matrix.map_mul]

omit [Algebra ℤ_[l] F] in

theorem red_gam (hl : l ≠ 2) (γ : W.Gam) (u : ℤ_[l]) (un : O⟦X⟧) (hun : IsUn l O u un)
    (hγ : ∀ a, W.γ₀ γ a = act l O u a) (g : LatHom T.L T'.L) (D : ZMod f → Mx O⟦X⟧ n n)
    (D' : ZMod f → Mx O⟦X⟧ n' n') (A : ZMod f → Mx O⟦X⟧ n' n)
    (hD : ∀ k, W.γD T γ (b k : W.DD T) =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • D i) m k) : LetA O f) • (b m : W.DD T))
    (hD' : ∀ k, W.γD T' γ (b' k : W.DD T') =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • D' i) m k) : LetA O f) • (b' m : W.DD T'))
    (hA : ∀ k, W.map g (b k : W.DD T) = ∑ m, (fun i => inc l O (A i m k) : LetA O f) • (b' m : W.DD T'))
    (i : ZMod f) :
    (1 + (X : F⟦X⟧) • (D' i).map (PowerSeries.map red)) *
        ((A i).map (PowerSeries.map red)).map (gam0 0 (PowerSeries.map red un)) =
      (A i).map (PowerSeries.map red) * (1 + (X : F⟦X⟧) • (D i).map (PowerSeries.map red)) := by
  classical
  have hc := fun j k => coeff_comm (fun k => (b k : W.DD T)) b'
    (W.map g).toAddMonoidHom (W.γD T γ).toAddMonoidHom (W.γD T' γ).toAddMonoidHom (letγ (W.γ₀ γ))
    (fun a x => map_smul_letA W g a x) (fun a x => gamD_smul W T' γ a x) (fun x => W.map_γ g γ x)
    (fun m k => (fun i => inc l O ((1 + (X : O⟦X⟧) • D i) m k) : LetA O f))
    (fun m k => (fun i => inc l O ((1 + (X : O⟦X⟧) • D' i) m k) : LetA O f))
    (fun m k => (fun i => inc l O (A i m k) : LetA O f)) hD hD' hA j k
  have hi : ∀ j k, ∑ m, inc l O ((1 + (X : O⟦X⟧) • D i) m k) * inc l O (A i j m) =
      ∑ m, inc l O ((A i).map (gam0 (l : O) un) m k) * inc l O ((1 + (X : O⟦X⟧) • D' i) j m) := by
    intro j k
    have e := congrFun (hc j k) i
    rw [Finset.sum_apply, Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun m _ => ?_)
    show W.γ₀ γ (inc l O (A i m k)) * inc l O ((1 + (X : O⟦X⟧) • D' i) j m) = _
    rw [hγ, gamma_on_pi0Subst_holds l O u un hun]
    rfl
  have hM := mul_eq_of_inc hl (1 + (X : O⟦X⟧) • D i) (1 + (X : O⟦X⟧) • D' i) (A i) ((A i).map (gam0 (l : O) un)) hi
  have hG : ((A i).map (gam0 (l : O) un)).map (PowerSeries.map red) =
      ((A i).map (PowerSeries.map red)).map (gam0 0 (PowerSeries.map red un)) := by
    refine Matrix.ext fun m k => ?_
    simp only [Matrix.map_apply]
    rw [gamma_reduction_holds O F red (l : O) un (A i m k), map_natCast, CharP.cast_eq_zero]
  rw [← hG, ← map_one_add_X_smul red (D' i), ← map_one_add_X_smul red (D i), ← Matrix.map_mul, hM, Matrix.map_mul]

end Local

theorem charP_residueField_of_irreducible {l : ℕ} [Fact l.Prime] (LL : FinExt l) : CharP (ResidueField ↥(OL LL)) l := by
  have hl : l.Prime := Fact.out
  have : Algebra.IsIntegral ℤ_[l] ↥(OL LL) := ⟨fun x => integralClosure.isIntegral x⟩
  rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue ↥(OL LL)), IsLocalRing.residue_eq_zero_iff]
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[l]) (IsLocalRing.maximalIdeal ↥(OL LL))
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hmem : (l : ℤ_[l]) ∈ (IsLocalRing.maximalIdeal ↥(OL LL)).comap (algebraMap ℤ_[l] ↥(OL LL)) := by
    rw [heq, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  simpa using hmem

set_option maxHeartbeats 1000000 in

theorem exists_mapMat_redHom : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (γ : (H.W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (N' : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n' ↥(OL LL)) (u : ℤ_[l]) (un : PowerSeries ↥(OL LL)) (g : LatHom T.L T'.L), IsCrys (P.PD K) T.ρ → IsCrys (P.PD K) T'.ρ → IsFrame (H.W K 1 LL hA.2.2) T γ b N → IsFrame (H.W K 1 LL hA.2.2) T' γ b' N' → ((H.W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → IsUn l ↥(OL LL) u un → ∃ A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n, IsMapMat (H.W K 1 LL hA.2.2) g b b' A ∧ ∀ i, RedHom l ((PowerSeries.map (residue ↥(OL LL))) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((A i).map (PowerSeries.map (residue ↥(OL LL)))) ((A (i - 1)).map (PowerSeries.map (residue ↥(OL LL)))) := by
  intro l _ P H K LL hA T T' n n' γ b b' N N' u un g hT hT' hF hF' hχ hun
  have hl : l ≠ 2 := hA.2.1
  have := charP_residueField_of_irreducible LL
  obtain ⟨hφ, -, hγ, -, hRF, -⟩ := GlobalTheory.T.wachRingFacts_unramified_levelOne H K LL hA
  have RF : ∀ a : (↥(OL LL))⟦X⟧, (∀ δ ∈ (H.W K 1 LL hA.2.2).DelF, (H.W K 1 LL hA.2.2).γ₀ δ a = a) →
      ∃ y, inc l ↥(OL LL) y = a := fun a ha => (hRF a).mp ha
  obtain ⟨A, hAm⟩ := exists_mapMat (H.W K 1 LL hA.2.2) b b' RF g hT hT' hF.1 hF'.1
  refine ⟨A, hAm, fun i => ⟨?_, ?_⟩⟩
  · exact red_frob (H.W K 1 LL hA.2.2) b b' (residue ↥(OL LL)) hl (fun z => rfl) hφ g N.P N'.P A
      hF.2.1 hF'.2.1 hAm i
  · exact red_gam (H.W K 1 LL hA.2.2) b b' (residue ↥(OL LL)) hl γ u un hun (hγ γ u hχ) g N.D N'.D A
      hF.2.2.1 hF'.2.2.1 hAm i

end GlobalTheory.WachMap

end
end

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachModule_map_matrix_reduction_comm : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (γ : (H.W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (N' : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n' ↥(OL LL)) (u : ℤ_[l]) (un : PowerSeries ↥(OL LL)) (g : LatHom T.L T'.L), IsCrys (P.PD K) T.ρ → IsCrys (P.PD K) T'.ρ → IsFrame (H.W K 1 LL hA.2.2) T γ b N → IsFrame (H.W K 1 LL hA.2.2) T' γ b' N' → ((H.W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → IsUn l ↥(OL LL) u un → ∃ A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n, IsMapMat (H.W K 1 LL hA.2.2) g b b' A ∧ ∀ i, RedHom l ((PowerSeries.map (residue ↥(OL LL))) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((A i).map (PowerSeries.map (residue ↥(OL LL)))) ((A (i - 1)).map (PowerSeries.map (residue ↥(OL LL)))) := by
  atlas_forward_decl GlobalTheory.WachMap.exists_mapMat_redHom
end

section
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachPlace

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}

theorem wachMap_comp_coeff (W : LocWach PD LL O v f) {T T' T'' : LocLat G Qp LL O} {n n' n'' : ℕ}
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (b' : Module.Basis (Fin n') (LetA O f) ↥(W.N T'))
    (b'' : Module.Basis (Fin n'') (LetA O f) ↥(W.N T''))
    (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L)
    (a : Fin n → Fin n' → LetA O f) (a' : Fin n' → Fin n'' → LetA O f) (a'' : Fin n → Fin n'' → LetA O f)
    (h1 : ∀ k, W.map g (b k : W.DD T) = ∑ m, a k m • (b' m : W.DD T'))
    (h2 : ∀ k, W.map g' (b' k : W.DD T') = ∑ m, a' k m • (b'' m : W.DD T''))
    (h3 : ∀ k, W.map g'' (b k : W.DD T) = ∑ m, a'' k m • (b'' m : W.DD T''))
    (hc : ∀ x, g''.f x = g'.f (g.f x)) (k : Fin n) (p : Fin n'') :
    a'' k p = ∑ m, a k m * a' m p := by
  have hg : g'' = latComp g' g := by
    cases g''
    simp only [latComp]
    congr 1
    exact LinearMap.ext hc
  have hsm : ∀ {S S' : LocLat G Qp LL O} (u : LatHom S.L S'.L) (c : LetA O f) (x : W.DD S),
      W.map u (c • x) = c • W.map u x := fun u c x => (W.map u).map_smul_of_tower c x
  have key : W.map g'' (b k : W.DD T) = ∑ q, (∑ m, a k m * a' m q) • (b'' q : W.DD T'') := by
    rw [hg, W.map_comp, h1 k, map_sum]
    simp_rw [hsm, h2, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
  have e : ∑ q, a'' k q • b'' q = ∑ q, (∑ m, a k m * a' m q) • b'' q := by
    apply (W.N T'').subtype_injective
    simpa [map_sum] using (h3 k).symm.trans key
  have := congrArg (fun x => b''.repr x p) e
  simpa [Finset.sum_apply, map_sum, Finsupp.smul_apply, b''.repr_self, Finsupp.single_apply] using this

end Gen

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem isMapMat_comp_mul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' n'' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T'')) (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n') (A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n), IsMapMat (H.W K 1 LL hA.2.2) g b b' A → IsMapMat (H.W K 1 LL hA.2.2) g' b' b'' A' → IsMapMat (H.W K 1 LL hA.2.2) g'' b b'' A'' → (∀ x, g''.f x = g'.f (g.f x)) → ∀ i, A'' i = A' i * A i := by
  intro l _ P H K LL hA T T' T'' n n' n'' b b' b'' g g' g'' A A' A'' h1 h2 h3 hc i
  obtain ⟨hadd, hmul, hC, -, -, -, -, hinj⟩ := Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_laws_hold l ↥(OL LL)
  let incR : (↥(OL LL))⟦X⟧ →+* (↥(OL LL))⟦X⟧ :=
    { toFun := inc l ↥(OL LL)
      map_one' := by simpa using hC 1
      map_mul' := hmul
      map_zero' := by simpa using hC 0
      map_add' := hadd }
  refine Matrix.ext fun p k => hinj hA.2.1 ?_
  have e := congrFun (wachMap_comp_coeff (H.W K 1 LL hA.2.2) b b' b'' g g' g''
    (fun k m i => inc l ↥(OL LL) (A i m k)) (fun k m i => inc l ↥(OL LL) (A' i m k))
    (fun k m i => inc l ↥(OL LL) (A'' i m k)) h1 h2 h3 hc k p) i
  rw [Finset.sum_apply] at e
  rw [Matrix.mul_apply]
  refine e.trans (Eq.trans ?_ (map_sum incR _ _).symm)
  exact Finset.sum_congr rfl fun m _ => (mul_comm _ _).trans (hmul _ _).symm

end GlobalTheory.WachPlace
end
end

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModuleMapMatrix_comp_mul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' n'' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T'')) (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n') (A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n), IsMapMat (H.W K 1 LL hA.2.2) g b b' A → IsMapMat (H.W K 1 LL hA.2.2) g' b' b'' A' → IsMapMat (H.W K 1 LL hA.2.2) g'' b b'' A'' → (∀ x, g''.f x = g'.f (g.f x)) → ∀ i, A'' i = A' i * A i := by
  atlas_forward_decl GlobalTheory.WachPlace.isMapMat_comp_mul
end

section
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachPlace

theorem matGood_of_tw {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (f n : ℕ)
    (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r r' : ↥(GK K) →* GL (Fin n) ↥(OL LL))
    (U : ZMod f → Multiset ℤ) (a : Mx ↥(OL LL) n n) :
    MatGood P emb r U → Tw r' r a → a.det ≠ 0 → MatGood P emb r' U := by
  rintro ⟨hc, hcr, hj⟩ ht hdet
  set φ := algebraMap ↥(OL LL) ↥LL.1 with hφ
  have hinj : Function.Injective φ := fun x y h => Subtype.ext h
  set aL : Mx ↥LL.1 n n := a.map φ with haL
  have hdL : IsUnit aL.det := by
    have hd : aL.det = φ a.det := (RingHom.map_det φ a).symm
    rw [hd]
    exact isUnit_iff_ne_zero.mpr (fun h => hdet (hinj (by rw [h, map_zero])))
  have htL : ∀ g, aL * (r' g : Mx ↥(OL LL) n n).map φ = (r g : Mx ↥(OL LL) n n).map φ * aL := fun g => by
    rw [haL, ← Matrix.map_mul, ← Matrix.map_mul, ht g]
  have hconj : ∀ g, (r' g : Mx ↥(OL LL) n n).map φ = aL⁻¹ * ((r g : Mx ↥(OL LL) n n).map φ * aL) := fun g => by
    rw [← htL g, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdL, Matrix.one_mul]
  let e : (Fin n → ↥LL.1) ≃ₗ[↥LL.1] (Fin n → ↥LL.1) :=
    LinearEquiv.ofLinear (Matrix.toLin' aL) (Matrix.toLin' aL⁻¹)
      (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hdL, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hdL, Matrix.toLin'_one])
  have he : ∀ g v, e (repOf r' g v) = repOf r g (e v) := fun g v => by
    show aL.mulVec (repOf r' g v) = repOf r g (aL.mulVec v)
    rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htL g]
  refine ⟨fun i j => ?_, GlobalTheory.HTW.Rec.isCrys_of_equiv _ e he hcr, fun i τ hτ u => ?_⟩
  · have hform : (fun g => (((r' g : Mx ↥(OL LL) n n) i j : ↥(OL LL)) : ↥LL.1)) =
        fun g => ∑ k, aL⁻¹ i k * ∑ m, (((r g : Mx ↥(OL LL) n n) k m : ↥(OL LL)) : ↥LL.1) * aL m j := by
      funext g
      have := congrFun (congrFun (hconj g) i) j
      simp only [Matrix.map_apply, Matrix.mul_apply] at this
      exact this
    rw [hform]
    refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
    exact continuous_finset_sum _ fun m _ => (hc k m).mul continuous_const
  · rw [GlobalTheory.HTW.Rec.multV_eq_of_equiv _ e he]
    exact hj i τ hτ u

end GlobalTheory.WachPlace

end
end

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isContinuousCrystallineMatrixRep_of_intertwines_det_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r r' : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (U : ZMod f → Multiset ℤ) (a : Mx ↥(OL LL) n n), MatGood P emb r U → Tw r' r a → a.det ≠ 0 → MatGood P emb r' U := by
  atlas_forward_decl GlobalTheory.WachPlace.matGood_of_tw
end

section
namespace GlobalTheory.MulVecZeroDenominator

private lemma mulVec_eq_zero_of_map_mulVec_eq_zero {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] {m c : ℕ} (D : Matrix (Fin m) (Fin c) O) (x : Fin c → L) (v : Fin c → O)
    (d : O) (hv : ∀ i, algebraMap O L (v i) = d • x i)
    (hD : Matrix.mulVec (Matrix.map D (algebraMap O L)) x = 0) : Matrix.mulVec D v = 0 := by
  funext i
  apply IsFractionRing.injective O L
  rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
  have hvx : (algebraMap O L ∘ v) = d • x := funext hv
  rw [hvx, Matrix.mulVec_smul, hD, smul_zero, Pi.zero_apply]

private lemma exists_common_denominator_divisor {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] {c : ℕ} (x : Fin c → L) :
    ∃ (d : O) (v : Fin c → O), algebraMap O L d ≠ 0 ∧ ∀ i, algebraMap O L (v i) = d • x i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose v hv using hd
  exact ⟨d, v, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hv⟩

theorem main {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L] [IsFractionRing O L]
    {a b c : ℕ} (B : GlobalTheory.WachPlace.Mx O a c) (C : GlobalTheory.WachPlace.Mx O b c)
    (h : ∀ (v : Fin c → O), Matrix.mulVec B v = (0 : Fin a → O) →
      Matrix.mulVec C v = (0 : Fin b → O) → v = (0 : Fin c → O))
    (x : Fin c → L)
    (hB : Matrix.mulVec (Matrix.map B (⇑(algebraMap O L) : O → L)) x = (0 : Fin a → L))
    (hC : Matrix.mulVec (Matrix.map C (⇑(algebraMap O L) : O → L)) x = (0 : Fin b → L)) :
    x = (0 : Fin c → L) := by
  obtain ⟨d, v, hd, hv⟩ := exists_common_denominator_divisor (O := O) x
  have hv0 : v = 0 := h v (mulVec_eq_zero_of_map_mulVec_eq_zero B x v d hv hB) (mulVec_eq_zero_of_map_mulVec_eq_zero C x v d hv hC)
  funext i
  have hi := hv i
  rw [hv0, Pi.zero_apply, map_zero, Algebra.smul_def] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left hd

theorem target : ∀ {O L : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field L] [inst_3 : Algebra O L] [IsFractionRing O L] {a b c : ℕ} (B : GlobalTheory.WachPlace.Mx O a c) (C : GlobalTheory.WachPlace.Mx O b c), (∀ (v : Fin c → O), Matrix.mulVec B v = (0 : Fin a → O) → Matrix.mulVec C v = (0 : Fin b → O) → v = (0 : Fin c → O)) → ∀ (x : Fin c → L), Matrix.mulVec (Matrix.map B (⇑(Algebra.algebraMap O L) : O → L)) x = (0 : Fin a → L) → Matrix.mulVec (Matrix.map C (⇑(Algebra.algebraMap O L) : O → L)) x = (0 : Fin b → L) → x = (0 : Fin c → L) := by
  intro O L _ _ _ _ _ a b c B C h x hB hC
  obtain ⟨d, v, hd, hv⟩ := exists_common_denominator_divisor (O := O) x
  have hv0 : v = 0 := h v (mulVec_eq_zero_of_map_mulVec_eq_zero B x v d hv hB) (mulVec_eq_zero_of_map_mulVec_eq_zero C x v d hv hC)
  funext i
  have hi := hv i
  rw [hv0, Pi.zero_apply, map_zero, Algebra.smul_def] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left hd

end GlobalTheory.MulVecZeroDenominator
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace.FullRankSum

theorem joint_inj {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L] [IsFractionRing O L] {a b c : ℕ}
    (B : Mx O a c) (C : Mx O b c) (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) (x : Fin c → L)
    (hB : (B.map (algebraMap O L)).mulVec x = 0) (hC : (C.map (algebraMap O L)).mulVec x = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6; revert O L h_2 h_3 h_4 h_5 h_6 a b c B C h x hB hC; exact @_root_.GlobalTheory.MulVecZeroDenominator.target)
  | exact @_root_.GlobalTheory.MulVecZeroDenominator.target
  | exact _root_.GlobalTheory.MulVecZeroDenominator.target
  | (apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulVecZeroDenominator.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulVecZeroDenominator.target ..)

theorem exists_equiv {L : Type} [Field L] {n : ℕ} (B : Mx L n (n + 1)) (C : Mx L 1 (n + 1))
    (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) :
    ∃ e : (Fin (n + 1) → L) ≃ₗ[L] (Fin n → L) × (Fin 1 → L), ∀ v, e v = (B.mulVec v, C.mulVec v) := by
  let φ : (Fin (n + 1) → L) →ₗ[L] (Fin n → L) × (Fin 1 → L) := (Matrix.toLin' B).prod (Matrix.toLin' C)
  have hi : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact h v (congrArg Prod.fst hv) (congrArg Prod.snd hv)
  exact ⟨φ.linearEquivOfInjective hi (by simp), fun v => rfl⟩

variable {l : ℕ} [Fact l.Prime] {K LL : FinExt l}

theorem tw_mulVec {a b : ℕ} {r : ↥(GK K) →* GL (Fin b) ↥(OL LL)} {r' : ↥(GK K) →* GL (Fin a) ↥(OL LL)}
    {A : Mx ↥(OL LL) a b} (hA : Tw r r' A) (g : ↥(GK K)) (y : Fin b → ↥LL.1) :
    (A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec (repOf r g y) =
      repOf r' g ((A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec y) := by
  rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
    hA g]

theorem matGood_sum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (ρ : ↥(GK K) →* GL (Fin 1) ↥(OL LL)) (r₂ : ↥(GK K) →* GL (Fin (n + 1)) ↥(OL LL)) (U U' : ZMod f → Multiset ℤ) (B : Mx ↥(OL LL) n (n + 1)) (C : Mx ↥(OL LL) 1 (n + 1)), MatGood P emb r U → MatGood P emb ρ U' → Tw r₂ r B → Tw r₂ ρ C → (∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) → MatGood P emb r₂ (fun i => U i + U' i) := by
  intro l _ P AI T K LL f n emb r ρ r₂ U U' B C hr hρ hB hC hinj
  obtain ⟨_, -, -, -, -, -, hF⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨e, he⟩ := exists_equiv (B.map (algebraMap ↥(OL LL) ↥LL.1)) (C.map (algebraMap ↥(OL LL) ↥LL.1))
    (joint_inj B C hinj)
  have hq : ∀ g v, e (repOf r₂ g v) = (repOf r g (e v).1, repOf ρ g (e v).2) := fun g v => by
    rw [he, he, tw_mulVec hB, tw_mulVec hC]
  obtain ⟨-, hc, hm⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T K LL _ (repOf r₂) _ (repOf r) _ (repOf ρ) e hq
  refine ⟨fun a b => ?_, hc.2 ⟨hr.2.1, hρ.2.1⟩, fun i τ hτ a => ?_⟩
  · have c1 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inl _ _ _) := LinearMap.continuous_on_pi _
    have c2 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inr _ _ _) := LinearMap.continuous_on_pi _
    have d1 : Continuous fun g => repOf r g (e (Pi.single b 1)).1 := (latOf r hr.1).cont _
    have d2 : Continuous fun g => repOf ρ g (e (Pi.single b 1)).2 := (latOf ρ hρ.1).cont _
    have d := (continuous_apply a).comp ((c1.comp d1).add (c2.comp d2))
    refine d.congr fun g => ?_
    have : repOf r₂ g (Pi.single b 1) = e.symm (repOf r g (e (Pi.single b 1)).1, 0) +
        e.symm (0, repOf ρ g (e (Pi.single b 1)).2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, ← hq, e.symm_apply_apply]
    have h2 := congrFun this a
    rw [repOf_apply, Matrix.mulVec_single_one] at h2
    exact h2.symm
  · rw [hm, hr.2.2 i τ hτ a, hρ.2.2 i τ hτ a, Multiset.count_add]
    push_cast
    rfl

end GlobalTheory.WachPlace.FullRankSum

end
end

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matGood_of_block_extension_twist : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (ρ : ↥(GK K) →* GL (Fin 1) ↥(OL LL)) (r₂ : ↥(GK K) →* GL (Fin (n + 1)) ↥(OL LL)) (U U' : ZMod f → Multiset ℤ) (B : Mx ↥(OL LL) n (n + 1)) (C : Mx ↥(OL LL) 1 (n + 1)), MatGood P emb r U → MatGood P emb ρ U' → Tw r₂ r B → Tw r₂ ρ C → (∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) → MatGood P emb r₂ (fun i => U i + U' i) := by
  atlas_forward_decl GlobalTheory.WachPlace.FullRankSum.matGood_sum
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.PlaceLetters

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

theorem norm_emb_le (σ : E →+* Om l) (b : 𝓞 E) : ‖σ (b : E)‖ ≤ 1 :=
  GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int σ b.isIntegral_coe)

theorem emb_eq_of_congr (hE : ¬ (l : ℤ) ∣ discr E) (τ τ' : E →+* Om l)
    (hlt : ∀ b : 𝓞 E, ‖τ (b : E) - τ' (b : E)‖ < 1) : τ = τ' := by
  classical
  by_contra hne
  have hd := GlobalTheory.SplitEmbSep.one_le_norm_intCast (C := Om l) Fact.out GlobalTheory.PlaceBridge.norm_l_lt_one hE
  let b := integralBasis E
  have e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Om l) :=
    Fintype.equivOfCardEq (by rw [AlgHom.card, Module.finrank_eq_card_basis b])
  have hdet := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ (Om l) b e
  rw [← coe_discr, map_intCast] at hdet
  set M := Algebra.embeddingsMatrixReindex ℚ (Om l) b e with hM
  have hMij : ∀ i j, M i j = (e j).toRingHom ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i j
    simp [hM, b, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, integralBasis_apply]
  set k := e.symm τ.toRatAlgHom with hk
  set k' := e.symm τ'.toRatAlgHom with hk'
  have hkk : k ≠ k' := fun h => hne (by
    have := e.symm.injective h
    exact RingHom.ext fun x => DFunLike.congr_fun this x)
  have hcol : ∀ i, M i k + (-1 : Om l) • M i k' =
      τ ((RingOfIntegers.basis E i : 𝓞 E) : E) - τ' ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    rw [hMij, hMij, hk, hk', e.apply_symm_apply, e.apply_symm_apply, neg_one_smul,
      ← sub_eq_add_neg]
    rfl
  have hlt' : ‖M.det‖ < 1 := by
    rw [← Matrix.det_updateCol_add_smul_self M hkk (-1)]
    refine GlobalTheory.SplitEmbSep.norm_det_lt_one _ (fun i j => ?_) k fun i => ?_
    · by_cases hj : j = k
      · rw [hj, Matrix.updateCol_self, hcol]; exact (hlt _).le
      · rw [Matrix.updateCol_ne hj, hMij]; exact norm_emb_le _ _
    · rw [Matrix.updateCol_self, hcol]; exact hlt _
  rw [hdet, norm_pow] at hd
  exact absurd (hd.trans_lt (pow_lt_one₀ (norm_nonneg _) hlt' two_ne_zero)) (lt_irrefl _)

theorem norm_algHom {K : IntermediateField ℚ_[l] (Om l)} (f : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) :
    ‖f x‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq f f.toRingHom.injective x
  have h2 := minpoly.algHom_eq K.val K.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

theorem norm_gal (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algEquiv_eq]

theorem norm_sub_lt_one {x y : Om l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))

theorem inertia_of_fix (g : GQ l) (hg : ∀ x ∈ MaximalUnramifiedExtension l, g x = x) (x : Om l) (hx : ‖x‖ ≤ 1) : ‖g x - x‖ < 1 := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact norm_sub_lt_one (by rwa [norm_gal]) hlt
  · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar x heq
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
    have h1 : g ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
    have h2 : g x - x = g (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
    rw [h2]
    exact norm_sub_lt_one (by rwa [norm_gal]) hxζ

theorem emb_mem_Kur (hE : ¬ (l : ℤ) ∣ discr E) (τ : E →+* Om l) (x : E) : τ x ∈ MaximalUnramifiedExtension l := by
  have : IsGalois ℚ_[l] (Om l) := {}
  rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
  intro g hg
  have h := emb_eq_of_congr hE ((g : Om l →+* Om l).comp τ) τ fun b =>
    inertia_of_fix g ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hg) _ (norm_emb_le τ b)
  exact DFunLike.congr_fun h x

theorem exists_extend {K : IntermediateField ℚ_[l] (Om l)} (f : ↥K →ₐ[ℚ_[l]] Om l) :
    ∃ g : Om l →ₐ[ℚ_[l]] Om l, ∀ x : ↥K, g x = f x :=
  ⟨f.liftNormal (Om l), fun x => f.liftNormal_commutes (Om l) x⟩

section Bridge

variable {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem kw_le (M : IntermediateField ℚ_[l] (Om l)) (h : ∀ x : E, Bw.j (algebraMap E Ω x) ∈ M) : Bw.Kw.1 ≤ M := by
  have hfin := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (Bw.j.comp (algebraMap E Ω))
  have hcl := Submodule.closed_of_finiteDimensional (𝕜 := ℚ_[l])
    (IntermediateField.adjoin ℚ_[l] (Set.range (Bw.j.comp (algebraMap E Ω)))).toSubmodule
  refine le_trans (fun y hy => ?_) (IntermediateField.adjoin_le_iff.2 (Set.range_subset_iff.2 h))
  exact closure_minimal (IntermediateField.subset_adjoin ℚ_[l] _) hcl (Bw.j_dense hy)

theorem kw_le_comap (LL : FinExt l) (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) (g : Om l →ₐ[ℚ_[l]] Om l) :
    Bw.Kw.1 ≤ LL.1.comap g :=
  kw_le Bw _ fun x => hL ((g : Om l →+* Om l).comp (Bw.j.comp (algebraMap E Ω))) x

theorem caseA (hl : l ≠ 2) (hE : ¬ (l : ℤ) ∣ discr E) (LL : FinExt l) (hζ : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l)
    (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) : CaseA Bw.Kw LL := by
  have hK : Bw.Kw.1 ≤ MaximalUnramifiedExtension l := kw_le Bw _ fun x => emb_mem_Kur hE (Bw.j.comp (algebraMap E Ω)) x
  refine ⟨hK, hl, le_rfl, fun h => absurd h hl, (le_inf le_rfl hK).trans le_sup_left, fun τ x => ?_⟩
  obtain ⟨g, hg⟩ := exists_extend τ
  obtain ⟨ζ, hζ⟩ := hζ
  have hζ' : IsPrimitiveRoot (ζ : Om l) l := hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hle : Ks Bw.Kw 1 ≤ LL.1.comap g := by
    refine sup_le (inf_le_left.trans (kw_le_comap Bw LL hL g)) (IntermediateField.adjoin_le_iff.2 fun y hy => ?_)
    have hy' : g y ^ l = 1 := by
      have : y ^ l = 1 := by simpa using hy
      rw [← map_pow, this, map_one]
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hy'
    change g y ∈ LL.1
    rw [← hi]
    exact pow_mem ζ.2 i
  rw [← hg]
  exact hle x.2

end Bridge

section Letters

variable {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (hK : Bw.Kw.1 ≤ K0 Bw.Kw) {LL : FinExt l}

def toK0 : E →+* ↥(K0 Bw.Kw) :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict (K0 Bw.Kw) fun x => hK (Bw.j_E x)

def embOf (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) : E →+* Om l :=
  ((LL.1.val.comp e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] Om l) : ↥(K0 Bw.Kw) →+* Om l).comp (toK0 Bw hK)

omit [NumberField E] in

theorem isInduced_embOf (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : ∀ x : ↥(K0 Bw.Kw), τ (algebraMap ↥(K0 Bw.Kw) ↥Bw.Kw.1 x) = e x) :
    GlobalTheory.Pst.IsInduced Bw (embOf Bw hK e) τ := fun x =>
  congrArg Subtype.val (hτ (toK0 Bw hK x)).symm

omit [NumberField E] in

theorem embOf_injective : Function.Injective (embOf Bw hK (LL := LL)) := by
  intro e e' h
  have h1 := isInduced_embOf Bw hK e (e.comp (IntermediateField.inclusion hK)) fun _ => rfl
  have h2 := isInduced_embOf Bw hK e' (e'.comp (IntermediateField.inclusion hK)) fun _ => rfl
  rw [← h] at h2
  have h3 := h1.unique h2
  exact AlgHom.ext fun x => DFunLike.congr_fun h3 (algebraMap ↥(K0 Bw.Kw) ↥Bw.Kw.1 x)

theorem embOf_frob (P : LocPrime l) (hE : ¬ (l : ℤ) ∣ discr E) {σ : Equiv.Perm (E →+* PadicAlgCl l)}
    (hσ : GlobalTheory.ExpFrame.IsFrobPerm σ) (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) :
    embOf Bw hK (e.comp (P.PD Bw.Kw).σ) = σ (embOf Bw hK e) := by
  refine emb_eq_of_congr hE _ _ fun b => ?_
  have h1 := hσ (embOf Bw hK e) b
  have h2 := P.PD_σ Bw.Kw (toK0 Bw hK b) (norm_emb_le (Bw.j.comp (algebraMap E Ω)) b)
  have h3 := norm_algHom (LL.1.val.comp e) ((P.PD Bw.Kw).σ (toK0 Bw hK b) - toK0 Bw hK b ^ l)
  rw [map_sub, map_pow] at h3
  have h4 : ‖embOf Bw hK (e.comp (P.PD Bw.Kw).σ) b - embOf Bw hK e b ^ l‖ < 1 := h3.trans_lt h2
  have h5 := norm_sub_lt_one h4 h1
  rwa [sub_sub_sub_cancel_right] at h5

end Letters

theorem exists_bridge_over (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (LL : FinExt l)
    (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) (τ : E →+* Om l) :
    ∃ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧ Bw.LL.1 ≤ LL.1 ∧
        ∀ x, τ x = Bw.j (algebraMap E Ω x) := by
  obtain ⟨w, A, hA, L0, Bw, hI, hτ⟩ := GlobalTheory.ExpFrame.Tests.exists_bridge Ω τ
  refine ⟨w, A, hA, { Bw with
    LL := LL
    LL_split := fun f x => ?_
    eO := RingEquiv.refl _
    eO_alg := fun _ => rfl
    eO_cont := continuous_id
    eO_symm_cont := continuous_id }, hI, le_rfl, hτ⟩
  obtain ⟨g, hg⟩ := exists_extend f
  rw [← hg]
  exact kw_le_comap Bw LL hL g x.2

theorem exists_place : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (H : LocHW l P) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), GlobalTheory.ExpFrame.IsFrobPerm σ → ∀ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) → ∀ i₀ : E →+* PadicAlgCl l, ∃ (K : FinExt l) (hA : CaseA K LL) (ι : ↥(GK K) →* (Ω ≃ₐ[E] Ω)) (κ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (E →+* PadicAlgCl l)), Function.Injective κ ∧ (∀ i, κ (i - 1) = σ (κ i)) ∧ i₀ ∈ Set.range κ ∧ ∀ (n : ℕ) (r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)) (J : (E →+* PadicAlgCl l) → Multiset ℤ), GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) J → MatGood P (H.W K 1 LL hA.2.2).emb (r.comp ι) (fun i => J (κ i)) := by
  intro l _ P AI hT H E Ω _ _ _ _ _ hl hE σ hσ LL hζ hL i₀
  obtain ⟨w, A, hA, Bw, hI, hLL, hi₀⟩ := exists_bridge_over Ω LL hL i₀
  have hC := caseA Bw hl hE LL hζ hL
  have hK0 : Bw.Kw.1 ≤ K0 Bw.Kw := le_inf le_rfl hC.1
  have hbij := (H.W Bw.Kw 1 LL hC.2.2).emb_bij
  have hembσ := (H.W Bw.Kw 1 LL hC.2.2).emb_σ
  let emb := (H.W Bw.Kw 1 LL hC.2.2).emb
  have hK0L : K0 Bw.Kw ≤ LL.1 := inf_le_left.trans (kw_le Bw _ fun x => hL (Bw.j.comp (algebraMap E Ω)) x)
  refine ⟨Bw.Kw, hC, (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom, fun i => embOf Bw hK0 (emb i),
    (embOf_injective Bw hK0).comp hbij.1, fun i => ?_, ?_, fun n r J hr => ?_⟩
  · have h := hembσ (i - 1)
    rw [sub_add_cancel] at h
    exact (congrArg (embOf Bw hK0) h.symm).trans (embOf_frob Bw hK0 P hE hσ (emb i))
  · obtain ⟨i, hi⟩ := hbij.2 (IntermediateField.inclusion hK0L)
    refine ⟨i, RingHom.ext fun x => ?_⟩
    change embOf Bw hK0 ((H.W Bw.Kw 1 LL hC.2.2).emb i) x = _
    rw [hi, hi₀]
    rfl
  · obtain ⟨hc, hj⟩ := hr.2 P AI ⟨hT⟩ w A hA _ Bw hI
    have hM : GlobalTheory.Pst.IsModel Bw (((Matrix.GeneralLinearGroup.map (toOm LL)).comp r).comp
        (ReciprocityTheory.Gal.Dec (F := E) A).subtype) LL
        (Formalism.MainNotions.N.mapRep (algebraMap ↥(OL LL) ↥LL.1) (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) :=
      ⟨hLL, by ext g a b; rfl⟩
    refine ⟨fun a b => ?_, (hM.isCrysAt_iff P).1 hc, fun i τ hτ a => ?_⟩
    · have h1 : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : ↥(ReciprocityTheory.Gal.Dec (F := E) A)) : Ω ≃ₐ[E] Ω) :=
        continuous_subtype_val.comp Bw.e_symm_cont
      have h2 := (Units.continuous_val.comp (hr.1.comp h1)).matrix_elem a b
      exact continuous_induced_rng.2 h2
    · have hτ' := isInduced_embOf Bw hK0 (emb i) τ hτ
      exact (GlobalTheory.Pst.IsJumpsAt.count_eq P hM hτ' (hj _ _ _ hτ') a).symm

end GlobalTheory.PlaceLetters

end
end

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramifiedLocalSituation_of_embedding : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (H : LocHW l P) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), GlobalTheory.ExpFrame.IsFrobPerm σ → ∀ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) → ∀ i₀ : E →+* PadicAlgCl l, ∃ (K : FinExt l) (hA : CaseA K LL) (ι : ↥(GK K) →* (Ω ≃ₐ[E] Ω)) (κ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (E →+* PadicAlgCl l)), Function.Injective κ ∧ (∀ i, κ (i - 1) = σ (κ i)) ∧ i₀ ∈ Set.range κ ∧ ∀ (n : ℕ) (r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)) (J : (E →+* PadicAlgCl l) → Multiset ℤ), GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) J → MatGood P (H.W K 1 LL hA.2.2).emb (r.comp ι) (fun i => J (κ i)) := by
  atlas_forward_decl GlobalTheory.PlaceLetters.exists_place
end

section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace

theorem eq_zero_of_lrank {F : Type} [Field F] {a b : ℕ} (A : Mx F⟦X⟧ a b) (h : lrank A = 0) : A = 0 := by
  have h0 : A.map (algebraMap F⟦X⟧ (LaurentSeries F)) = 0 := by
    unfold lrank Matrix.rank at h
    have hr := Submodule.finrank_eq_zero.mp h
    have hB := LinearMap.range_eq_bot.mp hr
    refine Matrix.ext fun i j => ?_
    have := congrFun (LinearMap.congr_fun hB (Pi.single j 1)) i
    simpa [Matrix.mulVecLin_apply] using this
  refine Matrix.ext fun i j => ?_
  have := congrFun (congrFun h0 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at this
  rw [LaurentSeries.coe_algebraMap] at this
  exact HahnSeries.ofPowerSeries_injective (this.trans (map_zero _).symm)

section Functor

variable {D : D7} {HW : HWOf D.loc} (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) {l : ℕ} [Fact l.Prime]
  {K LL : FinExt l} (hA : CaseA K LL)

include F Cm in
theorem exists_frame {n : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ}
    (hr : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r U) (hU : ∀ i, ∀ u ∈ U i, 0 ≤ u) (γ : ((HW l).W K 1 LL hA.2.2).Gam) :
    ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r hr.1))) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)),
      IsFrame ((HW l).W K 1 LL hA.2.2) (latOf r hr.1) γ b N := by
  have hn : Module.finrank ↥(OL LL) ↥(latOf r hr.1).L.T = n := by
    rw [Module.finrank_eq_card_basis (basisOf r hr.1), Fintype.card_fin]
  exact GlobalTheory.T.exists_invariant_wachModule_basis_of_nonneg_jumps D HW F Cm l K LL hA (latOf r hr.1) U n hr.2 hU hn γ

include F Cm in
theorem latAt_of_frame {n h : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Fin n → ℤ}
    (hr : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r fun i => Finset.univ.val.map (U i)) (hU : ∀ i a, 0 ≤ U i a ∧ U i a ≤ h)
    {γ : ((HW l).W K 1 LL hA.2.2).Gam} {b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r hr.1))} {N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)}
    (hb : IsFrame ((HW l).W K 1 LL hA.2.2) (latOf r hr.1) γ b N) {u : ℤ_[l]ˣ} {c : ℤ_[l]} {ζ : ↥(OL LL)} {jj : ℕ → (↥(OL LL))⟦X⟧ →+* (↥LL.1)⟦X⟧}
    (hγ : (((HW l).W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) (u : ℤ_[l])) (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c)
    (hζ : IsPrimitiveRoot ζ l) (hjj : ∀ a ∈ Finset.Ioo 0 l, IsExpAt (OL LL).val.toRingHom (ζ ^ a) (jj a)) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    LatAt l (N.P i) (N.D i) (N.Th i) h u (U i) (OL LL).val.toRingHom jj := by
  refine ⟨?_, hb.2.2.2 i, ?_⟩
  · refine GlobalTheory.T.frobeniusMatrix_cofactor_eq_q_pow_frame D HW F Cm l K LL hA (latOf r hr.1) (fun i => Finset.univ.val.map (U i)) n h γ b N hr.2
      (fun i v hv => ?_) hb i
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hv
    exact hU i a
  · intro a ha
    obtain ⟨ha0, hal⟩ := Finset.mem_Ioo.mp ha
    have hprim : IsPrimitiveRoot (ζ ^ a) l :=
      hζ.pow_of_coprime a (Nat.coprime_comm.mp
        ((Fact.out : l.Prime).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha0 hal)))
    exact GlobalTheory.T.frobeniusMatrix_frame_at_primitiveRoot_factor D HW F Cm l K LL hA (latOf r hr.1) n U γ b N (u : ℤ_[l]) c (ζ ^ a) (jj a) hr.2
      (fun i a => (hU i a).1) hb hγ hu hprim (hjj a ha) i

private theorem coe_basisOf_eq_stdMap_single {n : ℕ} (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (hr : Cont r) (k : Fin n) :
    ((basisOf r hr k : ↥(latOf r hr).L.T) : (latOf r hr).V) = stdMap LL n (Pi.single k 1) := by
  show stdMap LL n ((Pi.basisFun ↥(OL LL) (Fin n)) k) = _
  rw [Pi.basisFun_apply]

include F in
theorem exists_mapMat {n n' : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {r' : ↥(GK K) →* GL (Fin n') ↥(OL LL)}
    {U U' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ} (hr : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r U) (hr' : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r' U')
    {γ : ((HW l).W K 1 LL hA.2.2).Gam} {b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r hr.1))} {N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)}
    (hb : IsFrame ((HW l).W K 1 LL hA.2.2) (latOf r hr.1) γ b N)
    {b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r' hr'.1))} {N' : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n' ↥(OL LL)}
    (hb' : IsFrame ((HW l).W K 1 LL hA.2.2) (latOf r' hr'.1) γ b' N') {u : ℤ_[l]} {un : (↥(OL LL))⟦X⟧}
    (hγ : (((HW l).W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u) (hun : IsUn l ↥(OL LL) u un) {a : Mx ↥(OL LL) n' n} (ha : Tw r r' a) :
    ∃ A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (↥(OL LL))⟦X⟧ n' n, IsMapMat ((HW l).W K 1 LL hA.2.2) (homOf hr.1 hr'.1 a ha) b b' A ∧
      (∀ i, RedHom l (PowerSeries.map (residue ↥(OL LL)) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((A i).map (PowerSeries.map (residue ↥(OL LL))))
        ((A (i - 1)).map (PowerSeries.map (residue ↥(OL LL))))) ∧ ∀ i, lrank ((A i).map (PowerSeries.map (residue ↥(OL LL)))) = (a.map (residue ↥(OL LL))).rank := by
  obtain ⟨A, hA1, hA2⟩ := GlobalTheory.T.exists_wachModule_map_matrix_reduction_comm (HW l) K LL hA (latOf r hr.1) (latOf r' hr'.1) n n' γ b b' N N' u un
    (homOf hr.1 hr'.1 a ha) hr.2.1 hr'.2.1 hb hb' hγ hun
  refine ⟨A, hA1, hA2, fun i => ?_⟩
  refine GlobalTheory.T.rank_reduced_letter_matrix_eq_rank_mod_maximal D HW F l K LL hA (latOf r hr.1) (latOf r' hr'.1) n n' b b' (homOf hr.1 hr'.1 a ha) A
    (basisOf r hr.1) (basisOf r' hr'.1) a hr.2.1 hr'.2.1 hA1 (fun k => ?_) i
  simp only [coe_basisOf_eq_stdMap_single]
  show (a.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec (stdMap LL n (Pi.single k 1)) =
    ∑ m, ((a m k : ↥(OL LL)) : ↥LL.1) • stdMap LL n' (Pi.single m 1)
  rw [stdMap_mulVec]
  funext j
  rw [stdMap_apply, Finset.sum_apply, Finset.sum_eq_single j
    (fun m _ hm => by simp [stdMap_apply, Pi.single_apply, Ne.symm hm]) (by simp)]
  simp [stdMap_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem mapMat_mul {n n' n'' : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {r' : ↥(GK K) →* GL (Fin n') ↥(OL LL)}
    {r'' : ↥(GK K) →* GL (Fin n'') ↥(OL LL)} {hr : Cont r} {hr' : Cont r'} {hr'' : Cont r''}
    {b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r hr))}
    {b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r' hr'))}
    {b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N (latOf r'' hr''))}
    {a : Mx ↥(OL LL) n' n} {ha : Tw r r' a} {a' : Mx ↥(OL LL) n'' n'} {ha' : Tw r' r'' a'} {a'' : Mx ↥(OL LL) n'' n} {ha'' : Tw r r'' a''}
    {A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (↥(OL LL))⟦X⟧ n' n} {A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (↥(OL LL))⟦X⟧ n'' n'} {A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (↥(OL LL))⟦X⟧ n'' n}
    (h : IsMapMat ((HW l).W K 1 LL hA.2.2) (homOf hr hr' a ha) b b' A) (h' : IsMapMat ((HW l).W K 1 LL hA.2.2) (homOf hr' hr'' a' ha') b' b'' A')
    (h'' : IsMapMat ((HW l).W K 1 LL hA.2.2) (homOf hr hr'' a'' ha'') b b'' A'') (e : a'' = a' * a) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    (A'' i).map (PowerSeries.map (residue ↥(OL LL))) = (A' i).map (PowerSeries.map (residue ↥(OL LL))) * (A i).map (PowerSeries.map (residue ↥(OL LL))) := by
  have hc : ∀ v : Fin n → ↥LL.1, (homOf hr hr'' a'' ha'').f v = (homOf hr' hr'' a' ha').f ((homOf hr hr' a ha).f v) := by
    intro v
    show (a''.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec v =
      (a'.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec ((a.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec v)
    rw [e, Matrix.map_mul, Matrix.mulVec_mulVec]
  rw [GlobalTheory.T.wachModuleMapMatrix_comp_mul (HW l) K LL hA (latOf r hr) (latOf r' hr') (latOf r'' hr'') n n' n'' b b' b''
    (homOf hr hr' a ha) (homOf hr' hr'' a' ha') (homOf hr hr'' a'' ha'') A A' A'' h h' h'' hc i, Matrix.map_mul]

include F Cm in
set_option maxHeartbeats 1000000 in

theorem exists_positions {n t h R : ℕ} {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} {ψ : Fin t → ↥(GK K) →* GL (Fin 1) ↥(OL LL)}
    {U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Fin n → ℤ} {wt : Fin t → ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℤ}
    (hr : MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb r fun i => Finset.univ.val.map (U i)) (hU : ∀ i a, 0 ≤ U i a ∧ U i a ≤ h)
    (hψ : ∀ s, MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb (ψ s) fun i => {wt s i}) (hwt : ∀ s i, 0 ≤ wt s i ∧ wt s i ≤ h)
    {x : GalMats ↥(GK K) ↥(OL LL) n t R} {rs : Fin t → Fin R} {dim : Fin (R + 1) → ℕ}
    (hx : x.Chain (residue ↥(OL LL)) r ψ rs dim) {u : ℤ_[l]ˣ} {c : ℤ_[l]} {un : (↥(OL LL))⟦X⟧} {ζ : ↥(OL LL)}
    {jj : ℕ → (↥(OL LL))⟦X⟧ →+* (↥LL.1)⟦X⟧} (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c) (hun : IsUn l ↥(OL LL) (u : ℤ_[l]) un)
    (hζ : IsPrimitiveRoot ζ l) (hjj : ∀ a ∈ Finset.Ioo 0 l, IsExpAt (OL LL).val.toRingHom (ζ ^ a) (jj a)) :
    ∃ (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (Nψ : Fin t → Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) 1 ↥(OL LL)) (y : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Slot (ResidueField ↥(OL LL)) n t R), ∀ i,
      LatAt l (N.P i) (N.D i) (N.Th i) h u (U i) (OL LL).val.toRingHom jj ∧
      (∀ s, LatAt l ((Nψ s).P i) ((Nψ s).D i) ((Nψ s).Th i) h u (fun _ => wt s i) (OL LL).val.toRingHom jj) ∧
      (y i).Chain (y (i - 1)) l (PowerSeries.map (residue ↥(OL LL)) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) (fun s => ((Nψ s).P i).map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => ((Nψ s).D i).map (PowerSeries.map (residue ↥(OL LL)))) rs dim := by
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.wachRingFacts_unramified_levelOne (HW l) K LL hA).2.2.2.1 u
  have hU0 : ∀ i, ∀ v ∈ Finset.univ.val.map (U i), 0 ≤ v := fun i v hv => by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hv
    exact (hU i a).1
  have hone : ∀ w : ℤ, (Finset.univ.val.map fun _ : Fin 1 => w) = {w} := fun w => by simp
  have hψ' : ∀ s, MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb (ψ s)
      (fun i => Finset.univ.val.map fun _ : Fin 1 => wt s i) := fun s => by
    simpa only [hone] using hψ s
  have hψ0 : ∀ s i, ∀ v ∈ Finset.univ.val.map (fun _ : Fin 1 => wt s i), 0 ≤ v := fun s i v hv => by
    rw [hone, Multiset.mem_singleton] at hv
    rw [hv]
    exact (hwt s i).1
  have hrk : ∀ k, MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb (x.rk k) (fun i => Finset.univ.val.map (U i)) :=
    fun k => GlobalTheory.T.isContinuousCrystallineMatrixRep_of_intertwines_det_ne_zero (D.loc l) K LL _ n _ r (x.rk k) _ (x.a k) hr (hx.1 k).1 (hx.1 k).2.1
  have hr2 : ∀ s, MatGood (D.loc l) ((HW l).W K 1 LL hA.2.2).emb (x.r2 s)
      (fun i => Finset.univ.val.map (U i) + {wt s i}) :=
    fun s => GlobalTheory.T.matGood_of_block_extension_twist (D.loc l) (D.locA l) (D.locT l) K LL _ n _ r (ψ s) (x.r2 s) _ _ (x.B s) (x.C s) hr (hψ s)
      (hx.2.2 s).1 (hx.2.2 s).2.2.1 (hx.2.2 s).2.2.2.2.2.2.2.2.2.2
  have hr20 : ∀ s i, ∀ v ∈ Finset.univ.val.map (U i) + {wt s i}, 0 ≤ v := fun s i v hv => by
    rcases Multiset.mem_add.mp hv with hv | hv
    · exact hU0 i v hv
    · rw [Multiset.mem_singleton] at hv
      rw [hv]
      exact (hwt s i).1
  obtain ⟨b0, N0, hb0⟩ := exists_frame F Cm hA hr hU0 γ
  choose bk Nk hbk using fun k : Fin (R + 1) => exists_frame F Cm hA (hrk k) hU0 γ
  choose bψ Nψ hbψ using fun s : Fin t => exists_frame F Cm hA (hψ' s) (hψ0 s) γ
  choose b2 N2 hb2 using fun s : Fin t => exists_frame F Cm hA (hr2 s) (hr20 s) γ
  choose Aa hAa1 hAa2 hAa3 using fun k : Fin (R + 1) =>
    exists_mapMat F hA (hrk k) hr (hbk k) hb0 hγ hun (hx.1 k).1
  choose Ab hAb1 hAb2 hAb3 using fun k : Fin R =>
    exists_mapMat F hA (hrk k.castSucc) (hrk k.succ) (hbk k.castSucc) (hbk k.succ) hγ hun (hx.2.1 k).1
  choose AB hAB1 hAB2 hAB3 using fun s : Fin t =>
    exists_mapMat F hA (hr2 s) hr (hb2 s) hb0 hγ hun (hx.2.2 s).1
  choose AB' hAB'1 hAB'2 hAB'3 using fun s : Fin t =>
    exists_mapMat F hA (hr2 s) (hrk (rs s).succ) (hb2 s) (hbk (rs s).succ) hγ hun (hx.2.2 s).2.1
  choose AC hAC1 hAC2 hAC3 using fun s : Fin t =>
    exists_mapMat F hA (hr2 s) (hψ' s) (hb2 s) (hbψ s) hγ hun (hx.2.2 s).2.2.1
  choose AE hAE1 hAE2 hAE3 using fun s : Fin t =>
    exists_mapMat F hA (hrk (rs s).castSucc) (hr2 s) (hbk (rs s).castSucc) (hb2 s) hγ hun (hx.2.2 s).2.2.2.1
  choose AZ hAZ1 hAZ2 hAZ3 using fun s : Fin t =>
    exists_mapMat F hA (hrk (rs s).castSucc) (hψ' s) (hbk (rs s).castSucc) (hbψ s) hγ hun (a := 0)
      (fun g => by simp)
  refine ⟨N0, Nψ, fun i =>
    { Pk := fun k => ((Nk k).P i).map (PowerSeries.map (residue ↥(OL LL)))
      Dk := fun k => ((Nk k).D i).map (PowerSeries.map (residue ↥(OL LL)))
      A := fun k => (Aa k i).map (PowerSeries.map (residue ↥(OL LL)))
      Bb := fun k => (Ab k i).map (PowerSeries.map (residue ↥(OL LL)))
      P2 := fun s => ((N2 s).P i).map (PowerSeries.map (residue ↥(OL LL)))
      D2 := fun s => ((N2 s).D i).map (PowerSeries.map (residue ↥(OL LL)))
      B := fun s => (AB s i).map (PowerSeries.map (residue ↥(OL LL)))
      B' := fun s => (AB' s i).map (PowerSeries.map (residue ↥(OL LL)))
      C := fun s => (AC s i).map (PowerSeries.map (residue ↥(OL LL)))
      E := fun s => (AE s i).map (PowerSeries.map (residue ↥(OL LL))) }, fun i => ⟨?_, fun s => ?_, ?_⟩⟩
  · exact latAt_of_frame F Cm hA hr hU hb0 hγ hu hζ hjj i
  · exact latAt_of_frame F Cm hA (hψ' s) (fun i _ => hwt s i) (hbψ s) hγ hu hζ hjj i
  · refine ⟨fun k => ⟨hAa2 k i, (hAa3 k i).trans (hx.1 k).2.2⟩, fun k => ?_,
      fun s => ⟨hAB2 s i, hAC2 s i, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact mapMat_mul hA (hAb1 k) (hAa1 k.succ) (hAa1 k.castSucc) (hx.2.1 k).2 i
    · exact (mapMat_mul hA (hAE1 s) (hAB1 s) (hAa1 (rs s).castSucc) (hx.2.2 s).2.2.2.2.1.symm i).symm
    · have h0 := mapMat_mul hA (hAE1 s) (hAC1 s) (hAZ1 s) (hx.2.2 s).2.2.2.2.2.1.symm i
      have hz := eq_zero_of_lrank _ ((hAZ3 s i).trans (by simp))
      exact h0.symm.trans hz
    · exact mapMat_mul hA (hAB'1 s) (hAa1 (rs s).succ) (hAB1 s) (hx.2.2 s).2.2.2.2.2.2.1 i
    · exact (hAE3 s i).trans (hx.2.2 s).2.2.2.2.2.2.2.1
    · exact (hAC3 s i).trans (hx.2.2 s).2.2.2.2.2.2.2.2.1
    · exact (hAB'3 s i).trans (hx.2.2 s).2.2.2.2.2.2.2.2.2.1

end Functor

theorem glue_orbits {ι X : Type} (σ : Equiv.Perm ι) (Rel : ι → X → X → Prop)
    (h : ∀ i₀, ∃ (ι' : Type) (σ' : Equiv.Perm ι') (κ : ι' → ι) (x : ι' → X), Function.Injective κ ∧
      (∀ j, κ (σ' j) = σ (κ j)) ∧ i₀ ∈ Set.range κ ∧ ∀ j, Rel (κ j) (x j) (x (σ' j))) :
    ∃ x : ι → X, ∀ i, Rel i (x i) (x (σ i)) := by
  classical
  choose ι' σ' κ x hκ hcomm hmem hrel using h
  by_cases hne : Nonempty X
  · obtain ⟨x₀⟩ := hne
    obtain ⟨r, hr, hrσ⟩ : ∃ r : ι → ι, (∀ i, σ.SameCycle (r i) i) ∧ ∀ i, r (σ i) = r i :=
      ⟨fun i => (Quotient.mk'' i : Quotient (Equiv.Perm.SameCycle.setoid σ)).out,
        fun i => by exact Quotient.mk_out' (s₁ := Equiv.Perm.SameCycle.setoid σ) i,
        fun i => congrArg Quotient.out
          (Quotient.sound' (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl σ i)))⟩
    have hpow : ∀ k (m : ℤ) j, (σ ^ m) (κ k j) = κ k ((σ' k ^ m) j) := by
      intro k m
      induction m using Int.induction_on with
      | zero => intro j; simp
      | succ m ih =>
        intro j
        rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hcomm, ih]
      | pred m ih =>
        intro j
        rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← ih]
        congr 1
        rw [Equiv.Perm.inv_eq_iff_eq, ← hcomm, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have hin : ∀ i, ∃ j, κ (r i) j = i := fun i => by
      obtain ⟨m, hm⟩ := hr i
      obtain ⟨j₀, hj₀⟩ := hmem (r i)
      exact ⟨(σ' (r i) ^ m) j₀, by rw [← hpow, hj₀, hm]⟩
    refine ⟨fun i => Function.extend (κ (r i)) (x (r i)) (fun _ => x₀) i, fun i => ?_⟩
    obtain ⟨j, hj⟩ := hin i
    have e1 := (hκ (r i)).extend_apply (x (r i)) (fun _ => x₀) j
    have e2 := (hκ (r i)).extend_apply (x (r i)) (fun _ => x₀) (σ' (r i) j)
    rw [hj] at e1
    rw [hcomm, hj] at e2
    have h3 := hrel (r i) j
    rw [hj] at h3
    show Rel i (Function.extend (κ (r i)) (x (r i)) (fun _ => x₀) i)
      (Function.extend (κ (r (σ i))) (x (r (σ i))) (fun _ => x₀) (σ i))
    rw [hrσ i, e1, e2]
    exact h3
  · have hι : IsEmpty ι := ⟨fun i => by obtain ⟨j, -⟩ := hmem i; exact hne ⟨x i j⟩⟩
    exact ⟨fun i => (hι.false i).elim, fun i => (hι.false i).elim⟩

end GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace

set_option maxHeartbeats 1000000 in

theorem exists_positions_global (hBS : GlobalTheory.Published.BhattScholzeCrystallineLattices) {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (hd : ¬ (l : ℤ) ∣ NumberField.discr E)
    {σ : Equiv.Perm (E →+* PadicAlgCl l)} (hσ : GlobalTheory.ExpFrame.IsFrobPerm σ) {n t h R : ℕ}
    {J : (E →+* PadicAlgCl l) → Fin n → ℤ} {wt : Fin t → (E →+* PadicAlgCl l) → ℤ}
    (hJ : ∀ i a, 0 ≤ J i a ∧ J i a ≤ h) (hwt : ∀ s i, 0 ≤ wt s i ∧ wt s i ≤ h) {LL : FinExt l}
    (hz : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) (hE : ∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1)
    {r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)} {ψ : Fin t → (Ω ≃ₐ[E] Ω) →* GL (Fin 1) ↥(OL LL)}
    (hr : GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) fun τ => Finset.univ.val.map (J τ))
    (hψ : ∀ s, GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp (ψ s)) fun τ => {wt s τ})
    {x : GalMats (Ω ≃ₐ[E] Ω) ↥(OL LL) n t R} {rs : Fin t → Fin R} {dim : Fin (R + 1) → ℕ}
    (hx : x.Chain (residue ↥(OL LL)) r ψ rs dim) {u : ℤ_[l]ˣ} {c : ℤ_[l]} {un : (↥(OL LL))⟦X⟧} {ζ : ↥(OL LL)}
    {jj : ℕ → (↥(OL LL))⟦X⟧ →+* (↥LL.1)⟦X⟧} (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c)
    (hun : IsUn l ↥(OL LL) (u : ℤ_[l]) un) (hζ : IsPrimitiveRoot ζ l)
    (hjj : ∀ a ∈ Finset.Ioo 0 l, IsExpAt (OL LL).val.toRingHom (ζ ^ a) (jj a)) :
    ∃ (N : Lat (E →+* PadicAlgCl l) n ↥(OL LL)) (Nψ : Fin t → Lat (E →+* PadicAlgCl l) 1 ↥(OL LL))
      (y : (E →+* PadicAlgCl l) → Slot (ResidueField ↥(OL LL)) n t R),
      LatN l N h u J (OL LL).val.toRingHom jj ∧
      (∀ s, LatN l (Nψ s) h u (fun i _ => wt s i) (OL LL).val.toRingHom jj) ∧
      ∀ i, (y i).Chain (y (σ i)) l (PowerSeries.map (residue ↥(OL LL)) un)
        ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => ((Nψ s).P i).map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => ((Nψ s).D i).map (PowerSeries.map (residue ↥(OL LL)))) rs dim := by
  obtain ⟨D⟩ := GlobalTheory.MemLoc.record_nonempty
  obtain ⟨HW, F, ⟨Cm⟩, -⟩ := GlobalTheory.HWL.exists_hw_fon_cmp_ties hBS D.loc D.locA D.locT
  obtain ⟨xg, hxg⟩ := glue_orbits
    (X := (Mx (↥(OL LL))⟦X⟧ n n × Mx (↥(OL LL))⟦X⟧ n n × Mx ↥(OL LL) n n) ×
      (Fin t → Mx (↥(OL LL))⟦X⟧ 1 1 × Mx (↥(OL LL))⟦X⟧ 1 1 × Mx ↥(OL LL) 1 1) ×
      Slot (ResidueField ↥(OL LL)) n t R) σ
    (fun τ d d' =>
      LatAt l d.1.1 d.1.2.1 d.1.2.2 h u (J τ) (OL LL).val.toRingHom jj ∧
      (∀ s, LatAt l (d.2.1 s).1 (d.2.1 s).2.1 (d.2.1 s).2.2 h u (fun _ => wt s τ) (OL LL).val.toRingHom jj) ∧
      d.2.2.Chain d'.2.2 l (PowerSeries.map (residue ↥(OL LL)) un)
        (d.1.1.map (PowerSeries.map (residue ↥(OL LL)))) (d.1.2.1.map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => (d.2.1 s).1.map (PowerSeries.map (residue ↥(OL LL))))
        (fun s => (d.2.1 s).2.1.map (PowerSeries.map (residue ↥(OL LL)))) rs dim)
    (fun i₀ => by
      obtain ⟨K, hA, ι, κ, hκ, hκσ, hi₀, hMG⟩ :=
        GlobalTheory.T.exists_unramifiedLocalSituation_of_embedding (D.loc l) (D.locA l) (D.locT l) (HW l) E Ω hl hd σ hσ LL hz hE i₀
      obtain ⟨N, Nψ, y, hy⟩ := exists_positions F Cm hA (U := fun i => J (κ i)) (wt := fun s i => wt s (κ i))
        (hMG n r _ hr) (fun i a => hJ (κ i) a) (fun s => hMG 1 (ψ s) _ (hψ s)) (fun s i => hwt s (κ i))
        (hx.res ι) hu hun hζ hjj
      exact ⟨ZMod (Module.finrank ℚ_[l] ↥(K0 K)), Equiv.subRight 1, κ,
        fun j => ((N.P j, N.D j, N.Th j), fun s => ((Nψ s).P j, (Nψ s).D j, (Nψ s).Th j), y j),
        hκ, fun j => hκσ j, hi₀, fun j => hy j⟩)
  exact ⟨⟨fun i => (xg i).1.1, fun i => (xg i).1.2.1, fun i => (xg i).1.2.2⟩,
    fun s => ⟨fun i => ((xg i).2.1 s).1, fun i => ((xg i).2.1 s).2.1, fun i => ((xg i).2.1 s).2.2⟩,
    fun i => (xg i).2.2, (latN_iff l _ h u J _ jj).2 fun i => (hxg i).1,
    fun s => (latN_iff l _ h u _ _ jj).2 fun i => (hxg i).2.1 s, fun i => (hxg i).2.2⟩

end GlobalTheory.WachPlace

end
end
