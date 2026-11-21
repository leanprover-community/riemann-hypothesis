import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibilityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqStdPowerSeriesAtZeroStatement
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachCrystallineComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrH1Description
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAndIsogenyInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValOfPowAssociated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelCrystallineSurjectionKilledByXPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds

section
noncomputable section

namespace GlobalTheory.NL.LetterFree

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem letE_mul (i : ZMod n) (a : LetA O n) : (letE i : LetA O n) * a = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem single_mul_letE (i : ZMod n) (a : PowerSeries O) :
    (Pi.single i a : LetA O n) * letE i = Pi.single i a := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i :=
  single_mul_letE i 1

theorem letE_mul_ne {i j : ZMod n} (h : i ≠ j) : (letE i : LetA O n) * letE j = 0 := by
  rw [letE_mul]
  simp [letE, h]

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem sum_letE_smul [NeZero n] (x : W.DD T) : ∑ i : ZMod n, (letE i : LetA O n) • x = x := by
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • (letE i : LetA O n) • y = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

theorem lettersDecompose [NeZero n] : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose W T := by
  refine ⟨?_, le_antisymm (iSup_le fun i x hx => ((mem_Nl_iff W T i x).1 hx).1) fun x hx => ?_⟩
  · intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hk : (⨆ (j) (_ : j ≠ i), W.Nl T j) ≤
        LinearMap.ker (LinearMap.lsmul (LetA O n) (W.DD T) (letE i)) := by
      refine iSup_le fun j => iSup_le fun hj y hy => ?_
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ← ((mem_Nl_iff W T j y).1 hy).2, smul_smul,
        letE_mul_ne hj.symm, zero_smul]
    have h0 := hk hx'
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ((mem_Nl_iff W T i x).1 hx).2] at h0
    exact h0
  · rw [← sum_letE_smul W T x]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨x, hx, rfl⟩

theorem isLetterBasis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis W T i (fun k => (letE i : LetA O n) • (b k : W.DD T)) := by
  have hli : LinearIndependent (LetA O n) (fun k => (b k : W.DD T)) :=
    b.linearIndependent.map' (W.N T).subtype (W.N T).ker_subtype
  refine ⟨fun k => ⟨b k, (b k).2, rfl⟩, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hy' : y = ∑ k, b.repr ⟨y, hy⟩ k • (b k : W.DD T) := by
    have := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this.symm
  generalize b.repr ⟨y, hy⟩ = a at hy'
  subst hy'
  have key : (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) =
      ∑ k, (Pi.single i (a k i) : LetA O n) • (b k : W.DD T) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, letE_mul]
  refine ⟨fun k => a k i, ?_, fun c hc => ?_⟩
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _
    rw [key]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, single_mul_letE]
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _ at hc
    rw [key] at hc
    simp only [smul_smul, single_mul_letE] at hc
    funext k
    have h0 := Fintype.linearIndependent_iff.1 hli
      (fun k => (Pi.single i (c k) : LetA O n) - Pi.single i (a k i))
      (by simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]) k
    have h1 := congrFun h0 i
    simpa [sub_eq_zero] using h1

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule

theorem exists_letter_basis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    ∃ c : Module.Basis (Fin r) (PowerSeries O) ↥(W.Nl T i),
      ∀ k, (c k : W.DD T) = (letE i : LetA O n) • (b k : W.DD T) := by
  obtain ⟨hm, hu⟩ := isLetterBasis W T b i
  let f : Fin r → ↥(W.Nl T i) := fun k => ⟨_, hm k⟩
  have hs : ∀ c : Fin r → PowerSeries O, ((∑ k, c k • f k : ↥(W.Nl T i)) : W.DD T) =
      ∑ k, (Pi.single i (c k) : LetA O n) • (letE i : LetA O n) • (b k : W.DD T) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul W T i (c k) (f k)
  have hli : LinearIndependent (PowerSeries O) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 := hs c
    rw [hc] at h1
    have h2 := (hu 0 (Submodule.zero_mem _)).unique h1 (y₂ := fun _ => 0) (by simp)
    exact congrFun h2 k
  have hsp : ⊤ ≤ Submodule.span (PowerSeries O) (Set.range f) := by
    intro x _
    obtain ⟨c, hc, -⟩ := hu x.1 x.2
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hs c).trans hc.symm)⟩
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

end Generic

theorem letters_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose (H.W K s LL h) T ∧ GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersFree (H.W K s LL h) T ∧
      ∀ i, ∃ b : Fin (Module.finrank ↥(OL LL) ↥T.L.T) → (H.W K s LL h).DD T,
        GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis (H.W K s LL h) T i b := by
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨b⟩ := N_basis_loc H K s LL h T hT
  exact ⟨lettersDecompose _ T, fun i => ⟨(exists_letter_basis _ T b i).choose⟩,
    fun i => ⟨_, isLetterBasis _ T b i⟩⟩

end GlobalTheory.NL.LetterFree
end
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LetterFree

theorem letters_free : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), WachLatticeFreeGlobal D HW F := by
  intro D HW F l _ K s LL h T hT
  obtain ⟨hd, -, hb⟩ := letters_loc (HW l) K s LL h T hT
  refine ⟨hd.2.symm, fun i => ?_⟩
  obtain ⟨b, hb1, hb2⟩ := hb i
  exact ⟨_, b, hb1, hb2⟩

end GlobalTheory.NL.LetterFree
end

section
noncomputable section

namespace GlobalTheory.NL.CmpCris

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_one (f : ℤ → M) : conv (1 : PowerSeries LL) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem conv_zero_coeff (e : PowerSeries LL) (f : ℤ → M) (hf : ∀ k < (0 : ℤ), f k = 0) :
    conv e f 0 = PowerSeries.constantCoeff e • f 0 := by
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [hf _ (by omega), smul_zero]

theorem mem_latSpan {ι : Type} (ex : ι → ℤ → M) (x : ι) : ex x ∈ latSpan (LL := LL) ex :=
  Submodule.subset_span ⟨1, x, (conv_one _).symm⟩

theorem neg_eq_zero_of_std {ι : Type} {D : Submodule LL M} {ex : ι → ℤ → M}
    (h : Std D (latSpan (LL := LL) ex)) (x : ι) : ∀ k < (0 : ℤ), ex x k = 0 :=
  ((h _).1 (mem_latSpan ex x)).2

theorem full_of_std {D : Submodule LL M} {Λ : Submodule LL (ℤ → M)} (h : Std D Λ) : Full D Λ :=
  ⟨0, fun f h1 h2 => (h f).2 ⟨h1, by simpa using h2⟩⟩

theorem span_const_of_std {ι : Type} {D : Submodule LL M} {ex : ι → ℤ → M}
    (h : Std D (latSpan (LL := LL) ex)) :
    Submodule.span LL (Set.range fun x => ex x 0) = D := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ((h _).1 (mem_latSpan ex x)).1 0
  · intro d hd
    have h1 : (Pi.single (0 : ℤ) d : ℤ → M) ∈ latSpan (LL := LL) ex := by
      refine (h _).2 ⟨fun k => ?_, fun k hk => Pi.single_eq_of_ne hk.ne _⟩
      by_cases hk : k = 0
      · subst hk; simpa using hd
      · rw [Pi.single_eq_of_ne hk]; exact D.zero_mem
    have h2 : latSpan (LL := LL) ex ≤ (Submodule.span LL (Set.range fun x => ex x 0)).comap
        (LinearMap.proj (R := LL) (φ := fun _ : ℤ => M) 0) := by
      unfold latSpan
      rw [Submodule.span_le]
      rintro _ ⟨e, x, rfl⟩
      change conv e (ex x) 0 ∈ Submodule.span LL (Set.range fun x => ex x 0)
      rw [conv_zero_coeff e _ (neg_eq_zero_of_std h x)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    simpa using h2 h1

theorem exists_shift_of_std {D : Submodule LL M} {Λ : Submodule LL (ℤ → M)} (h : Std D Λ)
    (g : ℤ → M) (hg : g ∈ Λ) (h0 : g 0 = 0) : ∃ f ∈ Λ, ∀ j : ℤ, g j = f (j - ((1 : ℕ) : ℤ)) := by
  obtain ⟨h1, h2⟩ := (h g).1 hg
  refine ⟨fun j => g (j + 1), (h _).2 ⟨fun k => h1 _, fun k hk => ?_⟩, fun j => by simp⟩
  rcases (show k + 1 < 0 ∨ k + 1 = 0 by omega) with h3 | h3
  · exact h2 _ h3
  · rw [h3, h0]

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem prim_one (p : ℕ) : ∃ j : ℕ, IsPrimitiveRoot (1 : LL) (p ^ j) :=
  ⟨0, by simpa using IsPrimitiveRoot.one⟩

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem const_lev_π (i : ZMod n) : PowerSeries.constantCoeff (W.lev i 1 letπ) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 (prim_one _)
  have := congrArg PowerSeries.constantCoeff hE
  simpa [hE0] using this

theorem const_lev (i : ZMod n) (a : LetA O n) :
    PowerSeries.constantCoeff (W.lev i 1 a) = algebraMap O LL (PowerSeries.constantCoeff (a i)) := by
  obtain ⟨b, hb⟩ : (PowerSeries.X : PowerSeries O) ∣
      a i - PowerSeries.C (PowerSeries.constantCoeff (a i)) := by
    rw [PowerSeries.X_dvd_iff]; simp
  have h := W.lev_letter i 1
    (a - algebraMap O (LetA O n) (PowerSeries.constantCoeff (a i)) - letπ * fun _ => b) (by
      simp only [Pi.sub_apply, Pi.mul_apply, letπ, Pi.algebraMap_apply]
      rw [← hb]
      simp [PowerSeries.algebraMap_apply])
  rw [map_sub, map_sub, map_mul, AlgHom.commutes] at h
  have h2 := congrArg PowerSeries.constantCoeff h
  rw [map_sub, map_sub, map_mul, const_lev_π, zero_mul, sub_zero, map_zero, sub_eq_zero] at h2
  rw [h2]
  simp [PowerSeries.algebraMap_apply]

theorem const_lev_Q (i : ZMod n) : PowerSeries.constantCoeff (W.lev i 1 W.Q) = (PD.p : LL) := by
  rw [LevPt.Q_eq, map_sum, map_sum]
  simp [const_lev_π]

theorem π_dvd_of_van (hinj : Function.Injective (algebraMap O LL)) (a : LetA O n)
    (ha : ∀ i, a ∈ van W i 1 1) : (letπ : LetA O n) ∣ a := by
  have h : ∀ i, (PowerSeries.X : PowerSeries O) ∣ a i := by
    intro i
    have h1 := ha i
    rw [van, Ideal.mem_comap, Ideal.mem_span_singleton, pow_one, PowerSeries.X_dvd_iff,
      const_lev] at h1
    rw [PowerSeries.X_dvd_iff]
    exact hinj (by rw [h1, map_zero])
  choose b hb using h
  exact ⟨b, funext hb⟩

theorem cmp_eq_sum [NeZero n] (T : LocLat G Qp LL O) (x : ↥(W.N T)) :
    W.cmp T x = ∑ i : ZMod n, W.cmp T ((letE i : LetA O n) • x) := by
  rw [← map_sum, ← Finset.sum_smul, sum_letE, one_smul]

theorem cmp_iso_of_expansions [NeZero n] (hinj : Function.Injective (algebraMap O LL))
    (T : LocLat G Qp LL O) (ex : ZMod n → ↥(W.N T) → ℤ → T.V ⊗[Qp] B)
    (hcmp : ∀ i x, W.cmp T ((letE i : LetA O n) • x) = ex i x 0)
    (hstd : ∀ i, Std (DcrisL PD T.ρ (W.emb i)) (latSpan (LL := LL) (ex i)))
    (hsup : (⨆ i, DcrisL PD T.ρ (W.emb i)) = Dcris PD T.ρ)
    (hind : iSupIndep fun i => DcrisL PD T.ρ (W.emb i))
    {r : ℕ} (nb : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hvan : ∀ i (y : ↥(W.N T)), (∃ f ∈ latSpan (LL := LL) (ex i), ∀ j : ℤ,
      ex i y j = f (j - ((1 : ℕ) : ℤ))) → ∀ j, nb.repr y j ∈ van W i 1 1)
    (hφ : ∀ (i : ZMod n) (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T),
      ex i ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ 0 =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i 1 (W.Q ^ m)) •
          (((PD.p : LL) ^ ((0 : ℤ) - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (ex (i - 1) x (0 - (j : ℤ))))) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison.CmpIso W PD.p T := by
  have hlet : ∀ i : ZMod n, Submodule.span LL
      (Set.range fun x : ↥(W.N T) => W.cmp T ((letE i : LetA O n) • x)) =
        DcrisL PD T.ρ (W.emb i) := by
    intro i
    simp only [hcmp]
    exact span_const_of_std (hstd i)
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, ?_, hlet, ?_⟩
  · rw [cmp_eq_sum] at hx
    have h0 : ∀ i, ex i x 0 = 0 := by
      intro i
      rw [← hcmp]
      exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).1 hind Finset.univ
        (fun i => W.cmp T ((letE i : LetA O n) • x)) (fun i _ => W.cmp_letter T i x) hx i
        (Finset.mem_univ _)
    have hv : ∀ j, (letπ : LetA O n) ∣ nb.repr x j := fun j =>
      π_dvd_of_van W hinj _ fun i =>
        hvan i x (exists_shift_of_std (hstd i) _ (mem_latSpan _ x) (h0 i)) j
    choose b hb using hv
    refine ⟨∑ j, b j • nb j, ?_⟩
    rw [Finset.smul_sum]
    conv_lhs => rw [← nb.sum_repr x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb j, mul_smul]
  · rintro ⟨y, rfl⟩
    exact W.cmp_π T y
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact W.cmp_mem T x
    · rw [← hsup, iSup_le_iff]
      intro i
      rw [← hlet i]
      apply Submodule.span_mono
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · intro x m hx
    rw [cmp_eq_sum W T x, cmp_eq_sum, map_sum, Finset.smul_sum,
      ← Equiv.sum_comp (Equiv.subRight (1 : ZMod n))
        (fun i => (PD.p : LL) ^ m •
          φVB PD (LL := LL) (V := T.V) (W.cmp T ((letE i : LetA O n) • x)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcmp, hcmp, Equiv.subRight_apply, hφ, finsum_eq_single _ 0]
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, map_pow, const_lev_Q]
      simp only [Nat.cast_zero, sub_zero, zpow_zero, one_smul]
    · intro j hj
      rw [neg_eq_zero_of_std (hstd (i - 1)) x (0 - (j : ℤ)) (by omega), map_zero, smul_zero,
        smul_zero]

end Generic

set_option maxHeartbeats 1000000 in

theorem cmp_iso (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison.CmpIso ((HW l).W K s LL h) ((D.loc l).PD K).p T := by
  have := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hstd := GlobalTheory.T.wach_lattice_eq_std_powerSeries_at_zero D HW F Cm l K s LL h T hT
  have hD := GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  exact cmp_iso_of_expansions ((HW l).W K s LL h) Subtype.val_injective T
    (fun i => ex (Cm l) h T i 1) (fun i x => ((Cm l).C K s LL h).tie.cmp_eq T hT i x) hstd
    hD.2.1 hD.2.2.1 nb
    (fun i y => (((GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i 1 (prim_one l)
        (full_of_std (hstd i))).2 _ nb).2.2 y 1).1)
    (fun i x m hx => by
      have key := ((Cm l).C K s LL h).tie.levB_φ T hT i 1 (prim_one _) x m hx 0
      have h1 : (1 : ↥LL.1) ^ ((D.loc l).PD K).p = 1 := one_pow _
      simp only [h1] at key
      unfold ex
      exact key)

end GlobalTheory.NL.CmpCris
end
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.CmpCris

theorem wachLattice_comparison_dcris (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : P3 D HW F Cm := by
  intro l _ K s LL h T hT
  obtain ⟨h1, h2, -, h4⟩ := cmp_iso D HW F Cm l K s LL h T hT
  refine ⟨fun x hx => ?_, h2, fun x k hk => h4 x k hk⟩
  obtain ⟨y, rfl⟩ := (h1 x).1 hx
  exact ⟨y, y.2, rfl⟩

end GlobalTheory.NL.CmpCris
end
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.NL.FiniteRestrictionH1f

theorem coboundary_of_finiteIndex {G M k : Type} [Group G] [Field k] [CharZero k] [AddCommGroup M]
    [Module k M] (a : G → M →ₗ[k] M) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (H : Subgroup G) [H.FiniteIndex] (c : G → M) (hc : ∀ g h, c (g * h) = c g + a g (c h))
    (b : M) (hb : ∀ h ∈ H, c h = a h b - b) : ∃ x : M, ∀ g, c g = a g x - x := by
  classical
  let d : G → M := fun g => c g - (a g b - b)
  have hd : ∀ g h, d (g * h) = d g + a g (d h) := by
    intro g h
    simp only [d, hc, ha, map_sub]
    abel
  have hd0 : ∀ h ∈ H, d h = 0 := fun h hh => by simp only [d, hb h hh, sub_self]
  have hdH : ∀ g g' : G, (QuotientGroup.leftRel H) g g' → d g = d g' := by
    intro g g' hgg
    rw [QuotientGroup.leftRel_apply] at hgg
    have : g' = g * (g⁻¹ * g') := by group
    rw [this, hd, hd0 _ hgg, map_zero, add_zero]
  let D : G ⧸ H → M := fun q => Quotient.liftOn' q d hdH
  have hD : ∀ (g : G) (q : G ⧸ H), D (g • q) = d g + a g (D q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H x => exact hd g x
  let _inst : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hn : ((Fintype.card (G ⧸ H) : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsum : ∀ g : G, ∑ q, D q = ((Fintype.card (G ⧸ H) : ℕ) : k) • d g + a g (∑ q, D q) := by
    intro g
    rw [← Equiv.sum_comp (MulAction.toPerm g) D]
    conv_rhs => rw [Equiv.sum_comp (MulAction.toPerm g) D]
    simp only [MulAction.toPerm_apply, hD, Finset.sum_add_distrib, map_sum, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  refine ⟨b - (((Fintype.card (G ⧸ H) : ℕ) : k))⁻¹ • ∑ q, D q, fun g => ?_⟩
  have h1 : d g = (((Fintype.card (G ⧸ H) : ℕ) : k))⁻¹ • (∑ q, D q - a g (∑ q, D q)) := by
    rw [← eq_sub_iff_add_eq.2 (hsum g).symm, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have h2 : c g = d g + (a g b - b) := by simp only [d]; abel
  rw [h2, h1, map_sub, map_smul, smul_sub]
  abel

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_tmul (g : G) (x : V) (b : B) :
    actVB PD ρ g (x ⊗ₜ[Qp] b) = ρ g x ⊗ₜ[Qp] PD.actB g b := rfl

theorem actVB_mul (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp only [actVB_tmul, map_mul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem crisCob_of_finiteIndex [CharZero LL] (H : Subgroup G) [H.FiniteIndex] (c : G → V)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (b : V ⊗[Qp] B)
    (hb : ∀ h ∈ H, c h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h b - b) :
    ∃ x : V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x :=
  coboundary_of_finiteIndex (actVB PD ρ) (actVB_mul PD ρ) H (fun g => c g ⊗ₜ[Qp] (1 : B))
    (fun g h => by simp only [hc, add_tmul, actVB_tmul, map_one]) b hb

end Generic

section Classes

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O)

theorem mem_H1fT_iff_res [CharZero LL] (H : Subgroup G) [H.FiniteIndex] (κ : LatticeCohomology T.L) :
    κ ∈ latticeFiniteCohomology PD T.L ↔ ∃ c : ↥(latticeCocycles (resLat T H)),
      (∃ x : T.V ⊗[Qp] B, ∀ h : ↥H,
        (c : ↥H → T.V) h ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ (h : G) x - x) ∧
      Submodule.Quotient.mk c = resH1 T H κ := by
  constructor
  · rintro ⟨z, ⟨-, -, x, hx⟩, rfl⟩
    exact ⟨⟨resFun T H z, resFun_Z1T T H z z.2⟩, ⟨x, fun h => hx (h : G)⟩, rfl⟩
  · rintro ⟨c, ⟨x, hx⟩, hc⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
    have hc' : (Submodule.Quotient.mk c : LatticeCohomology (resLat T H)) =
        Submodule.Quotient.mk ⟨resFun T H z, resFun_Z1T T H z z.2⟩ := hc
    obtain ⟨y, -, hy⟩ := (Submodule.Quotient.eq _).1 hc'
    refine ⟨z, ⟨z.2, z.2.1, ?_⟩, rfl⟩
    refine crisCob_of_finiteIndex PD T.ρ H z z.2.1.2 (x - y ⊗ₜ[Qp] (1 : B)) fun h hh => ?_
    have h1 : T.ρ h y - y = (c : ↥H → T.V) ⟨h, hh⟩ - (z : G → T.V) h := congrFun hy ⟨h, hh⟩
    have h2 : (z : G → T.V) h = (c : ↥H → T.V) ⟨h, hh⟩ - (T.ρ h y - y) := by rw [h1]; abel
    rw [h2, sub_tmul, sub_tmul, hx ⟨h, hh⟩, map_sub, actVB_tmul, map_one]
    abel

end Classes

theorem GKs_finiteIndex {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (n : ℕ)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) : W.GKs.FiniteIndex := by
  have h1 : W.GKs = (GlobalTheory.Cyc.Gj K W.s).subgroupOf (GK K) := by
    ext x
    rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, Subgroup.mem_subgroupOf]
  have h2 : (GlobalTheory.Cyc.Gj K W.s).FiniteIndex := by
    have hlp : l.Prime := Fact.out
    constructor
    rw [GlobalTheory.Cyc.Gj, ← IntermediateField.finrank_eq_fixingSubgroup_index,
      GlobalTheory.Cyc.finrank_Ks K W.s W.s_pos]
    have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
      FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
        (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
    exact (Nat.mul_pos Module.finrank_pos
      (Nat.mul_pos (Nat.sub_pos_of_lt hlp.one_lt) (pow_pos hlp.pos _))).ne'
  rw [h1]
  infer_instance

end GlobalTheory.NL.FiniteRestrictionH1f
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.FiniteRestrictionH1f

theorem mem_H1f_iff_res_mem : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Pr2b D HW F := by
  intro D HW F l _ K s LL h T _ κ
  have hfin := GKs_finiteIndex (D.loc l) K LL _ ((HW l).W K s LL h)
  refine (mem_H1fT_iff_res ((D.loc l).PD K) T ((HW l).W K s LL h).GKs κ).trans ?_
  constructor
  · rintro ⟨c, hx, hc⟩
    exact ⟨c, ⟨c.2, c.2.1, hx⟩, hc⟩
  · rintro ⟨c, ⟨-, -, hx⟩, hc⟩
    exact ⟨c, hx, hc⟩

end GlobalTheory.NL.FiniteRestrictionH1f
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_expansion_at_low_level_points : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P4 D HW F Cm := by
  first | exact @GlobalTheory.NL.LatLevel.lattice_at_level | exact GlobalTheory.NL.LatLevel.lattice_at_level | (intros; apply GlobalTheory.NL.LatLevel.lattice_at_level <;> assumption)
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.Exact

theorem smul_eq_sum {O : Type} [CommRing O] {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M]
    [Module (LetA O n) M] [Module O M] [IsScalarTower O (LetA O n) M] (c : ℕ)
    (h : ∀ m : M, ((letπ : LetA O n) ^ c) • m = 0) (a : LetA O n) (m : M) :
    a • m = ∑ i : ZMod n, ∑ k ∈ Finset.range c,
      PowerSeries.coeff k (a i) • (((letE i : LetA O n) * (letπ : LetA O n) ^ k) • m) := by
  have ha : a = (∑ i : ZMod n, ∑ k ∈ Finset.range c,
      PowerSeries.coeff k (a i) • ((letE i : LetA O n) * (letπ : LetA O n) ^ k)) +
      (letπ : LetA O n) ^ c * (fun j => PowerSeries.mk fun k => PowerSeries.coeff (k + c) (a j)) := by
    funext j
    ext k
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, letπ, letE]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
    simp only [Pi.single_eq_same, one_mul, map_add, map_sum, PowerSeries.coeff_smul,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    by_cases hk : k < c
    · simp [hk, Nat.not_le.2 hk]
    · simp [hk, Nat.le_of_not_lt hk, Nat.sub_add_cancel (Nat.le_of_not_lt hk)]
  conv_lhs => rw [ha]
  rw [add_smul, mul_smul, h, add_zero, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_assoc]

theorem finite_of_pi_pow {O : Type} [CommRing O] {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M]
    [Module (LetA O n) M] [Module O M] [IsScalarTower O (LetA O n) M] [Module.Finite (LetA O n) M]
    (c : ℕ) (h : ∀ m : M, ((letπ : LetA O n) ^ c) • m = 0) : Module.Finite O M := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := LetA O n) (M := M)
  let S : Finset M := (Finset.univ ×ˢ Finset.range c ×ˢ s).image
    fun p => ((letE p.1 : LetA O n) * (letπ : LetA O n) ^ p.2.1) • p.2.2
  refine ⟨⟨S, eq_top_iff.2 fun x _ => ?_⟩⟩
  have hx : x ∈ Submodule.span (LetA O n) (s : Set M) := hs ▸ Submodule.mem_top
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hx
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [smul_eq_sum c h]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2
    ⟨(i, k, m), Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨hk, hm⟩⟩, rfl⟩))

theorem finiteLength_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {c : O}
    (hc : c ≠ 0) (h : ∀ x : M, c • x = 0) : IsFiniteLength O M := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) M := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem length_cokN_lt_top [NeZero n] [IsDomain O] [IsDiscreteValuationRing O]
    (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) (p c : ℕ)
    (hp0 : ((p : ℕ) : O) ≠ 0)
    (hl : ∀ z ∈ W.N T₂, ∃ y ∈ W.N T₁, W.map π y = ((p : ℕ) : LetA O n) ^ c • z)
    (hπ : ∀ z ∈ W.N T₂, ∃ y ∈ W.N T₁, W.map π y = (letπ : LetA O n) ^ c • z) :
    Module.length O (cokN W π) < ⊤ := by
  haveI : Module.Finite (LetA O n) ↥(W.N T₂) := Module.Finite.iff_fg.mpr (W.N_fg T₂)
  have hπ' : ∀ m : cokN W π, ((letπ : LetA O n) ^ c) • m = 0 := by
    intro m
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    obtain ⟨y, hy, e⟩ := hπ z hz
    exact ⟨y, hy, e⟩
  haveI := finite_of_pi_pow (O := O) c hπ'
  have hl' : ∀ m : cokN W π, ((p : ℕ) : O) ^ c • m = 0 := by
    intro m
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    obtain ⟨y, hy, e⟩ := hl z hz
    refine ⟨y, hy, ?_⟩
    change W.map π y = ((p : ℕ) : O) ^ c • z
    rw [e, ← algebraMap_smul (LetA O n) (((p : ℕ) : O) ^ c) z, map_pow, map_natCast]
  exact lt_top_iff_ne_top.2 (Module.length_ne_top_iff.2 (finiteLength_of_killed (pow_ne_zero c hp0) hl'))

end Generic

set_option maxHeartbeats 1600000 in

theorem exactness_of_N : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P6 D HW F := by
  intro D HW F Cm l _ K s LL h
  obtain ⟨h1, h2⟩ := GlobalTheory.NL.Isog.saturated_and_isogeny_invariant D HW F l K s LL h
  refine ⟨h1, h2, fun T₀ T₁ T₂ ι π c0 c1 c2 hses => ?_⟩
  have hex : Function.Injective (((HW l).W K s LL h).map ι) ∧
      Function.Exact (((HW l).W K s LL h).map ι) (((HW l).W K s LL h).map π) ∧
      Function.Surjective (((HW l).W K s LL h).map π) := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    T₀ T₁ T₂ ι π hses
  have h4 := GlobalTheory.T.mem_wachN_of_map_mem_saturated D HW F l K s LL h T₀ T₁ T₂ ι π c0 c1 c2 hses
  obtain ⟨c, hc⟩ := GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL h T₀ T₁ T₂ ι π c0 c1 c2 hses
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x _ hx => ?_, fun y hy hy0 => ?_, fun z hz => ?_, h4, ?_⟩
  · exact hex.1 (hx.trans (map_zero _).symm)
  · obtain ⟨x, hx⟩ := (hex.2.1 y).1 hy0
    exact ⟨0, x, h4 x (hx ▸ hy), by rw [hx, pow_zero, one_smul]⟩
  · obtain ⟨⟨y, hy, e⟩, -⟩ := hc z hz
    exact ⟨c, y, hy, by rw [e, hp]⟩
  · haveI := ((D.loc l).PD K).finK₀
    haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
    obtain ⟨_, -, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
      intro h0
      have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
      simp [(Fact.out : l.Prime).ne_zero] at this
    exact length_cokN_lt_top _ π l c hl0 (fun z hz => (hc z hz).1) (fun z hz => (hc z hz).2)

end GlobalTheory.NL.Exact
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_saturated_exactness_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P6 D HW F := by
  atlas_forward_decl GlobalTheory.NL.Exact.exactness_of_N
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.InvBasis

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem γD_smulA (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem mem_DelF_iff (g : W.Gam) : g ∈ W.DelF ↔ IsOfFinOrder g := by
  rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]

theorem sum_inv (x : W.DD T) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γD T δ (∑ d ∈ W.DelF, W.γD T d x) = ∑ d ∈ W.DelF, W.γD T d x := by
  rw [map_sum]
  rw [mem_DelF_iff] at hδ
  refine Finset.sum_bij' (fun d _ => δ * d) (fun d _ => δ⁻¹ * d) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_DelF_iff] at hd ⊢
    exact hδ.mul hd
  · intro d hd
    rw [mem_DelF_iff] at hd ⊢
    exact hδ.inv.mul hd
  · intro d _
    simp
  · intro d _
    simp
  · intro d _
    rw [W.γD_mul]

theorem exists_avg (hc : IsUnit ((W.DelF.card : ℕ) : O)) (x : ↥(W.N T)) :
    ∃ x' y : ↥(W.N T), (x' : W.DD T) ∈ W.NΔ T ∧ x' = x + (letπ : LetA O n) • y := by
  classical
  obtain ⟨c, hc⟩ := hc.exists_left_inv
  choose y hy hy' using fun g => W.N_π T g x x.2
  have hmem : ∀ z ∈ W.N T, c • z ∈ W.N T := fun z hz => by
    rw [← algebraMap_smul (LetA O n) c z]
    exact (W.N T).smul_mem _ hz
  have h1 : c • ∑ d ∈ W.DelF, W.γD T d x ∈ W.N T :=
    hmem _ (Submodule.sum_mem _ fun d _ => W.N_Γ T d x x.2)
  refine ⟨⟨_, h1⟩, ⟨c • ∑ d ∈ W.DelF, y d, hmem _ (Submodule.sum_mem _ fun d _ => hy d)⟩,
    ⟨h1, fun δ hδ => ?_⟩, ?_⟩
  · change W.γD T δ (c • _) = c • _
    rw [map_smul, sum_inv W T _ δ hδ]
  · apply Subtype.ext
    change c • _ = (x : W.DD T) + (letπ : LetA O n) • (c • ∑ d ∈ W.DelF, y d)
    have h2 : ∀ d ∈ W.DelF, W.γD T d x = x + (letπ : LetA O n) • y d := fun d _ => by
      rw [← hy']; abel
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_const, smul_add,
      ← Finset.smul_sum, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul,
      ← algebraMap_smul (LetA O n) c, ← algebraMap_smul (LetA O n) c, smul_comm]

theorem basis_of_congr {M : Type} [AddCommGroup M] [Module (LetA O n) M] {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) M) (x y : Fin r → M)
    (h : ∀ j, x j = b j + (letπ : LetA O n) • y j) :
    ∃ b' : Module.Basis (Fin r) (LetA O n) M, ∀ j, b' j = x j := by
  classical
  have hu : IsUnit (b.det x) := by
    rw [Pi.isUnit_iff]
    intro i
    rw [PowerSeries.isUnit_iff_constantCoeff]
    let ψ : LetA O n →+* O := (PowerSeries.constantCoeff (R := O)).comp
      (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)
    have hψ : ψ letπ = 0 := by simp [ψ, letπ]
    change IsUnit (ψ (b.det x))
    rw [Module.Basis.det_apply, RingHom.map_det]
    have : ψ.mapMatrix (b.toMatrix x) = 1 := by
      ext j k
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, h, map_add,
        map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, map_add, map_mul, hψ,
        zero_mul, add_zero, b.repr_self, Finsupp.single_apply, Matrix.one_apply]
      by_cases hjk : j = k
      · simp [hjk]
      · simp [hjk, Ne.symm hjk]
    rw [this, Matrix.det_one]
    exact isUnit_one
  obtain ⟨h1, h2⟩ := (b.is_basis_iff_det).mpr hu
  exact ⟨Module.Basis.mk h1 h2.ge, fun j => Module.Basis.mk_apply _ _ _⟩

theorem div_param [IsDomain O] {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O} (hs : 0 < s')
    (h9 : wachRingRelations W e s' π' E) (a c : LetA O n) (ha : InAΔ W a) (hac : a = letπ * c) :
    ∃ a', InAΔ W a' ∧ a = π' * a' := by
  obtain ⟨hπ, hser, ⟨w, hw⟩, -⟩ := h9
  obtain ⟨f, hf, -⟩ := hser a ha
  have h0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := fun i => by
    rw [hw]
    simp [letπ, hs.ne']
  have hsub : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (h0 i)
  have hne : ∀ i, π' i ≠ 0 := fun i => by
    rw [hw]
    refine mul_ne_zero ?_ (pow_ne_zero _ PowerSeries.X_ne_zero)
    exact (Pi.isUnit_iff.mp w.isUnit i).ne_zero
  have hdiv : ∀ i, ∃ g, a i = π' i * g := fun i => by
    have e1 : f i = PowerSeries.X * (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) +
        PowerSeries.C (PowerSeries.constantCoeff (f i)) := PowerSeries.eq_X_mul_shift_add_const _
    have e2 : a i = π' i * PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i))
        + PowerSeries.C (PowerSeries.constantCoeff (f i)) := by
      rw [hf i]
      conv_lhs => rw [e1]
      rw [← PowerSeries.coe_substAlgHom (hsub i), map_add, map_mul, PowerSeries.substAlgHom_X]
      congr 1
      exact (PowerSeries.substAlgHom (hsub i)).commutes _
    have e3 : PowerSeries.constantCoeff (a i) = 0 := by
      rw [hac]
      simp [letπ]
    have e4 : PowerSeries.constantCoeff (f i) = 0 := by
      rw [e2] at e3
      simpa [h0 i] using e3
    exact ⟨_, by rw [e2, e4, map_zero, add_zero]⟩
  choose g hg using hdiv
  have hag : a = π' * g := funext hg
  refine ⟨g, fun δ hδ => ?_, hag⟩
  have h1 := ha δ hδ
  rw [hag, map_mul, hπ δ hδ] at h1
  funext i
  exact mul_left_cancel₀ (hne i) (congrFun h1 i)

theorem invariant_basis_of_basis [IsDomain O] (hc : IsUnit ((W.DelF.card : ℕ) : O)) {r : ℕ}
    (b₀ : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O} (hs : 0 < s')
    (h9 : wachRingRelations W e s' π' E) : wachModuleOverLetters W T π' := by
  choose x y hx hxy using fun j => exists_avg W T hc (b₀ j)
  obtain ⟨b, hb⟩ := basis_of_congr b₀ x y hxy
  have hbΔ : ∀ j, (b j : W.DD T) ∈ W.NΔ T := fun j => hb j ▸ hx j
  have huniq : ∀ a a' : Fin r → LetA O n,
      ∑ j, a j • (b j : W.DD T) = ∑ j, a' j • (b j : W.DD T) → a = a' := by
    intro a a' h
    apply b.equivFun.symm.injective
    apply Subtype.ext
    simpa [Module.Basis.equivFun_symm_apply] using h
  have hex : ∀ z ∈ W.N T, ∃ a : Fin r → LetA O n, z = ∑ j, a j • (b j : W.DD T) := by
    intro z hz
    refine ⟨b.repr ⟨z, hz⟩, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  have hact : ∀ (a : Fin r → LetA O n) δ, δ ∈ W.DelF →
      W.γD T δ (∑ j, a j • (b j : W.DD T)) = ∑ j, W.γA δ (a j) • (b j : W.DD T) := by
    intro a δ hδ
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [γD_smulA, (hbΔ j).2 δ hδ]
  have hinv : ∀ z ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, InAΔ W (a j)) ∧
      z = ∑ j, a j • (b j : W.DD T) := by
    intro z hz
    obtain ⟨a, ha⟩ := hex z hz.1
    refine ⟨a, fun j δ hδ => ?_, ha⟩
    have h1 := hz.2 δ hδ
    rw [ha, hact a δ hδ] at h1
    exact congrFun (huniq _ _ h1) j
  refine ⟨⟨r, fun j => b j, hbΔ, fun z hz => ?_, hinv⟩, fun z hz => ?_⟩
  · obtain ⟨a, ha⟩ := hex z hz
    exact ⟨a, ha, fun a' ha' => huniq _ _ (ha'.symm.trans ha)⟩
  · have hmem : W.γ T z - z ∈ W.NΔ T := by
      refine (W.NΔ T).sub_mem ⟨W.N_Γ T _ z hz.1, fun δ hδ => ?_⟩ hz
      change W.γD T δ (W.γD T W.gam z) = W.γD T W.gam z
      rw [← W.γD_mul, mul_comm, W.γD_mul, hz.2 δ hδ]
    obtain ⟨a, ha, ha'⟩ := hinv _ hmem
    obtain ⟨u, hu, hu'⟩ := W.N_π T W.gam z hz.1
    obtain ⟨c, hc'⟩ := hex u hu
    have hac : a = fun j => letπ * c j := by
      apply huniq
      rw [← ha']
      change W.γD T W.gam z - z = _
      rw [hu', hc', Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    choose a' h1 h2 using fun j => div_param W hs h9 (a j) (c j) (ha j) (congrFun hac j)
    refine ⟨∑ j, a' j • (b j : W.DD T),
      ⟨Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (b j).2, fun δ hδ => ?_⟩, ?_⟩
    · rw [hact a' δ hδ]
      exact Finset.sum_congr rfl fun j _ => by rw [h1 j δ hδ]
    · rw [ha', Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [h2 j, smul_smul]

theorem not_dvd_card (l : ℕ) [Fact l.Prime] (h : ∀ g : W.Gam, g ^ l = 1 → g = 1) :
    ¬ l ∣ W.DelF.card := by
  classical
  intro hd
  have hcard : Nat.card (CommGroup.torsion W.Gam) = W.DelF.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => (mem_DelF_iff W g).symm)
  haveI : Finite (CommGroup.torsion W.Gam) :=
    Finite.of_equiv _ (Equiv.subtypeEquivRight fun g => (mem_DelF_iff W g) :
      {g // g ∈ W.DelF} ≃ CommGroup.torsion W.Gam)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := CommGroup.torsion W.Gam) l (hcard ▸ hd)
  have h1 : g = 1 := Subtype.ext (h g (by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this))
  rw [h1, orderOf_one] at hg
  exact (Fact.out : l.Prime).one_lt.ne hg

end Generic

theorem padic_root_one {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (x : ℤ_[l]) (hx : x ^ l = 1) : x = 1 := by
  by_contra hne
  have hp : l.Prime := Fact.out
  have h1 : PadicInt.toZMod (x - 1) = 0 := by
    have := congrArg (PadicInt.toZMod (p := l)) hx
    rw [map_pow, ZMod.pow_card] at this
    rw [map_sub, this, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton] at h1
  obtain ⟨b, hb⟩ := h1
  have hx' : x = 1 + l * b := by rw [← hb]; ring
  have h2 := odd_sq_dvd_geom_sum₂_sub (1 : ℤ_[l]) b (hp.odd_of_ne_two hl)
  have h3 : ∑ i ∈ Finset.range l, x ^ i = 0 := by
    have := geom_sum_mul x l
    rw [hx, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  simp only [one_pow, mul_one, ← hx', h3, zero_sub, dvd_neg] at h2
  obtain ⟨c, hc⟩ := h2
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h4 : (l : ℤ_[l]) * c = 1 := mul_left_cancel₀ hl0 (by linear_combination -hc)
  exact PadicInt.prime_p.not_isUnit (IsUnit.of_mul_eq_one _ h4)

set_option maxHeartbeats 1000000 in

theorem invariant_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let _E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.s = 1 → l ≠ 2 → ∀ (e s' : ℕ) (π' : AA K LL) (E' : Let K → Polynomial ↥(OL LL)), 0 < s' → wachRingRelations W e s' π' E' → wachModuleOverLetters W T π' := by
  intro D HW F l _ K s LL h W _E T hT _ hl e s' π' E' hs h9
  obtain ⟨b₀⟩ := N_basis D HW F l K s LL h T hT
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  have hnd : ¬ l ∣ W.DelF.card := by
    refine not_dvd_card W l fun g hg => W.χΓ_inj ?_
    have h1 : (χ g : ℤ_[l]) = 1 := padic_root_one hl _ (by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hg, map_one, Units.val_one])
    apply Units.ext
    rw [map_one, Units.val_one, ← hχ g, h1, map_one]
  have hu : IsUnit ((W.DelF.card : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnd
  have hc : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    simpa using hu.map (algebraMap ℤ_[l] ↥(OL LL))
  exact invariant_basis_of_basis W T hc b₀ hs h9

end GlobalTheory.NL.InvBasis
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_deltaInvariant_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.s = 1 → l ≠ 2 → ∀ (e s' : ℕ) (π' : AA K LL) (E' : Let K → Polynomial ↥(OL LL)), 0 < s' → wachRingRelations W e s' π' E' → wachModuleOverLetters W T π' := by
  atlas_forward_decl GlobalTheory.NL.InvBasis.invariant_basis
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem GlobalTheory.NL.p9_statement : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), P9 D HW F := by
  intro D HW F l _ K s LL h T hT hs hl
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hp] at hl ⊢
  obtain ⟨hc, ⟨π', E', hr⟩, h1⟩ := GlobalTheory.DelParam.torsion_parameters D HW l K s LL h hs hl
  have md := GlobalTheory.T.wachLattice_deltaInvariant_basis D HW F l K s LL h T hT hs hl
  have hpos : 0 < ((HW l).W K s LL h).DelF.card :=
    Finset.card_pos.2 ⟨1, (((HW l).W K s LL h).DelF_def 1).2 ⟨1, one_pos, one_pow _⟩⟩
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt (Fact.out : l.Prime).one_lt
  refine ⟨hc, ⟨π', E', hr, md _ _ _ _ (hc ▸ hpos) hr⟩, fun he => ⟨h1 he, md _ _ _ _ hl1 (h1 he)⟩⟩
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_descent_to_tame_subextension : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), P9 D HW F := by
  atlas_forward_decl GlobalTheory.NL.p9_statement
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_of_cmpOf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), p5eL D.loc D.locA HW F := by
  first | exact @GlobalTheory.NL.SandJumps.main | exact GlobalTheory.NL.SandJumps.main | (intros; apply GlobalTheory.NL.SandJumps.main <;> assumption)
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL

theorem wach_used_clauses (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : DeltaInvariantNormBound D HW F Cm := by
  unfold DeltaInvariantNormBound
  refine ⟨GlobalTheory.NL.LetterFree.letters_free D HW F, GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm,
    GlobalTheory.NL.CmpCris.wachLattice_comparison_dcris D HW F Cm, GlobalTheory.T.wach_lattice_expansion_at_low_level_points D HW F Cm, GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm,
    GlobalTheory.T.wachModule_saturated_exactness_crystalline D HW F Cm, GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F, GlobalTheory.T.p8_of_cmpOf D HW F Cm, GlobalTheory.T.wachModule_descent_to_tame_subextension D HW F,
    GlobalTheory.T.wachModule_uniqueness_characterisation D HW F, GlobalTheory.T.gammaSemisimpleQuotientD_statement D HW F Cm, GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F,
    GlobalTheory.NL.FiniteRestrictionH1f.mem_H1f_iff_res_mem D HW F, GlobalTheory.T.wachIntegralComplex_cocycle_class_finite D HW F, GlobalTheory.T.defect_torsion_second_cohomology_kernel D HW F Cm,
    GlobalTheory.T.cokernel_crystalline_surjection_killed_by_X_pow D HW F Cm, ?_⟩
  unfold ConclusionE
  exact ⟨GlobalTheory.NL.NygaardExtension.main D HW F, GlobalTheory.T.local_comparison_of_cmpOf D HW F Cm⟩

end GlobalTheory.NL
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_laterClauses_hold : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantNormBound D HW F Cm := by
  atlas_forward_decl GlobalTheory.NL.wach_used_clauses
end
