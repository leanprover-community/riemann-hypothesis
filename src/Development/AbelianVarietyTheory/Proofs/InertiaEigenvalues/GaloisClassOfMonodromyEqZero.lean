import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryMemCocyclesOddPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeEquivPeriodRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialCocycleMemLPowLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClassStatement
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyMemRangeOfInvariantVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulPhiMemMM
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToBcrisPhi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitToBFrobEis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisSubValueMemFilZeroOfMonodromyZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMuSemidirectCyclicCoverOfMemGKinfCoeffs

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrisFixedLattice

theorem coordLeft_lTensor {R : Type} [CommRing R] {V M N : Type}
    [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι R V) (f : M →ₗ[R] N) (x : V ⊗[R] M) (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor V x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem coordRight_map {R : Type} [CommRing R] {M P N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    {κ : Type} [DecidableEq κ] (b : Module.Basis κ R N) (f : M →ₗ[R] P) (x : M ⊗[R] N) (j : κ) :
    equivFinsuppOfBasisRight b (TensorProduct.map f LinearMap.id x) j = f (equivFinsuppOfBasisRight b x j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable {l : ℕ} [Fact l.Prime]

theorem padicInt_ringHom_ext_pt {R : Type} [CommRing R] [IsHausdorff (Ideal.span {(l : R)}) R]
    (f g : ℤ_[l] →+* R) (a : ℤ_[l]) : f a = g a := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(l : R)}) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)
  have e : a = (a.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c := by rw [← hc]; ring
  refine ⟨f c - g c, ?_⟩
  have hf := congrArg f e
  have hg := congrArg g e
  rw [map_add, map_mul, map_pow, map_natCast, map_natCast] at hf hg
  rw [hf, hg]
  ring

theorem zA_eq_algebraMap_pt (a : ℤ_[l]) : Per.zA l a = algebraMap ℤ_[l] (Ainf l) a :=
  padicInt_ringHom_ext_pt (R := WittVector l (Per.Fl l)) (Per.zA l) _ a

theorem iota_algebraMap_pt (C : GlobalTheory.MemLoc.Core l) (a : ℤ_[l]) :
    C.ι (algebraMap ℤ_[l] (Per.Bcris l) a) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (Per.zA l a)) := by
  rw [zA_eq_algebraMap_pt]
  exact GlobalTheory.MemLoc.ULaws.iota_aB C _

def filZero (C : GlobalTheory.MemLoc.Core l) : Submodule ℤ_[l] (Per.Bcris l) where
  carrier := {b | C.ι b ∈ Per.FilD l 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem ha hb
  smul_mem' := by
    intro a b hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_def, map_mul]
    have e : C.ι (algebraMap ℤ_[l] (Per.Bcris l) a) =
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (Per.zA l a)) := iota_algebraMap_pt C a
    rw [e, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hb

theorem qB_padicInt (C : GlobalTheory.MemLoc.Core l) (a : ℤ_[l]) :
    C.qB (a : ℚ_[l]) = algebraMap ℤ_[l] (Per.Bcris l) a := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [iota_algebraMap_pt, ← C.o_sec.z]
  exact C.ι_u _

theorem exists_padicInt_of_norm_le (q : ℚ_[l]) (N : ℕ) (h : ‖q‖ ≤ (l : ℝ) ^ N) :
    ‖(l : ℚ_[l]) ^ N * q‖ ≤ 1 := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
  rw [inv_mul_le_iff₀ (pow_pos hl N), mul_one]
  exact h

end GlobalTheory.CrisFixedLattice

namespace GlobalTheory.CrisFixedLattice

theorem frobOB_eq_lTensor {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (x : OB l O) : frobOB l O x = (frobB l).toLinearMap.lTensor O x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_pow_smul_eq_one_tmul : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (z : TW (OB l O) T), TWmap (frobOB l O) T z = z → z ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • z = (1 : OB l O) ⊗ₜ[O] x := by
  intro hF l _ O K _ _ _ _ _ _ _ G _ _ T C z hφ hz
  classical
  rcases subsingleton_or_nontrivial O with hO | hO
  · haveI := Module.subsingleton O (TW (OB l O) T)
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI : Module.Free O ↥T.L.T := T.L.free
  let bO := Module.Free.chooseBasis ℤ_[l] O
  let bM := Module.Free.chooseBasis O ↥T.L.T
  let eR := TensorProduct.equivFinsuppOfBasisRight (M := OB l O) bM
  let eL := TensorProduct.equivFinsuppOfBasisLeft (N := Per.Bcris l) bO
  let c := fun j i => eL (eR z j) i

  have hcφ : ∀ j i, Per.φB l (c j i) = c j i := by
    intro j i
    have h1 : eR (TWmap (frobOB l O) T z) j = frobOB l O (eR z j) :=
      coordRight_map bM (frobOB l O).toLinearMap z j
    rw [hφ, frobOB_eq_lTensor] at h1
    have h2 : c j i = eL ((frobB l).toLinearMap.lTensor O (eR z j)) i := congrArg (fun w => eL w i) h1
    rw [coordLeft_lTensor] at h2
    exact h2.symm

  let F0 := filZero C
  let RQ : Submodule ℤ_[l] (OB l O) := LinearMap.range (F0.subtype.lTensor O)
  have hsmul : ∀ (o : O) (w : OB l O), w ∈ RQ → o • w ∈ RQ := by
    rintro o _ ⟨y, rfl⟩
    refine ⟨(LinearMap.mulLeft ℤ_[l] o).rTensor _ y, ?_⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a f => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have key : ∀ w, w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∀ j, eR w j ∈ RQ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w' hw' =>
      obtain ⟨β, x, hβ, rfl⟩ := hw'
      intro j
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      refine hsmul _ _ ⟨(1 : O) ⊗ₜ[ℤ_[l]] (⟨β, hβ⟩ : F0), ?_⟩
      simp
    | zero => intro j; simp
    | add x y _ _ hx hy => intro j; rw [map_add, Finsupp.add_apply]; exact add_mem (hx j) (hy j)
    | smul o x _ hx => intro j; rw [map_smul, Finsupp.smul_apply]; exact hsmul o _ (hx j)
  have hzR : ∀ j, eR z j ∈ RQ := key z hz
  have hcF : ∀ j i, C.ι (c j i) ∈ Per.FilD l 0 := by
    intro j i
    obtain ⟨y, hy⟩ := hzR j
    have h := coordLeft_lTensor bO F0.subtype y i
    simp only [c]
    rw [← hy, h]
    exact (equivFinsuppOfBasisLeft bO y i).2

  have hq : ∀ j i, ∃ q : ℚ_[l], C.qB q = c j i := fun j i => (hF l C).2.2.2.1 _ (hcφ j i) (hcF j i)
  choose q hqc using hq

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ j, ∑ i, ‖q j i‖) hl1
  have hb : ∀ j i, ‖(l : ℚ_[l]) ^ N * q j i‖ ≤ 1 := fun j i => by
    refine exists_padicInt_of_norm_le _ N (le_trans ?_ hN.le)
    refine le_trans ?_ (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg (q j i))
      (Finset.mem_univ j))
    exact Finset.single_le_sum (fun i _ => norm_nonneg (q j i)) (Finset.mem_univ i)
  let a : _ → _ → ℤ_[l] := fun j i => ⟨(l : ℚ_[l]) ^ N * q j i, hb j i⟩
  have ha : ∀ j i, ((l ^ N : ℕ) : Per.Bcris l) * c j i = algebraMap ℤ_[l] (Per.Bcris l) (a j i) := by
    intro j i
    rw [← qB_padicInt, ← hqc]
    show _ = C.qB ((l : ℚ_[l]) ^ N * q j i)
    rw [map_mul, map_pow, map_natCast, Nat.cast_pow]
  let y : _ → O := fun j => bO.equivFun.symm (a j)
  refine ⟨N, bM.equivFun.symm y, ?_⟩
  apply eR.injective
  ext j : 1
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  apply eL.injective
  ext i : 1
  have e1 : bM.repr (bM.equivFun.symm y) j = y j := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [e1, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, Finsupp.smul_apply, map_nsmul, Finsupp.smul_apply,
    nsmul_eq_mul, ha, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  have e2 : bO.repr (y j) i = a j i := by
    simp only [y]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [e2, Algebra.smul_def, mul_one]

end GlobalTheory.CrisFixedLattice
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_smul_eq_tmul_of_frobenius_fixed_fil_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (z : TW (OB l O) T), TWmap (frobOB l O) T z = z → z ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • z = (1 : OB l O) ⊗ₜ[O] x := by
  atlas_forward_decl GlobalTheory.CrisFixedLattice.exists_pow_smul_eq_one_tmul
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CoeffComplete

open Filter Topology

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem norm_natCast_prime_eq : ‖(l : K)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] K) l, norm_algebraMap']
  exact Padic.norm_p

theorem natCast_smul_pow_eq (k : ℕ) (z : O) : ((l : ℤ_[l]) ^ k) • z = (l : O) ^ k * z := by
  rw [Algebra.smul_def, map_pow, map_natCast]

theorem norm_intCoord_le_one {ι : Type} [Fintype ι] (v : ι → ℤ_[l]) : ‖v‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => PadicInt.norm_le_one _

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ_[l] O)

theorem coord_small_of_small (y : O) (k : ℕ) (h : ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ k) :
    ‖b.equivFun y‖ ≤ ‖(l : ℤ_[l])‖ ^ k := by
  have hl : (l : K) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_natCast_prime_eq (l := l)]
    exact inv_ne_zero (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hw : ‖algebraMap O K y / (l : K) ^ k‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ h (by positivity)
  obtain ⟨z, hz⟩ := (IsUnitBall.mem_range_iff (O := O) _).2 hw
  have hy : y = (l : O) ^ k * z := by
    apply IsUnitBall.inj (K := K)
    rw [map_mul, hz, map_pow, map_natCast, mul_div_cancel₀ _ (pow_ne_zero _ hl)]
  rw [hy, ← natCast_smul_pow_eq, map_smul]
  calc ‖((l : ℤ_[l]) ^ k) • b.equivFun z‖ ≤ ‖(l : ℤ_[l]) ^ k‖ * ‖b.equivFun z‖ := norm_smul_le _ _
    _ ≤ ‖(l : ℤ_[l]) ^ k‖ * 1 := by gcongr; exact norm_intCoord_le_one _
    _ = ‖(l : ℤ_[l])‖ ^ k := by rw [mul_one, norm_pow]

theorem small_of_coord_small (y : O) (k : ℕ) (h : ‖b.equivFun y‖ ≤ ‖(l : ℤ_[l])‖ ^ k) :
    ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ k := by
  have hd : ∀ i, ((l : ℤ_[l]) ^ k) ∣ b.equivFun y i := by
    intro i
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    have := (pi_norm_le_iff_of_nonneg (by positivity)).1 h i
    rw [PadicInt.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg] at this
    exact this
  choose e he using hd
  have hy : y = (l : O) ^ k * b.equivFun.symm e := by
    rw [← natCast_smul_pow_eq, ← map_smul, ← b.equivFun.symm_apply_apply y]
    congr 1
    funext i
    simp [he i]
  rw [hy, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (norm_algebraMap_le _)

theorem completeSpace_of_finite_unitBall : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K], CompleteSpace K := by
  intro l _ O K _ _ _ _ _ _ _ _ _
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hϖ0 : 0 < ‖(l : K)‖ := by rw [norm_natCast_prime_eq (l := l)]; positivity
  have hϖ1 : ‖(l : K)‖ < 1 := by
    rw [norm_natCast_prime_eq (l := l)]; exact inv_lt_one_of_one_lt₀ hl1
  have hπ0 : 0 < ‖(l : ℤ_[l])‖ := by rw [PadicInt.norm_p]; positivity
  have hπ1 : ‖(l : ℤ_[l])‖ < 1 := by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ hl1
  refine Metric.complete_of_convergent_controlled_sequences (fun N => ‖(l : K)‖ ^ N)
    (fun n => pow_pos hϖ0 n) ?_
  intro u hu
  have h0 : ∀ n, ‖u n - u 0‖ ≤ 1 := fun n => by
    have := hu 0 n 0 (Nat.zero_le _) le_rfl
    rw [dist_eq_norm, pow_zero] at this
    exact this.le
  choose y hy using fun n => (IsUnitBall.mem_range_iff (O := O) _).2 (h0 n)
  have hc : CauchySeq (fun n => b.equivFun (y n)) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => ‖(l : ℤ_[l])‖ ^ N) (fun n m N hn hm => ?_) ?_
    · rw [dist_eq_norm, ← map_sub]
      apply coord_small_of_small (K := K) b
      rw [map_sub, hy, hy, show u n - u 0 - (u m - u 0) = u n - u m by abel]
      have := hu N n m hn hm
      rw [dist_eq_norm] at this
      exact this.le
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one hπ0.le hπ1
  obtain ⟨γ, hγ⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨u 0 + algebraMap O K (b.equivFun.symm γ), ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hϖ1
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hγ _ (pow_pos hπ0 k)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have e : u n - (u 0 + algebraMap O K (b.equivFun.symm γ)) =
      algebraMap O K (y n - b.equivFun.symm γ) := by
    rw [map_sub, hy]; abel
  rw [e]
  refine lt_of_le_of_lt (small_of_coord_small b _ k ?_) hk
  rw [map_sub, LinearEquiv.apply_symm_apply]
  have := hN n hn
  rw [dist_eq_norm] at this
  exact this.le

end GlobalTheory.CoeffComplete
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completeSpace_of_finite_padicInt_unitBall : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K], CompleteSpace K := by
  atlas_forward_decl GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall
end

section
section
open PowerSeries GlobalTheory.BK

theorem GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, ∀ σ : Vec K a ι, D.conn σ = D.zeta y → ∃ d : D.D, D.phi σ - σ - D.phi y = D.xi d := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy σ hσ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hyl : y ∈ D.Yl := D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hy⟩
  obtain ⟨⟨s, -, -, hs, d, -, hd⟩, -⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι η H D y hyl
  have h0 : D.conn (σ - s) = 0 := by rw [map_sub, hσ, hs, sub_self]
  set w := D.xiExt.symm (σ - s) with hw
  have hder : derV w = 0 := by
    have h1 : D.conn (D.xiExt w) = 0 := by rw [hw, LinearEquiv.apply_symm_apply]; exact h0
    rw [PhiMod.conn_apply, PhiMod.nabla_xiExt] at h1
    have h2 : D.xiExt (derV w) = 0 :=
      smul_right_injective (Vec K a ι) (X_ne_zero (R := K)) (by simpa only [smul_zero] using h1)
    exact D.xiExt.map_eq_zero_iff.1 h2
  have hwc : w = cst (red w) := by
    ext τ i n
    have h3 := congrArg (coeff n) (congrFun (congrFun hder τ) i)
    rw [derV_apply, coeff_derivative] at h3
    rcases n with _ | n
    · simp [red_apply, red0]
    · have h4 := congrArg (coeff n) (congrFun (congrFun hder τ) i)
      rw [derV_apply, coeff_derivative] at h4
      simp only [Pi.zero_apply, map_zero, mul_eq_zero] at h4
      rw [cst_apply, coeff_C, if_neg (Nat.succ_ne_zero n)]
      rcases h4 with h4 | h4
      · exact h4
      · exact absurd h4 (by exact_mod_cast Nat.succ_ne_zero n)
  have hxi : σ - s = D.xi (red w) := by
    rw [PhiMod.xi_apply, ← hwc, hw, LinearEquiv.apply_symm_apply]
  refine ⟨d + D.phiD (red w) - red w, ?_⟩
  rw [map_sub, map_add, ← PhiMod.phi_xi, ← hxi, ← hd, map_sub]
  abel
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_sub_sub_mem_xi_of_monodromy_eq : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, ∀ σ : Vec K a ι, D.conn σ = D.zeta y → ∃ d : D.D, D.phi σ - σ - D.phi y = D.xi d := by
  atlas_forward_decl GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi
end

section
section
open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.BK

namespace PhiMod

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NeZero a]

theorem exists_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {v : Vec K a ι} (hv : v ∈ P.MMl) :
    ∃ N : ℕ, (l : K) ^ N • v ∈ P.MM := by
  have hc : ∀ p : ZMod a × ι, ∃ n : ℕ,
      (l : K⟦X⟧) ^ n * (P.mxInv p.1 *ᵥ v p.1) p.2 ∈ S O K e := by
    intro p
    obtain ⟨n, hn⟩ := mem_away.1 (mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 hv p.1)) p.2)
    exact ⟨n, by simpa using hn⟩
  choose n hn using hc
  refine ⟨Finset.univ.sup n, mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => ?_)⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, hc, smul_eq_C_mul, map_pow, map_natCast,
    pow_add, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem _ l) c) (hn (τ, i))

theorem mem_MMl_of_lpow_smul_mem_MM (P : PhiMod O K l e a ι) {w : Vec K a ι} (N : ℕ)
    (h : (l : K) ^ N • w ∈ P.MM) : w ∈ P.MMl := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 (mem_vecs.2 fun i => mem_away.2 ⟨N, ?_⟩)
  have h1 := mem_vecs.1 (P.mem_extc_iff.1 (mem_tot.1 h τ)) i
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_C_mul, map_pow, map_natCast] at h1
  simpa using h1

end PhiMod

theorem BKDat.phi_mem_MMl : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ v ∈ D.MMl, D.phi v ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D v hv
  obtain ⟨N, hN⟩ := D.toPhiMod.exists_lpow_smul_mem_MM hv
  have h := PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper _ hN
  rw [map_smul, smul_smul, ← pow_add] at h
  exact D.toPhiMod.mem_MMl_of_lpow_smul_mem_MM _ h

end GlobalTheory.BK
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_mem_invertedLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ v ∈ D.MMl, D.phi v ∈ D.MMl := by
  atlas_forward_decl GlobalTheory.BK.BKDat.phi_mem_MMl
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem phi_mem_MMl_of_mem_Y : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.phi y ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy
  have hl : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero (algebraMap ℚ_[l] K)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
  have hE : E K l e ^ η • y ∈ D.M := hy.1
  have h0 : (l : K) ^ η • D.phi y ∈ D.MM := D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hE)
  have h1 : (l : K) ^ η • D.phi y ∈ D.MMl := D.ext_mono (le_away _ _) h0
  have hc : (C ((l : K)⁻¹ ^ η) : K⟦X⟧) ∈ invL l (S O K e) := by
    refine ⟨η, ?_⟩
    have : ((l : S O K e) : K⟦X⟧) ^ η * C ((l : K)⁻¹ ^ η) = 1 := by
      rw [show ((l : S O K e) : K⟦X⟧) = C (l : K) by simp, ← map_pow, ← map_mul, ← mul_pow,
        mul_inv_cancel₀ hl, one_pow, map_one]
    rw [this]; exact one_mem _
  have h2 := D.MMl.smul_mem ⟨_, hc⟩ h1
  convert h2 using 1
  rw [Subalgebra.smul_def]
  funext τ i
  simp only [Pi.smul_apply, smul_eq_mul, Subtype.coe_mk]
  rw [PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, ← mul_pow, inv_mul_cancel₀ hl, one_pow,
    map_one, one_mul]

end GlobalTheory.BK
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_mem_invertedPrime_lattice_of_mem_eisensteinInvariants : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.phi y ∈ D.MMl := by
  atlas_forward_decl GlobalTheory.BK.phi_mem_MMl_of_mem_Y
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.PhiVal

theorem isCrisVal_phi : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (hφ : D.phi y ∈ D.MMl), IsCrisVal t ϖ D.toPhiMod jB (phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩)) (jB (toBcris t ϖ D.toPhiMod ⟨D.phi y, hφ⟩)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T jB y hY hy hφ
  have hEM : ∀ τ i, E K l e ^ η * y τ i ∈ A O K := fun τ i => mem_tot.1 ((Descent.mem_invOf _).1 hY).1 τ i
  let g : ι → ZMod a → A O K := fun i τ => ⟨E K l e ^ η * y τ i, hEM τ i⟩
  let m : OA l O := frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ η
  refine ⟨m, fun i => frobOA l O (ϖ.iTot t K (g i)), ?_, ?_, ?_⟩
  · rw [map_pow]
    exact (FrobEis.isUnit_toB_frob_eis l a e O ϖ).pow η
  · let EW : ZMod a → invE l e (A O K) := fun _ => ⟨(EIn l e (A O K) : K⟦X⟧), le_away _ _ (EIn l e (A O K)).2⟩
    have h2 : ϖ.iW t K EW = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) :=
      (ϖ.iW_of_mem t K (fun _ => EIn l e (A O K))).trans (congrArg _ (ϖ.iTot_E t K))
    have hA : ∀ i, inclO l O m * frobOW l O (toW t ϖ D.toPhiMod ⟨y, hy⟩ i) =
        inclO l O (frobOA l O (ϖ.iTot t K (g i))) := by
      intro i
      have h1 : ϖ.iW t K (fun τ => ⟨(g i τ : K⟦X⟧), le_away _ _ (g i τ).2⟩) =
          ϖ.iW t K EW ^ η * ϖ.iW t K (fun τ => ⟨y τ i, mem_tot.1 hy τ i⟩) := by
        rw [← map_pow, ← map_mul]
        congr 1
      rw [← frobOW_inclO, ← ϖ.iW_of_mem t K, h1, map_mul, h2, toW_apply, map_pow (inclO l O), map_pow (frobOW l O),
        frobOW_inclO]
    rw [phiW_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, hA i]
  · rw [← LinearEquiv.map_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, toBcris_apply]
    let liftA : (ZMod a → A O K) → ZMod a → invL l (S O K e) :=
      fun F τ => ⟨F τ, le_away _ _ (A_le_S l e (F τ).2)⟩
    have key : liftA (frobAc l fun _ => EIn l e (A O K)) ^ η * coordL D.toPhiMod (invL l (S O K e)) ⟨D.phi y, hφ⟩ i =
        liftA (frobAc l (g i)) := by
      funext τ
      apply Subtype.ext
      have h1 : (coordL D.toPhiMod (invL l (S O K e)) ⟨D.phi y, hφ⟩ i τ : K⟦X⟧) = frob K l (y (τ - 1) i) := by
        change (D.mxInv τ *ᵥ D.phi y τ) i = _
        rw [PhiMod.phi_apply, Matrix.mulVec_mulVec, PhiMod.mxInv_mul_mx, Matrix.one_mulVec, frobV_apply]
      simp only [liftA, Pi.mul_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, h1, coe_frobAc,
        frobTot_apply, g, map_mul, map_pow]
      rfl
    have h3 := congrArg (ϖ.iB t K) key
    simp only [map_mul, map_pow, liftA, FrobCoord.iB_of_A, ϖ.iTot_frob t K, ϖ.iTot_E t K] at h3
    rw [← h3, map_pow]

end GlobalTheory.BKGal.PhiVal
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorBcris_value_frobenius_of_inverse_eisenstein_twist : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (hφ : D.phi y ∈ D.MMl), IsCrisVal t ϖ D.toPhiMod jB (phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩)) (jB (toBcris t ϖ D.toPhiMod ⟨D.phi y, hφ⟩)) := by
  atlas_forward_decl GlobalTheory.BKGal.PhiVal.isCrisVal_phi
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.PhiFix

theorem frob_actB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (x : TW (OB l O) T) :
    TWmap (frobOB l O) T (actB (sQ l) T g x) = actB (sQ l) T g (TWmap (frobOB l O) T x) := by
  have hB : ∀ r : OB l O, frobOB l O (galOB O (sQ l g) r) = galOB O (sQ l g) (frobOB l O r) := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul o β =>
      simp only [frobOB, galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact congrArg (fun y : Per.Bcris l => o ⊗ₜ[ℤ_[l]] y) ((GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.1 _ β)
    | add r s hr hs => rw [map_add (galOB O (sQ l g)), map_add (frobOB l O), map_add (frobOB l O), map_add (galOB O (sQ l g)), hr, hs]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [actB, TWmap, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, hB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem frob_fixed_coboundary : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → TWmap (frobOB l O) T (actB (sQ l) T g b - b) = actB (sQ l) T g b - b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY b hb g hg
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hb₀, rfl⟩ := hb
  haveI : CompleteSpace K := GlobalTheory.T.completeSpace_of_finite_padicInt_unitBall l O K
  obtain ⟨d, hd⟩ := GlobalTheory.T.phi_sub_sub_mem_xi_of_monodromy_eq O K l e a ι η H D y hyY σ.1 hconn
  obtain ⟨-, hall⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I
  obtain ⟨hφ, huniq, hfrobv, -, -⟩ := hall R.jB R.cmp
  have hσφ : D.phi σ.1 ∈ D.MMl := GlobalTheory.T.phi_mem_invertedLattice O K l e a ι η H D σ.1 σ.2
  have hyφ : D.phi y ∈ D.MMl := GlobalTheory.T.phi_mem_invertedPrime_lattice_of_mem_eisensteinInvariants O K l e a ι η H D y hyY

  have hv1 := IsCrisVal.sub t ϖ (hfrobv _ _ hb₀) hb₀
  have hv2 := GlobalTheory.T.tensorBcris_value_frobenius_of_inverse_eisenstein_twist l a e O K t ϖ ι η H D T R.jB y hyY hy hyφ
  have hw : phiW t ϖ D.toPhiMod (phiW t ϖ D.toPhiMod m₀) - phiW t ϖ D.toPhiMod m₀ =
      phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩) := by rw [← hm₀, map_sub]
  rw [hw] at hv1
  have hb0 := huniq _ _ _ hv1 hv2
  have hs := hφ σ ⟨D.phi σ.1, hσφ⟩ rfl
  have hmem : D.xi d ∈ D.MMl := by
    rw [← hd]; exact sub_mem (sub_mem hσφ σ.2) hyφ
  have hkey : TWmap (frobOB l O) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) -
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) = R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi d, hmem⟩) := by
    have he : (⟨D.xi d, hmem⟩ : D.MMl) = ⟨D.phi σ.1, hσφ⟩ - σ - ⟨D.phi y, hyφ⟩ := Subtype.ext (by
      simp only [Submodule.coe_sub]; exact hd.symm)
    rw [he, map_sub, map_sub, map_sub, map_sub, map_sub, ← hs, ← hb0]
    abel
  have hfix := R.horiz g hg d hmem
  rw [← hkey, map_sub] at hfix
  rw [map_sub, frob_actB]
  exact sub_eq_sub_iff_sub_eq_sub.1 hfix

end GlobalTheory.BKGal.PhiFix
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisCoboundary_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → TWmap (frobOB l O) T (actB (sQ l) T g b - b) = actB (sQ l) T g b - b := by
  atlas_forward_decl GlobalTheory.BKGal.PhiFix.frob_fixed_coboundary
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_mem_filtration_zero_tame : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → ∃ b₁, IsCrisVal t ϖ D.toPhiMod R.jB m₀ b₁ ∧ ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b₁ - b₁ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.value_mem_filtration_zero | exact GlobalTheory.BKGal.value_mem_filtration_zero | (intros; apply GlobalTheory.BKGal.value_mem_filtration_zero <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.gb_sub_b_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b - b ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hMon b hb g hg
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  refine ⟨C, ?_⟩
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, rfl⟩ := hb
  obtain ⟨b₁, hb₁, hF⟩ := GlobalTheory.T.value_mem_filtration_zero_tame l a e O K t ϖ hl2 ι η H D T R y hyY hy m₀ h1
  have hv : IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) (b₀ - b₁) := by
    rw [← h1]; exact GlobalTheory.BKGal.IsCrisVal.sub t ϖ h4 hb₁
  have h5 := GlobalTheory.T.galois_sub_value_mem_filZero_of_monodromy_zero l a e O K t ϖ hl2 ι η H D T R y hyY hMon hy σ h2 h3 (b₀ - b₁) hv g hg C
  have h6 := hF g hg C
  have h7 := Submodule.sub_mem _ h5 h6
  convert h7 using 1
  simp only [map_sub]
  abel
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisAction_sub_mem_filtrationZero_of_monodromy : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b - b ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  atlas_forward_decl GlobalTheory.BKGal.gb_sub_b_mem_filZero
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem coboundary_mem_lattice_of_mon_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  intro hF l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hy hMon b hb g hg
  obtain ⟨C, hC⟩ := GlobalTheory.T.galoisAction_sub_mem_filtrationZero_of_monodromy l a e O K t ϖ hl2 ι η H D T R y hy hMon b hb g hg
  exact GlobalTheory.T.exists_prime_pow_smul_eq_tmul_of_frobenius_fixed_fil_zero hF l O K (Gl l) T C _ (GlobalTheory.T.galoisCoboundary_frobenius_fixed l a e O K t ϖ ι η H D T R y hy b hb g hg) hC

end GlobalTheory.BKGal
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_coboundary_mem_lattice_inv_l_of_monodromy_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  atlas_forward_decl GlobalTheory.BKGal.coboundary_mem_lattice_of_mon_eq_zero
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_muSemidirectCyclic_cover_of_mem_GKinf_coeffs : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ k ∈ ϖ.GKinf, ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  first | exact @GlobalTheory.KinfCover.exists_covers_of_mem_GKinf | exact GlobalTheory.KinfCover.exists_covers_of_mem_GKinf | (intros; apply GlobalTheory.KinfCover.exists_covers_of_mem_GKinf <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleKinf

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G] {T : LocLat G ℚ_[l] K O}

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  congr 1
  ext1 i
  simp [map_mul]

theorem isCrisVal_add (P : PhiMod O K l e a ι) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T)
    {w w' : ι → OW l O} {b b' : TW (OB l O) T} (h : IsCrisVal t ϖ P jB w b)
    (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w + w') (b + b') := by
  obtain ⟨m, c, hm, hw, hb⟩ := h
  obtain ⟨m', c', hm', hw', hb'⟩ := h'
  refine ⟨m * m', m' • c + m • c', ?_, ?_, ?_⟩
  · rw [map_mul]; exact hm.mul hm'
  · rw [map_add, inclL_smul, inclL_smul, ← hw, ← hw', smul_smul, smul_smul, smul_add, map_mul,
      mul_comm (inclO l O m) (inclO l O m')]
  · have e1 : (fun i => toB l O ((m' • c + m • c') i)) =
        toB l O m' • (fun i => toB l O (c i)) + toB l O m • (fun i => toB l O (c' i)) := by
      ext1 i
      simp [map_add, map_mul]
    rw [e1, map_add, map_smul, map_smul, ← hb, ← hb', map_mul, smul_add, smul_smul, smul_smul,
      mul_comm (toB l O m') (toB l O m)]

theorem cocycle_mem_lattice_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ ϖ.GKinf → ∃ x : ↥T.L.T, actB (sQ l) T g b - b = (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY b hpot g hg
  obtain ⟨hy, m₀, σ, b₀, hm₀, hσ, -, hval, rfl⟩ := hpot
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_muSemidirectCyclic_cover_of_mem_GKinf_coeffs l a e O K t ϖ (sQ l g) hg

  have hσfix : actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB (toBcris t ϖ D.toPhiMod σ) :=
    GlobalTheory.T.kisinInfGalois_acts_through_descentDatum l a e O K t ϖ ι D.toPhiMod T R.I R.jB D.desc R.cmp R.desc g γ hγ σ σ (hσ γ).symm

  have hyfix : R.I.act (sQ l g) g (toW t ϖ D.toPhiMod ⟨y, hy⟩) = toW t ϖ D.toPhiMod ⟨y, hy⟩ :=
    R.desc g γ hγ ⟨y, hy⟩ ⟨y, hy⟩ (((Descent.mem_invOf _).1 hyY).2 γ).symm

  set w := R.I.act (sQ l g) g m₀ - m₀ with hw
  have hφw : phiW t ϖ D.toPhiMod w = w := by
    have h1 : phiW t ϖ D.toPhiMod w - w =
        R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀ - m₀) - (phiW t ϖ D.toPhiMod m₀ - m₀) := by
      rw [hw, map_sub, map_sub, R.I.act_phiW]; abel
    rw [hm₀, hyfix, sub_self] at h1
    exact sub_eq_zero.1 h1
  obtain ⟨x, hx⟩ : w ∈ LinearMap.range R.I.ofT := by rw [R.I.range_ofT]; exact hφw
  obtain ⟨-, huniq, -, hofT, hgal⟩ :=
    (GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp
  have h2 : IsCrisVal t ϖ D.toPhiMod R.jB (R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀))
      (actB (sQ l) T g b₀) := hgal g (R.stable g) _ _ hval
  have h3 : R.I.act (sQ l g) g (phiW t ϖ D.toPhiMod m₀) = phiW t ϖ D.toPhiMod m₀ + R.I.ofT x := by
    rw [R.I.act_phiW, hx, ← hφw, hw, map_sub]; abel
  rw [h3] at h2
  have h4 := huniq _ _ _ h2 (GlobalTheory.CocycleKinf.isCrisVal_add D.toPhiMod R.jB hval (hofT x))
  refine ⟨-x, ?_⟩
  rw [map_sub, hσfix, h4, tmul_neg]
  abel

end GlobalTheory.CocycleKinf
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_mem_lattice_on_kummerTowerGalois : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ ϖ.GKinf → ∃ x : ↥T.L.T, actB (sQ l) T g b - b = (1 : OB l O) ⊗ₜ[O] x := by
  atlas_forward_decl GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.MonZero

variable {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K]

theorem galOB_mul (g h : GQ l) (r : OB l O) :
    galOB O (g * h) r = galOB O g (galOB O h r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul o w =>
    simp only [galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact congrArg (fun z => o ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 g h w)

theorem actB_mul (T : LocLat (Gl l) ℚ_[l] K O) (g h : Gl l) (x : TW (OB l O) T) :
    actB (sQ l) T (g * h) x = actB (sQ l) T g (actB (sQ l) T h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r t =>
    have ht : T.actT (g * h) t = T.actT g (T.actT h t) :=
      Subtype.ext (show T.ρ (g * h) t = T.ρ g (T.ρ h t) by simp)
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_mul, galOB_mul, ht]

theorem actB_one_tmul (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (t : ↥T.L.T) :
    actB (sQ l) T g ((1 : OB l O) ⊗ₜ[O] t) = (1 : OB l O) ⊗ₜ[O] T.actT g t := by
  simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem smul_cancel (T : LocLat (Gl l) ℚ_[l] K O) (c : ℕ) {u v : TW (OB l O) T}
    (h : ((l : O) ^ c) • u = ((l : O) ^ c) • v) : u = v := by
  have e : ∀ w : TW (OB l O) T, ((l : O) ^ c) • w = ((l : OB l O) ^ c) • w := by
    intro w
    rw [← algebraMap_smul (OB l O) ((l : O) ^ c) w, map_pow, map_natCast]
  rw [e, e] at h
  exact (isUnit_l_OB.pow c).smul_left_cancel.1 h

theorem step_mul {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b) (g h k : Gl l)
    (hg : g = h * k) (hh : sQ l h ∈ GK (ϖ.field a)) (hk : sQ l k ∈ ϖ.GKinf) :
    ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  obtain ⟨xk, hxk⟩ := GlobalTheory.T.cocycle_mem_lattice_on_kummerTowerGalois l a e O K t ϖ ι η H D T R y hy b hb k hk
  obtain ⟨xh, hxh⟩ := GlobalTheory.T.potentialCocycle_mem_lPow_lattice l a e O K t ϖ ι η H D T R hηH hlH y hy c hc b hb h hh
    (GlobalTheory.T.galois_coboundary_mem_lattice_inv_l_of_monodromy_eq_zero hF l a e O K t ϖ hl2 ι η H D T R y hy hM b hb h hh)
  refine ⟨(l : O) ^ c • T.actT h xk + xh, ?_⟩
  have e1 : actB (sQ l) T g b - b = actB (sQ l) T h (actB (sQ l) T k b - b) + (actB (sQ l) T h b - b) := by
    rw [hg, actB_mul, map_sub]; abel
  rw [e1, hxk, actB_one_tmul, smul_add, hxh, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add]

theorem cob_of (T : LocLat (Gl l) ℚ_[l] K O) (b : TW (OB l O) T) (c : ℕ) (X : Gl l → ↥T.L.T)
    (hX : ∀ g, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] X g) :
    IsCobOf (sQ l) T b (fun g => ((l : K) ^ c)⁻¹ • (X g : T.V)) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  intro g n x hx
  apply smul_cancel T c
  rw [smul_comm ((l : O) ^ c) ((l : O) ^ n), hX g, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  rw [← algebraMap_smul K ((l : O) ^ c), ← algebraMap_smul K ((l : O) ^ n), map_pow, map_pow, map_natCast, hx,
    smul_comm ((l : K) ^ n), smul_smul ((l : K) ^ c), mul_inv_cancel₀ hne, one_smul]

theorem exists_cob {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b)
    (hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf) :
    ∃ κ : Gl l → T.V, IsCobOf (sQ l) T b κ ∧ ∀ g, (l : K) ^ c • κ g ∈ T.L.T := by
  have hX : ∀ g : Gl l, ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
    intro g
    obtain ⟨h, k, hg, hh, hk⟩ := hdec g
    exact step_mul t ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb g h k hg hh hk
  choose X hX using hX
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  refine ⟨_, cob_of T b c X hX, fun g => ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  exact (X g).2

end GlobalTheory.BKGal.MonZero

theorem GlobalTheory.BKGal.classOf_of_mon_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  intro hF l _ a e _ _ ϖ LL _ _ ι _ _ η H D T R Pl AI hstd hηH hlH y hy hM c hc
  have hl2 : l ≠ 2 := by omega
  obtain ⟨b, hb⟩ := (GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).1 y hy
  have hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf := by
    intro g
    obtain ⟨h, hh, k, hk, hgk⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).1 (sQ l g)
    let hG : Gl l := ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
    refine ⟨hG, hG⁻¹ * g, (mul_inv_cancel_left hG g).symm, hh, ?_⟩
    have e1 : sQ l (hG⁻¹ * g) = k := by
      rw [map_mul, map_inv, show sQ l g = h * k from hgk]
      show h⁻¹ * (h * k) = k
      group
    rw [e1]; exact hk
  obtain ⟨κ, hcob, hT⟩ := GlobalTheory.BKGal.MonZero.exists_cob (thetaW a LL) ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb hdec
  have hcl : R.ClassOf y κ := ⟨b, hb, hcob⟩
  have hZ1c : κ ∈ continuousCocycles T.ρ := GlobalTheory.T.coboundary_mem_cocycles_odd_prime l hl2 LL T b κ hcob
  obtain ⟨β, -, -, -, hf⟩ := GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing l LL T Pl AI hstd
  have hZ1f : κ ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ := (hf κ hZ1c).2 ⟨b, hcob⟩
  refine ⟨(l : ↥LL.1) ^ c • κ, ?_, (GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).2.2.1 y κ c hcl⟩
  refine ⟨⟨(continuousCocycles T.ρ).smul_mem _ hZ1c, ?_⟩, (finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ).smul_mem _ hZ1f⟩
  intro g _
  exact hT g
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisClass_of_monodromy_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  atlas_forward_decl GlobalTheory.BKGal.classOf_of_mon_eq_zero
end
