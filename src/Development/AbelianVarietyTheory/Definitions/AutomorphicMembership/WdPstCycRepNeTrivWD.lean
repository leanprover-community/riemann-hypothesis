import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKurOfActStFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst.Test

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)

def cycRep (K LL : FinExt l) : Representation ↥LL.1 ↥(GK K) ↥LL.1 where
  toFun g := algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by
    rw [smul_mul_smul_comm, ← map_mul, ← Units.val_mul, ← map_mul]; rfl

theorem cycRep_apply (K LL : FinExt l) (g : ↥(GK K)) (v : ↥LL.1) :
    cycRep P K LL g v = (P.χQ (g : GQ l) : ℚ_[l]) • v := by
  show algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) • v = _
  rw [algebraMap_smul]

theorem stRep_per (K LL : FinExt l) (g : ↥(GK K)) :
    stRep P (cycRep P K LL) g ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] (C (tInv P) : Bst P)) = (1 : ↥LL.1) ⊗ₜ C (tInv P) := by
  rw [stRep_tmul, cycRep_apply, smul_tmul, actSt_C, smul_C, smul_actQ_tInv]

def per (K LL : FinExt l) : ↥(Dpst P (cycRep P K LL)) :=
  ⟨(1 : ↥LL.1) ⊗ₜ C (tInv P), (mem_Dpst P _).mpr ⟨K, fun g _ => stRep_per P K LL g⟩⟩

theorem per_ne_zero (K LL : FinExt l) : per P K LL ≠ 0 := by
  intro h0
  have := nontrivial_B P
  have h1 : ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] (C (tInv P) : Bst P)) = 0 := congrArg Subtype.val h0
  have h2 : Function.Injective (Algebra.TensorProduct.includeRight : Bst P →ₐ[ℚ_[l]] ↥LL.1 ⊗[ℚ_[l]] Bst P) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ_[l] ↥LL.1).injective
  have h3 : (C (tInv P) : Bst P) = 0 := h2 (by rw [map_zero]; exact h1)
  have h4 := tInv_mul P
  rw [C_eq_zero.mp h3, zero_mul] at h4
  exact zero_ne_one h4





variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) (LL : FinExt l)

section Generic

variable {LL} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (x : ↥(Dpst P ρ))


theorem apply_eq_of_nilpotent {W : Type} [AddCommGroup W] [Module ℂ W] (hd : finrank ℂ W = 1) {v : W}
    (hv : v ≠ 0) (u : End ℂ W) (hu : IsNilpotent (u - 1)) : u v = v := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hd ((u - 1) v)
  have hp : ∀ n : ℕ, ((u - 1) ^ n) v = c ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have hc0 : c = 0 := by
    have := hp k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    exact pow_eq_zero_iff'.mp (this.resolve_right hv) |>.1
  rw [hc0, zero_smul, LinearMap.sub_apply, eq_comm, sub_eq_zero] at hc
  exact hc


end Generic



theorem lpDim_wdAt {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) :
    (wdAt P ι Bw h hj r).lpDim = a := by
  by_cases hr : IsPstAt P Bw r
  · obtain ⟨LL', r', -, h2, h3⟩ := wdAt_of_isPstAt ι Bw h hj hr
    rw [h3, lpDim_wdPst ι Bw h hj h2, LetterDim.finrank_wdSpace l P ι _ LL' _ _ h2]
    simp
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, lpDim_trivWD]

omit P ι in

theorem exists_induces (hw : w ∈ placesOver E l) (h : IsPlaceOver A w) :
    ∃ (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), Induces Bw := by
  obtain ⟨j, L0, hj, hL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l E Ω w A hw h
  obtain ⟨Bw, hB, -⟩ := hL L0 le_rfl
  exact ⟨L0, Bw, fun x => by rw [hB]; exact hj x⟩

omit P ι in

example : Nonempty (LocPrime l) := ⟨(GlobalTheory.MemLoc.exists_locPrime_tied l).choose⟩

end GlobalTheory.Pst.Test
