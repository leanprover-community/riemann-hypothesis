import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFDefs
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ZD

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

set_option maxHeartbeats 200000 in
theorem zB_eq (z : ℤ_[l]) : Per.zB l z = algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (Cmp6.OC l)) (z : ℚ_[l]) := by
  show algebraMap (Reformulated.AutPerF.Acris l (Cmp6.OC l)) (Reformulated.AutPerF.Bcris l (Cmp6.OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.Acris l (Cmp6.OC l))
        (Reformulated.AutPerF.Ainf.ofPadicInt l (Cmp6.OC l) z)) = _
  rw [Reformulated.AutPerF.Bcris.algebraMap_padicInt]
  rfl

set_option maxHeartbeats 200000 in
theorem zD_eq (z : ℤ_[l]) : Per.zD l z = algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (Cmp6.OC l)) (z : ℚ_[l]) := by
  rw [← Reformulated.AutPerF.Bcris.toBdR_algebraMap_padic, ← zB_eq]
  show algebraMap (Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) (Reformulated.AutPerF.BdR l (Cmp6.OC l))
      (algebraMap (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) (Reformulated.AutPerF.BdRPlus l (Cmp6.OC l))
        (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.AinfInv l (Cmp6.OC l))
          (Reformulated.AutPerF.Ainf.ofPadicInt l (Cmp6.OC l) z))) =
    Reformulated.AutPerF.Bcris.toBdR l (Cmp6.OC l)
      (algebraMap (Reformulated.AutPerF.Acris l (Cmp6.OC l)) (Reformulated.AutPerF.Bcris l (Cmp6.OC l))
        (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.Acris l (Cmp6.OC l))
          (Reformulated.AutPerF.Ainf.ofPadicInt l (Cmp6.OC l) z)))
  rw [Reformulated.AutPerF.Bcris.toBdR_algebraMap_acris, Reformulated.AutPerF.Acris.toBdRPlus_algebraMap]
  rfl

set_option maxRecDepth 20000 in
theorem integer_to_crystalline_compat : ∀ z : ℤ_[l], equivCrystalline l (Per.zB l z) = Per6.zB l z := by
  intro z
  show Cmp6.cBc l (Per.zB l z) = _
  rw [zB_eq]
  exact (Cmp6.compat_native l).1 z
set_option maxRecDepth 20000 in
theorem integer_to_deRham_compat : ∀ z : ℤ_[l], equivDeRham l (Per.zD l z) = Per6.zD l z := by
  intro z
  show Cmp6.cD l (Per.zD l z) = _
  rw [zD_eq]
  exact (Cmp6.compat_native l).2.1 z
set_option maxRecDepth 20000 in
theorem deRham_plus_algebraMap_compat : ∀ y : Per.BdRp l, equivDeRham l (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per6.BdRp l) (Per6.BdR l) (equivDeRhamPlus l y) := by
  intro y
  exact (Cmp6.compat_native l).2.2.1 y
set_option maxRecDepth 20000 in
theorem theta_deRham_compat : ∀ y : Per.BdRp l, Per6.θD l (equivDeRhamPlus l y) = Per.θD l y := by
  intro y
  exact (Cmp6.compat_native l).2.2.2.1 y
set_option maxRecDepth 20000 in
theorem galois_action_crystalline_compat : ∀ (g : GQ l) (b : Per.Bcris l), equivCrystalline l (Per.σB g b) = Per6.σB g (equivCrystalline l b) := by
  intro g b
  exact (Cmp6.compat_native l).2.2.2.2.1 g b
set_option maxRecDepth 20000 in
theorem galois_action_deRham_compat : ∀ (g : GQ l) (x : Per.BdR l), equivDeRham l (Per.σD g x) = Per6.σD g (equivDeRham l x) := by
  intro g x
  exact (Cmp6.compat_native l).2.2.2.2.2.1 g x
set_option maxRecDepth 20000 in
theorem frobenius_crystalline_compat : ∀ b : Per.Bcris l, equivCrystalline l (Per.φB l b) = Per6.φB l (equivCrystalline l b) := by
  intro b
  exact (Cmp6.compat_native l).2.2.2.2.2.2.1 b
set_option maxRecDepth 20000 in
theorem filtration_deRham_compat : ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ equivDeRham l x ∈ Per6.FilD l a := by
  intro a x
  exact (Cmp6.compat_native l).2.2.2.2.2.2.2.1 a x
set_option maxRecDepth 20000 in
theorem ainf_to_crystalline_compat : ∀ a : Ainf l, equivCrystalline l (Per.aB l a) = Per6.aB l a := by
  intro a
  exact (Cmp6.compat_native l).2.2.2.2.2.2.2.2.2 a

end Formalism.BasicNotions.CmpTie
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie.LogF

open Reformulated.AutPerF

variable (l : ℕ) [Fact l.Prime]

abbrev B : Type := BdRPlus l (Cmp6.OC l)

theorem mem_ker_pow_iff (x : B l) (n : ℕ) :
    x ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) ^ n ↔ BdRPlus.eval l (Cmp6.OC l) n x = 0 := by
  rw [BdRPlus.ker_thetaC, ← RingHom.mem_ker, BdRPlus.ker_eval]
  rfl

theorem truncLog_eq (N : ℕ) (x : AinfInv l (Cmp6.OC l) ⧸ AinfInv.kerTheta l (Cmp6.OC l) ^ N) :
    truncLog N x = ∑ i ∈ Finset.Ico 1 (N + 1), algebraMap ℚ _ ((-1) ^ (i + 1) / i) * x ^ i := by
  unfold truncLog
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  congr 2
  · push_cast
    ring
  · ring

abbrev u (ε : PreTilt ↥(PadicComplexInt l) l) : B l :=
  algebraMap (Ainf l (Cmp6.OC l)) (B l) (WittVector.teichmuller l ε)

abbrev sA (ε : PreTilt ↥(PadicComplexInt l) l) (n : ℕ) : B l :=
  ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ (B l) ((-1) ^ (i + 1) / i) * (u l ε - 1) ^ i

theorem log_sub_mem (ε : PreTilt ↥(PadicComplexInt l) l) (h : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1) (n : ℕ) :
    BdRPlus.log (u l ε) h - sA l ε n ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) ^ n := by
  have hk : u l ε - 1 ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) := by
    rw [BdRPlus.ker_thetaC, RingHom.mem_ker, map_sub, h, map_one, sub_self]
  have hX : BdRPlus.eval l (Cmp6.OC l) n ((u l ε - 1) ^ n) = 0 :=
    (mem_ker_pow_iff l _ n).1 (Ideal.pow_mem_pow hk n)
  rw [mem_ker_pow_iff, map_sub, BdRPlus.eval_log, truncLog_eq, map_sum]
  simp only [map_mul, map_pow, RingHom.map_rat_algebraMap]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.sum_Ico_succ_top hn, add_sub_cancel_left, ← map_pow, hX, mul_zero]

theorem isLog_iff (ε : PreTilt ↥(PadicComplexInt l) l) (y : B l) :
    (∃ h : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1, y = BdRPlus.log (u l ε) h) ↔ Cmp6.IsLogA l ε y := by
  constructor
  · rintro ⟨h, rfl⟩ n
    exact log_sub_mem l ε h n
  · intro hy
    have h1 := hy 1
    have h2 := hy 2
    have hu : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1 := by
      have h3 := sub_mem (by simpa using h1) (Ideal.pow_le_self two_ne_zero h2)
      have h4 : u l ε - 1 ∈ RingHom.ker (BdRPlus.theta l (Cmp6.OC l)) := by
        rw [← BdRPlus.ker_thetaC]
        simpa using h3
      rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h4
      exact h4
    refine ⟨hu, ?_⟩
    apply BdRPlus.ext_eval
    intro n
    have h5 := sub_mem (hy n) (log_sub_mem l ε hu n)
    rw [sub_sub_sub_cancel_right, mem_ker_pow_iff, map_sub, sub_eq_zero] at h5
    exact h5

end Formalism.BasicNotions.CmpTie.LogF
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

set_option maxRecDepth 20000 in
theorem logarithm_compat : ∀ {P : LocPrime l} (AI : LocAinf l P) (y : Per.BdRp l), Per.IsLog l AI.ε y ↔ Per6.IsLog l AI.ε (equivDeRhamPlus l y) := by
  intro P AI y
  exact (LogF.isLog_iff l AI.ε y).trans (Cmp6.isLogA_iff_cP l AI.ε y)

end Formalism.BasicNotions.CmpTie
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

set_option maxRecDepth 20000 in
theorem crystalline_deRham_inclusion_compat : ∀ f : Per.Bcris l →+* Per.BdR l,
    Per.IsCrisDR l f ↔ Per6.IsCrisDR l (((equivDeRham l).toRingHom.comp f).comp (equivCrystalline l).symm.toRingHom) := by
  intro f
  have e : Per.IsCrisDR l f ↔ Incl.IsCrisDRF (p := l) (R := Cmp6.OC l) f :=
    ⟨fun h => ⟨h.on0, h.bdd⟩, fun h => ⟨h.on0, h.bdd⟩⟩
  rw [e]
  exact Incl.incl_F l f

end Formalism.BasicNotions.CmpTie
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

def toCompanionTheory {eB : Per.Bcris l ≃+* Per6.Bcris l} {eD : Per.BdR l ≃+* Per6.BdR l} {eP : Per.BdRp l ≃+* Per6.BdRp l}
    (h : Compat l eB eD eP) {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) : LocTied6 l P AI := by
  refine
    { eB := T.eB.trans eB
      eD := T.eD.trans eD
      zB := fun z => ?_
      zD := fun z => ?_
      om := fun x => ?_
      actB := fun g b => ?_
      actD := fun g b => ?_
      frob := fun b => ?_
      incl := ?_
      fil := fun K a x => ?_
      t := ?_
      ιA := fun a => ?_ }
  · rw [RingEquiv.trans_apply, T.zB z, h.zB z]
  · rw [RingEquiv.trans_apply, T.zD z, h.zD z]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    exact ⟨eP y, by rw [RingEquiv.trans_apply, hy, h.alg y], by rw [h.θ y]; exact hθ⟩
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actB g b, h.σB]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actD g b, h.σD]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.frob b, h.φB]
  · have H := (h.incl _).1 T.incl
    convert H using 1
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.trans_apply, RingEquiv.symm_trans_apply]
  · rw [T.fil K a x, RingEquiv.trans_apply, h.fil a]
  · obtain ⟨y, hy, he⟩ := T.t
    exact ⟨eP y, (h.log AI y).1 hy, by rw [RingEquiv.trans_apply, he, h.alg y]⟩
  · rw [RingEquiv.trans_apply, T.ιA a, h.aB a]

theorem locTied6_of_cmp (hC : Cmp l) (P : LocPrime l) (AI : LocAinf l P) :
    Nonempty (LocTied l P AI) → Nonempty (LocTied6 l P AI) := by
  rintro ⟨T⟩
  obtain ⟨eB, eD, eP, h⟩ := hC
  exact ⟨toCompanionTheory h T⟩

end Formalism.BasicNotions.CmpTie
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

def ofSix {eB : Per.Bcris l ≃+* Per6.Bcris l} {eD : Per.BdR l ≃+* Per6.BdR l} {eP : Per.BdRp l ≃+* Per6.BdRp l}
    (h : Compat l eB eD eP) {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : LocTied l P AI := by
  refine
    { eB := T.eB.trans eB.symm
      eD := T.eD.trans eD.symm
      zB := fun z => ?_
      zD := fun z => ?_
      om := fun x => ?_
      actB := fun g b => ?_
      actD := fun g b => ?_
      frob := fun b => ?_
      incl := ?_
      fil := fun K a x => ?_
      t := ?_
      ιA := fun a => ?_ }
  · rw [RingEquiv.trans_apply, T.zB z, ← h.zB z, RingEquiv.symm_apply_apply]
  · rw [RingEquiv.trans_apply, T.zD z, ← h.zD z, RingEquiv.symm_apply_apply]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    refine ⟨eP.symm y, ?_, ?_⟩
    · rw [RingEquiv.trans_apply, hy, RingEquiv.symm_apply_eq, h.alg, RingEquiv.apply_symm_apply]
    · rw [← h.θ, RingEquiv.apply_symm_apply]; exact hθ
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actB g b, RingEquiv.symm_apply_eq, h.σB,
      RingEquiv.apply_symm_apply]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actD g b, RingEquiv.symm_apply_eq, h.σD,
      RingEquiv.apply_symm_apply]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.frob b, RingEquiv.symm_apply_eq, h.φB,
      RingEquiv.apply_symm_apply]
  · refine (h.incl _).2 ?_
    convert T.incl using 1
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.trans_apply, RingEquiv.symm_trans_apply, RingEquiv.apply_symm_apply,
      RingEquiv.symm_symm]
  · rw [T.fil K a x, RingEquiv.trans_apply, h.fil a, RingEquiv.apply_symm_apply]
  · obtain ⟨y, hy, he⟩ := T.t
    refine ⟨eP.symm y, (h.log AI (eP.symm y)).2 (by rw [RingEquiv.apply_symm_apply]; exact hy), ?_⟩
    rw [RingEquiv.trans_apply, he, RingEquiv.symm_apply_eq, h.alg, RingEquiv.apply_symm_apply]
  · rw [RingEquiv.trans_apply, T.ιA a, ← h.aB a, RingEquiv.symm_apply_apply]

theorem local_comparison_of_comparison (hC : Cmp l) (P : LocPrime l) (AI : LocAinf l P) :
    Nonempty (LocTied6 l P AI) → Nonempty (LocTied l P AI) := by
  rintro ⟨T⟩
  obtain ⟨eB, eD, eP, h⟩ := hC
  exact ⟨ofSix h T⟩

end Formalism.BasicNotions.CmpTie
end
end

section
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem compat_F (l : ℕ) [Fact l.Prime] : Compat l (equivCrystalline l) (equivDeRham l) (equivDeRhamPlus l) :=
  ⟨integer_to_crystalline_compat l, integer_to_deRham_compat l, deRham_plus_algebraMap_compat l, theta_deRham_compat l, galois_action_crystalline_compat l, galois_action_deRham_compat l, frobenius_crystalline_compat l, crystalline_deRham_inclusion_compat l, filtration_deRham_compat l, fun AI y => logarithm_compat l AI y,
    ainf_to_crystalline_compat l⟩

theorem cmp_F (l : ℕ) [Fact l.Prime] : Cmp l := ⟨_, _, _, compat_F l⟩

theorem locTied6_F : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied l P AI) → Nonempty (Formalism.BasicNotions.LocTied6 l P AI) :=
  fun l _ P AI => locTied6_of_cmp (cmp_F l) P AI

theorem local_comparison_from_alternative : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied6 l P AI) → Nonempty (Formalism.BasicNotions.LocTied l P AI) :=
  fun l _ P AI => local_comparison_of_comparison (cmp_F l) P AI

end Formalism.BasicNotions.CmpTie
end
end
