import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightEqOneLatticeStabilizerComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPoints

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_haar_realPoints_times_level : ∀ D : D7, LevFacts D → ForStage D fun c _ s => MeasurableSet (intOff c s) ∧ MeasurableSet {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ∧ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ⊆ intOff c s ∧ (∀ g : GA D s.V, Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L → ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} s.ν ∧ ∫ g in {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}, F g ∂s.ν = ∫ b, f b ∂mR := by
  first | exact @GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real | exact GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real | (intros; apply GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_equivariant_real_points : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ (v : M.Vec) (b : GinfC V), ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)) (v τ : M.H τ)) ∧ ∀ U ∈ Mult θ M J χ, U w = rTr V (b : GA D V) (U v) := by
  first | exact @GlobalTheory.ChainOnto.mult_equiv_real | exact GlobalTheory.ChainOnto.mult_equiv_real | (intros; apply GlobalTheory.ChainOnto.mult_equiv_real <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.PetCoef

theorem pet_smul_left {D : D7} (s : PiLocalization₂ D) (a : ℂ) (f g : GA D s.V → ℂ) :
    s.pet (a • f) g = a * s.pet f g := by
  unfold PiLocalization₂.pet Lift.pet
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul a _

theorem petco : ∀ D : D7, ForStage D fun c _ s => ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = Lev.levChi s.V s.β s.L κ * ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  intro D c hc j hj s hs ipD ip hM u v b κ hκ
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  obtain ⟨w, hw, hU⟩ := GlobalTheory.T.multiplicitySpace_equivariant_real_points D c.θ s.V s.par s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) hc.inf v b
  have hUw := hU _ hmem
  have ev : ∀ x : s.M.Vec, PiLocalization₂.val u (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) x := by
    intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ • PiLocalization₂.val u (PiTensorProduct.tprod ℂ w) := by
    funext g
    rw [ev, ev, hUw]
    simp only [rTr, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    exact hmap.lev v κ hκ (g * (b : GA D s.V))
  have hsch : s.pet (PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
      ip u u * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u u _ _
  rw [key, pet_smul_left, hsch, hM.pure w v]
  simp only [hw, mul_assoc]

end GlobalTheory.ChainOnto.PetCoef
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_petersson_value_realLevelTranslate : ∀ D : D7, ForStage D fun c _ s => ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = Lev.levChi s.V s.β s.L κ * ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.ChainOnto.PetCoef.petco | exact GlobalTheory.ChainOnto.PetCoef.petco | (intros; apply GlobalTheory.ChainOnto.PetCoef.petco <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.ZetaNeProof

variable {D : D7}

theorem coefW_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (hlaw : ∀ κ ∈ Lev.levG s.V s.β s.L, (p.ω (κ, 1)) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.pt φ)
    (b : GA D s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    coefW p.ω m X (p.pt φ) (b * κ) = Lev.levChi s.V s.β s.L κ * coefW p.ω m X (p.pt φ) b := by
  have hmul : p.ω (b * κ, 1) = p.ω (b, 1) * p.ω (κ, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : p.ω (b * κ, 1) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.ω (b, 1) (p.pt φ) := by
    rw [hmul, Module.End.mul_apply, hlaw κ hκ, map_smul]
  unfold coefW
  rw [hv, ← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem hgtS_mul_lev {c : Com D} {s : PiLocalization₂ D} (hs : IsSelfDualC s.V s.Λ)
    (hstab : ∀ k ∈ Lev.levG s.V s.β s.L, ∀ v,
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (a : GL (Fin s.V.rank) (AE D)) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    hgtS c s a ((b : GA D s.V) * κ) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.doublingHeight_eq_one_lattice_stabilizer_components D s.V s.Λ hs
  have hκf : κ ∈ GfC s.V := (Subgroup.mem_inf.mp hκ).1
  unfold hgtS
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := by
    intro w
    rw [map_mul, h2 κ hκf w, mul_one]
  have hF : ∀ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v
      (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v ((b : GA D s.V) * κ)) = 1 := by
    intro v _
    rw [map_mul, h3 b b.2 v, one_mul]
    exact h1 v _ (hstab κ hκ v)
  simp only [hA]
  rw [Finset.prod_eq_one hF, mul_one]

theorem zetaNe_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  intro D hMet hLev hLaw hSupp hRZ
  intro hng c hc k hk s s' hs hs' p hp m X hcov
  obtain ⟨φ, v, hvK, hR⟩ := hRZ hng c hc k hk s s' hs hs' p hp m X hcov
  have hkm : k ≤ D.R.m := hk.le
  obtain ⟨ipD, ip, hip⟩ := hMet c hc k hkm s hs
  obtain ⟨_, _, hLF3, _, _, hLF6⟩ := hLev c hc k hkm s hs
  obtain ⟨hmOff, _, hAsub, _, mR, hmR, hint⟩ := GlobalTheory.T.pushforward_haar_realPoints_times_level D hLev c hc k hkm s hs
  have hpet := GlobalTheory.T.thetaChainStage_petersson_value_realLevelTranslate D c hc k hkm s hs ipD ip hip
  have hlaw := (hLaw hng c hc k hk s s' hs hs' p hp φ).1
  have hsupp := hSupp hng c hc k hk s s' hs hs' p hp m X hcov φ
  obtain ⟨hz, hzI⟩ := hR mR hmR
  refine ⟨φ, PiTensorProduct.tprod ℂ v, Submodule.subset_span ⟨v, hvK, rfl⟩, ?_⟩
  intro u hu
  have hipu : ip u u ≠ 0 := by
    intro h0
    have := hip.pos u hu
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hcipu : conj (ip u u) ≠ 0 := (map_ne_zero _).mpr hipu

  have hlawZ : ∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) ((b : GA D s.V) * κ) =
        conj (ip u u) * (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
          conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) := by
    intro b κ hκ
    unfold Step.zint
    rw [coefW_mul_lev p m X φ hlaw _ κ hκ, hpet u v b κ hκ]
    have hn : Lev.levChi s.V s.β s.L κ * conj (Lev.levChi s.V s.β s.L κ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hLF6 κ hκ]
      norm_num
    simp only [map_mul]
    linear_combination (conj (ip u u) * coefW p.ω m X (p.pt φ) (b : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) * hn

  have hoff : ∀ g ∈ intOff c s \ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L},
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) g = 0 := by
    rintro g ⟨hg, hgA⟩
    unfold Step.zint
    rw [hsupp g hg hgA, zero_mul]
  have hzInt : Integrable (fun g : GinfC s.V => coefW p.ω m X (p.pt φ) (g : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) mR := by
    by_contra hni
    exact hz (integral_undef hni)
  refine ⟨?_, ?_⟩
  · rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmOff hAsub hoff]
    rw [(hint _ _ (hzInt.const_mul (conj (ip u u))) hlawZ).2, integral_const_mul]
    exact mul_ne_zero hcipu hz
  · intro a hmaj hcomp
    obtain ⟨s₁, hs₁, hI⟩ := hzI a hmaj hcomp
    refine ⟨s₁, hs₁, ?_⟩
    refine IntegrableOn.of_forall_diff_eq_zero (s := {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}) ?_ hmOff ?_
    · refine (hint _ _ (hI.const_mul (conj (ip u u))) ?_).1
      intro b κ hκ
      rw [hlawZ b κ hκ, hgtS_mul_lev hs.selfDual hLF3 a b κ hκ, mul_assoc]
    · intro g hg
      rw [hoff g hg, zero_mul]

end GlobalTheory.ChainOnto.ZetaNeProof

example : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D :=
  GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real
end
