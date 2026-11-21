import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EqZeroOfMemFactorial
import Formalism.LocalToGlobal.IndefiniteReal.PHeisThC
import ReciprocityTheory.AdeleApproximation.AdeleIntA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IsOpenIntSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInterAlt

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Topology NumberField.InfinitePlace.Completion
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem pairA_add (a a' : Ainf F) (b b' : Af F) : pairA F (a + a') (b + b') = pairA F a b + pairA F a' b' := rfl

theorem pairA_split (a : Ainf F) (b : Af F) : pairA F a b = pairA F a 0 + pairA F 0 b := by
  rw [← pairA_add, add_zero, zero_add]

theorem algebraMap_AF (q : F) :
    algebraMap F (AF F) q = pairA F (algebraMap F (Ainf F) q) (algebraMap F (Af F) q) := rfl

theorem trace_int (y : 𝓞 F) : ∃ z : ℤ, Algebra.trace ℚ F (y : F) = z := by
  have h : IsIntegral ℤ (Algebra.trace ℚ F (y : F)) := Algebra.isIntegral_trace y.isIntegral_coe
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨z, by rw [← hz]; simp⟩


theorem exp_two_pi_int (n : ℤ) : Complex.exp (2 * Real.pi * Complex.I * n) = 1 := by
  rw [show (2 * Real.pi * Complex.I * n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem exists_nsmul_mem_cpt {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (K : Set X) (hK : IsCompact K) (hKs : ∀ y ∈ K, ∀ n : ℕ, n • y ∈ K) (H : AddSubgroup X)
    (hH : IsOpen (H : Set X)) : ∃ m : ℕ, 0 < m ∧ ∀ y ∈ K, m • y ∈ H := by
  classical
  haveI : DiscreteTopology (X ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hSfin : ((fun y : X => (y : X ⧸ H)) '' K).Finite :=
    (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hord : ∀ y ∈ K, IsOfFinAddOrder (y : X ⧸ H) := by
    intro y hy
    obtain ⟨a, b, hab, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => ((n • y : X) : X ⧸ H)) (fun n => Set.mem_image_of_mem _ (hKs y hy n)) hSfin
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨c + 1, Nat.succ_pos c, ?_⟩
    have h2 : (a + (c + 1)) • (y : X ⧸ H) = a • (y : X ⧸ H) := by
      rw [← Nat.add_assoc, ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_nsmul]
      exact he.symm
    rw [add_nsmul] at h2
    simpa using h2
  refine ⟨∏ q ∈ hSfin.toFinset, addOrderOf q, ?_, ?_⟩
  · apply Finset.prod_pos
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hSfin.mem_toFinset.mp hq
    exact (hord y hy).addOrderOf_pos
  · intro y hy
    have hmem : (y : X ⧸ H) ∈ hSfin.toFinset := hSfin.mem_toFinset.mpr ⟨y, hy, rfl⟩
    have h0 : (∏ q ∈ hSfin.toFinset, addOrderOf q) • (y : X ⧸ H) = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (Finset.dvd_prod_of_mem (fun q => addOrderOf q) hmem)
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h0
    exact h0

end Gen

section Psi

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem sum_fEmb (x : D.host.F) : ∑ τ : D.what₂.Tau, Eqv.fEmb D τ x = ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) := by
  classical
  have hb : Function.Bijective (fun τ => Eqv.fEmb D τ) := by
    constructor
    · intro τ τ' h
      simp only at h
      have h' : Eqv.plW D τ = Eqv.plW D τ' := by
        show InfinitePlace.mk (Eqv.fEmb D τ) = InfinitePlace.mk (Eqv.fEmb D τ')
        rw [h]
      rw [Eqv.plW_eq_tauPl, Eqv.plW_eq_tauPl] at h'
      exact (Formalism.L2.Host.tauPl D).injective h'
    · intro φ
      refine ⟨(Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ), ?_⟩
      have h1 := Eqv.plW_embedding D ((Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ))
      rw [Eqv.plW_symm] at h1
      have hr := Eqv.fEmb_isReal D ((Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ))
      show Eqv.fEmb D _ = φ
      rcases InfinitePlace.embedding_mk_eq φ with h2 | h2
      · rw [← h1, h2]
      · rw [← h1] at hr
        rw [← h1, h2]
        rw [h2] at hr
        exact ComplexEmbedding.isReal_conjugate_iff.mp hr
  have htr := trace_eq_sum_embeddings (K := ℚ) (L := D.host.F) (E := ℂ) (x := x)
  rw [show ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ D.host.F x) from
    (eq_ratCast _ _).symm, htr]
  let e : (D.host.F →+* ℂ) ≃ (D.host.F →ₐ[ℚ] ℂ) := RingHom.equivRatAlgHom D.host.F ℂ
  exact Fintype.sum_bijective (e ∘ fun τ => Eqv.fEmb D τ) (e.bijective.comp hb) _ _ (fun τ => rfl)

theorem psi_inf (hψ : IsStdChar D ψ (-1)) (a : Ainf D.host.F) :
    ψ (pairA D.host.F a 0) = Complex.exp (-(2 * Real.pi * Complex.I * ∑ τ, Eqv.gW D (Eqv.plW D τ) a)) := by
  obtain ⟨-, -, hθ⟩ := hψ
  have h := hθ (Eqv.thetaC D) (Eqv.isInfFam_thetaC D) a
  simp only [Eqv.thetaC_tmul, map_one, mul_one] at h
  rw [show ψ (pairA D.host.F a 0) = psiInf D.host.F ψ a from rfl, h]
  congr 1
  push_cast
  ring

theorem psi_fin_rat (hψ : IsStdChar D ψ (-1)) (q : D.host.F) :
    ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
      Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ D.host.F q : ℚ)) := by
  have hrat : ψ (algebraMap D.host.F (AF D.host.F) q) = 1 := by
    obtain ⟨⟨-, -, h, -⟩, -⟩ := hψ
    exact h q
  have hinf := psi_inf hψ (algebraMap D.host.F (Ainf D.host.F) q)
  simp only [Eqv.gW_algebraMap, sum_fEmb] at hinf
  rw [algebraMap_AF, pairA_split, AddChar.map_add_eq_mul, hinf] at hrat
  have h2 := congrArg
    (fun w => Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F q : ℚ) : ℂ)) * w) hrat
  simp only [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul, mul_one] at h2
  exact h2


theorem psi_pair0_add (a b : Af D.host.F) :
    ψ (pairA D.host.F 0 (a + b)) = ψ (pairA D.host.F 0 a) * ψ (pairA D.host.F 0 b) := by
  rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]


theorem psi_invDiff (hψ : IsStdChar D ψ (-1)) (d : D.host.F) (hd : d ∈ invDiff D.host.F) (y : Af D.host.F)
    (hy : y ∈ intAf D.host.F) : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d * y)) = 1 := by
  obtain ⟨G, hGo, -, hG⟩ := Formalism.IndefR.PHeisTh.psiOpen D.host.F ψ hψ.1
  let md : Af D.host.F →+ Af D.host.F := AddMonoidHom.mulLeft (algebraMap D.host.F (Af D.host.F) d)
  let H : AddSubgroup (Af D.host.F) := AddSubgroup.comap md G
  have hHo : IsOpen (H : Set (Af D.host.F)) := hGo.preimage (continuous_const.mul continuous_id)
  obtain ⟨m, hm, hmH⟩ := exists_nsmul_mem_cpt (Formalism.IndefR.PHeisFC.Ohat D.host.F)
    (Formalism.IndefR.PHeisFC.isCompact_Ohat D.host.F)
    (fun y hy n => (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd D.host.F).toAddSubgroup.nsmul_mem hy n) H hHo
  have hm0 : ((m : ℕ) : 𝓞 D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  obtain ⟨a, ha⟩ := ReciprocityTheory.UG.AdeleIntA.exists_approx y (fun v => hy v) _ hm0

  set z : Af D.host.F := algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) *
    (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F)) with hz
  have hmF : (m : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hyz : y = algebraMap D.host.F (Af D.host.F) (a : D.host.F) + m • z := by
    rw [hz, nsmul_eq_mul, ← mul_assoc, show (m : Af D.host.F) = algebraMap D.host.F (Af D.host.F) (m : D.host.F) by
      simp, ← map_mul, mul_one_div_cancel hmF, map_one, one_mul]
    abel
  have hzint : z ∈ Formalism.IndefR.PHeisFC.Ohat D.host.F := by
    intro v
    have hv := ha v
    show (algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) *
      (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F))) v ∈ v.adicCompletionIntegers D.host.F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : (algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) *
        (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F))) v =
        algebraMap D.host.F (v.adicCompletion D.host.F) (1 / (m : D.host.F)) *
          (y v - algebraMap D.host.F _ (algebraMap (𝓞 D.host.F) D.host.F a)) := rfl
    rw [e, map_mul]
    have hval : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (1 / (m : D.host.F))) =
        (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹ := by
      rw [one_div, map_inv₀, map_inv₀]
      congr 1
      rw [show ((m : ℕ) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F ((m : ℕ) : 𝓞 D.host.F) by simp]
      exact ReciprocityTheory.UG.AdeleIntA.val_R v _
    rw [hval]
    have hv0 : v.intValuation ((m : ℕ) : 𝓞 D.host.F) ≠ 0 := v.intValuation_ne_zero _ hm0
    calc (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹ * Valued.v _
        ≤ (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹ * v.intValuation ((m : ℕ) : 𝓞 D.host.F) :=
          mul_le_mul' le_rfl hv
      _ = 1 := inv_mul_cancel₀ hv0
  rw [hyz, mul_add, psi_pair0_add]
  have h1 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d *
      algebraMap D.host.F (Af D.host.F) (a : D.host.F))) = 1 := by
    rw [← map_mul, psi_fin_rat hψ]
    obtain ⟨n, hn⟩ := hd a
    rw [hn]; push_cast; exact exp_two_pi_int n
  have h2 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d * m • z)) = 1 :=
    hG _ (hmH z hzint)
  rw [h1, h2, one_mul]

end Psi

section Kernel

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem isInt_of_intAf (y : Af D.host.F) (hy : y ∈ intAf D.host.F) : ReciprocityTheory.UG.AdeleIntA.IsInt y := by
  simp only [Formalism.MainNotions.StandardLattice.intAf, ReciprocityTheory.UG.AdeleIntA.IsInt] at hy ⊢
  exact hy

theorem intAf_of_isInt (y : Af D.host.F) (hy : ReciprocityTheory.UG.AdeleIntA.IsInt y) : y ∈ intAf D.host.F := by
  simp only [Formalism.MainNotions.StandardLattice.intAf, ReciprocityTheory.UG.AdeleIntA.IsInt] at hy ⊢
  exact hy

theorem intAf_mul {x y : Af D.host.F} (hx : x ∈ intAf D.host.F) (hy : y ∈ intAf D.host.F) : x * y ∈ intAf D.host.F := by
  exact intAf_of_isInt _ (ReciprocityTheory.UG.AdeleIntA.isInt_mul (isInt_of_intAf _ hx) (isInt_of_intAf _ hy))


theorem intAf_int (r : 𝓞 D.host.F) : algebraMap D.host.F (Af D.host.F) (r : D.host.F) ∈ intAf D.host.F := by
  have h := ReciprocityTheory.UG.AdeleIntA.isInt_R (K := D.host.F) r
  rw [IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F] at h
  exact intAf_of_isInt _ h

theorem one_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := by
  simpa using intAf_int (D := D) 1







end Kernel

section Exist

variable {D : D7}

def Linf (D : D7) : Ainf D.host.F →+ ℝ where
  toFun a := -∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) a).re
  map_zero' := by simp
  map_add' a b := by simp only [map_add, Complex.add_re, Finset.sum_add_distrib, neg_add]

theorem continuous_Linf : Continuous (Linf D) := by
  have hg : ∀ τ, Continuous fun a : Ainf D.host.F => Eqv.gW D (Eqv.plW D τ) a := fun τ =>
    (isometry_extensionEmbedding _).continuous.comp (continuous_apply _)
  show Continuous fun a => -∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) a).re
  exact (continuous_finset_sum _ fun τ _ => Complex.continuous_re.comp (hg τ)).neg

theorem sum_gW_eq (a : Ainf D.host.F) : ∑ τ : D.what₂.Tau, Eqv.gW D (Eqv.plW D τ) a = ((-(Linf D a) : ℝ) : ℂ) := by
  have h : ∀ τ, Eqv.gW D (Eqv.plW D τ) a = (((Eqv.gW D (Eqv.plW D τ) a).re : ℝ) : ℂ) := by
    intro τ
    rw [Eqv.gW_real]
    simp
  show ∑ τ, Eqv.gW D (Eqv.plW D τ) a = ((-(-∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) a).re) : ℝ) : ℂ)
  rw [neg_neg, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun τ _ => h τ

theorem Linf_int (b : 𝓞 D.host.F) : ∃ n : ℤ, Linf D (algebraMap D.host.F (Ainf D.host.F) (b : D.host.F)) = n := by
  obtain ⟨z, hz⟩ := trace_int b
  refine ⟨-z, ?_⟩
  show -∑ τ : D.what₂.Tau,
      (Eqv.gW D (Eqv.plW D τ) (algebraMap D.host.F (Ainf D.host.F) (b : D.host.F))).re = ((-z : ℤ) : ℝ)
  rw [show (∑ τ : D.what₂.Tau,
      (Eqv.gW D (Eqv.plW D τ) (algebraMap D.host.F (Ainf D.host.F) (b : D.host.F))).re) =
      (∑ τ : D.what₂.Tau, Eqv.fEmb D τ b).re by rw [Complex.re_sum]; simp only [Eqv.gW_algebraMap]]
  rw [sum_fEmb, hz]
  simp

theorem exists_Linf_half : ∃ t : Ainf D.host.F, Linf D t = 1 / 2 := by
  have hn0 : ((Module.finrank ℚ D.host.F : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hq : (Module.finrank ℚ D.host.F • (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ)))) : ℚ) = -(1 / 2) := by
    rw [nsmul_eq_mul]
    field_simp
  refine ⟨algebraMap D.host.F (Ainf D.host.F)
    (algebraMap ℚ D.host.F (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ))))), ?_⟩
  have h := congrArg Complex.re
    (sum_fEmb (D := D) (algebraMap ℚ D.host.F (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ))))))
  rw [Algebra.trace_algebraMap, hq, Complex.re_sum] at h
  show -∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) (algebraMap D.host.F (Ainf D.host.F)
    (algebraMap ℚ D.host.F (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ))))))).re = 1 / 2
  simp only [Eqv.gW_algebraMap, h]
  norm_num

theorem exists_stdChar : ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) := by
  let F := D.host.F
  let mk : ℝ →+ AddCircle (1 : ℝ) := QuotientAddGroup.mk' _
  have hmk : Continuous mk := continuous_quotient_mk'
  let fs : AF F →+ Ainf F := (fstA F).toRingHom.toAddMonoidHom
  have hfs : Continuous fs := continuous_fst
  let g : AF F →+ AddCircle (1 : ℝ) := mk.comp ((Linf D).comp fs)
  have hg : Continuous g := hmk.comp (continuous_Linf.comp hfs)
  let K : AddSubgroup (AF F) := (algebraMap F (AF F)).range.toAddSubgroup
  obtain ⟨h, hc, hK, hU⟩ := PI.GaugeCharW.extChar (AF F) K (PI.GaugeCharW.intSub F)
    (PI.GaugeCharW.isOpen_intSub F PI.GaugeCharW.openInt) g hg (by
      rintro x ⟨a, rfl⟩ hx
      obtain ⟨b, rfl⟩ := PI.GaugeCharW.intInter F a (fun v => by
        have hv := hx v
        rwa [AlgHom.commutes] at hv)
      obtain ⟨n, hn⟩ := Linf_int (D := D) b
      have e1 : fs (algebraMap F (AF F) (b : F)) = algebraMap F (Ainf F) (b : F) := rfl
      show mk (Linf D (fs (algebraMap F (AF F) (b : F)))) = 0
      rw [e1, hn]
      show ((n : ℝ) : AddCircle (1 : ℝ)) = 0
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩)
  let ψ : AddChar (AF F) ℂ :=
    { toFun := fun x => ((AddCircle.toCircle (h x) : Circle) : ℂ),
      map_zero_eq_one' := by simp,
      map_add_eq_mul' := fun x y => by simp [map_add, AddCircle.toCircle_add] }
  have hval : ∀ t : Ainf F, ψ (pairA F t 0) = Complex.exp (2 * Real.pi * Complex.I * (Linf D t : ℂ)) := by
    intro t
    have hx0 : pairA F t 0 ∈ PI.GaugeCharW.intSub F := fun v => by
      show (0 : Af F) v ∈ _
      exact zero_mem _
    show ((AddCircle.toCircle (h (pairA F t 0)) : Circle) : ℂ) = _
    rw [hU _ hx0]
    show ((AddCircle.toCircle ((Linf D t : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = _
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 1; push_cast; ring
  refine ⟨ψ, ⟨?_, ?_, ?_, ?_⟩, ⟨Eqv.thetaC D, Eqv.isInfFam_thetaC D⟩, fun θ hθ x => ?_⟩
  · exact continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp hc)
  · intro x; exact Circle.norm_coe _
  · intro a
    have ha : h (algebraMap F (AF F) a) = 0 := hK _ ⟨a, rfl⟩
    show ((AddCircle.toCircle (h (algebraMap F (AF F) a)) : Circle) : ℂ) = 1
    simp [ha]
  · obtain ⟨t, ht⟩ := exists_Linf_half (D := D)
    refine ⟨pairA F t 0, ?_⟩
    rw [hval, ht]
    have : Complex.exp (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = -1 := by
      rw [show 2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ) = Real.pi * Complex.I by push_cast; ring,
        Complex.exp_pi_mul_I]
    rw [this]; norm_num
  · rw [Eqv.eq_thetaC D hθ]
    unfold psiInf
    rw [hval]
    congr 1
    have e : ∑ ρ, Eqv.thetaC D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) = ((-(Linf D x) : ℝ) : ℂ) := by
      rw [← sum_gW_eq]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Eqv.thetaC_tmul, map_one, mul_one]
    rw [e]; push_cast; ring


end Exist

end Formalism.IndefR.Fin

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix Topology
open scoped TensorProduct ComplexConjugate Pointwise

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

abbrev QO : Type := MO S T ⧸ ratL T S

def chiO (ψ : AddChar (AF D.host.F) ℂ) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) : ℂ :=
  ψ (symplO S T z (ratW T S a))

theorem periodic_of {f : MO S T → ℂ} (hf : ∀ a z, f (ratW T S a + z) = f z) :
    ∀ g ∈ ratL T S, ∀ z, f (g + z) = f z := by
  intro g hg z
  obtain ⟨a, rfl⟩ := (mem_ratL_iff S T g).1 hg
  exact hf a z

theorem chiO_periodic (hψ : IsStdChar D ψ (-1)) (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) :
    chiO S T ψ a (ratW T S b + z) = chiO S T ψ a z := by
  unfold chiO
  rw [symplO_add_left, AddChar.map_add_eq_mul, psi_rat hψ, one_mul]

def liftQ (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) : QO S T → ℂ :=
  Quotient.lift f (by
    intro x y hxy
    have h : -x + y ∈ ratL T S := QuotientAddGroup.leftRel_apply.1 hxy
    have := periodic_of S T hf (-x + y) h x
    rw [show -x + y + x = y by abel] at this
    exact this.symm)

theorem cont_liftQ (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) (hc : Continuous f) :
    Continuous (liftQ S T f hf) :=
  hc.quotient_lift _

def liftC (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) (hc : Continuous f) : C(QO S T, ℂ) :=
  ⟨liftQ S T f hf, cont_liftQ S T f hf hc⟩


def chiC (hψ : IsStdChar D ψ (-1)) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : C(QO S T, ℂ) :=
  liftC S T (chiO S T ψ a) (fun b z => chiO_periodic S T hψ a b z)
    ((psi_cont hψ).comp (cont_symplO_left S T _))

theorem chiC_apply (hψ : IsStdChar D ψ (-1)) (a) (z : MO S T) :
    chiC S T hψ a (z : QO S T) = ψ (symplO S T z (ratW T S a)) := rfl

theorem chiC_mul (hψ : IsStdChar D ψ (-1)) (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    chiC S T hψ a * chiC S T hψ b = chiC S T hψ (a + b) := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.mul_apply, chiC_apply, ratW_add, symplO_add_right, AddChar.map_add_eq_mul]

theorem chiC_zero (hψ : IsStdChar D ψ (-1)) : chiC S T hψ 0 = 1 := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.one_apply, chiC_apply, ratW_zero, symplO_zero_right, AddChar.map_zero_eq_one]

theorem chiC_star (hψ : IsStdChar D ψ (-1)) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    star (chiC S T hψ a) = chiC S T hψ (-a) := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [ContinuousMap.star_apply, chiC_apply, chiC_apply, ratW_neg, symplO_neg_right]
  exact psi_conj hψ _

def Achar (hψ : IsStdChar D ψ (-1)) : StarSubalgebra ℂ C(QO S T, ℂ) where
  carrier := Submodule.span ℂ (Set.range (chiC S T hψ))
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  mul_mem' := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem x hx =>
      induction hg using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        rw [chiC_mul]
        exact Submodule.subset_span ⟨a + b, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
      | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  one_mem' := by
    rw [← chiC_zero S T hψ]; exact Submodule.subset_span ⟨0, rfl⟩
  algebraMap_mem' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, ← chiC_zero S T hψ]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)
  star_mem' := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [chiC_star]; exact Submodule.subset_span ⟨-a, rfl⟩
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [star_add]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [star_smul]; exact Submodule.smul_mem _ _ h






end Formalism.IndefR.Fin

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Topology Filter
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tate

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


end Tate

section Matrix

variable {D : D7} (S T : HSp D)

theorem embedding_xi_zero_ne_zero : D.host.xi0 ≠ 0 := by
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hdpos : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hd
    have : (Real.sqrt D.host.d : ℂ) = 0 := by
      rcases mul_eq_zero.1 hd.symm with h | h
      · exact absurd h Complex.I_ne_zero
      · exact h
    exact (Real.sqrt_pos.2 hdpos).ne' (by exact_mod_cast this)
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  unfold Host.xi0
  exact div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero hN hs)

def hE (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  ∑ a, ∑ b, ∑ c, ∑ d, S.gram⁻¹ a b * star (γ c b) * T.gram c d * e d a

def betaO (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.F :=
  Algebra.trace D.host.F D.host.E (D.host.xi0 * hE S T e γ)

theorem symplO_ratW_ratW (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (ratW T S e) (ratW T S γ) = algebraMap D.host.F (AF D.host.F) (betaO S T e γ) := by
  have h : hO S T (ratW T S e) (ratW T S γ) = incA D (hE S T e γ) := by
    unfold hO hE
    simp only [map_sum, map_mul, ratW, Matrix.map_apply, Brg.cA_inc]
  unfold symplO betaO
  rw [h, ← map_mul, trace_incA]

theorem symplO_smul_left (c : AF D.host.F) (x y : WO S T) : symplO S T (c • x) y = c * symplO S T x y := by
  have h : hO S T (c • x) y = algebraMap (AF D.host.F) (AE D) c * hO S T x y := by
    unfold hO
    simp only [Matrix.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring
  unfold symplO
  rw [h, mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

def symplLin (y : WO S T) : WO S T →ₗ[AF D.host.F] AF D.host.F where
  toFun x := symplO S T x y
  map_add' x x' := symplO_add_left S T x x' y
  map_smul' c x := symplO_smul_left S T c x y

theorem betaO_add_right (e γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    betaO S T e (γ + γ') = betaO S T e γ + betaO S T e γ' := by
  unfold betaO hE
  rw [← map_add, ← mul_add]
  congr 2
  simp only [Matrix.add_apply, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hE_smul_right (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hE S T e (q • γ) = algebraMap D.host.F D.host.E q * hE S T e γ := by
  unfold hE
  have h : ∀ c b, star ((q • γ) c b) = algebraMap D.host.F D.host.E q * star (γ c b) := fun c b => by
    rw [Matrix.smul_apply, Algebra.smul_def, star_mul', Eqv.star_algebraMapF, mul_comm]
  simp only [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem hE_smul_left (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hE S T (q • e) γ = algebraMap D.host.F D.host.E q * hE S T e γ := by
  unfold hE
  simp only [Matrix.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem trace_alg_mul (q : D.host.F) (z : D.host.E) :
    Algebra.trace D.host.F D.host.E (D.host.xi0 * (algebraMap D.host.F D.host.E q * z)) =
      q * Algebra.trace D.host.F D.host.E (D.host.xi0 * z) := by
  rw [mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem betaO_smul_right (q : D.host.F) (e γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    betaO S T e (q • γ) = q * betaO S T e γ := by
  unfold betaO; rw [hE_smul_right, trace_alg_mul]



def epsO (a : Formalism.IndefR.PHeisTh.Ix T S) : Matrix (Fin T.rank) (Fin S.rank) D.host.E :=
  Matrix.single a.1 a.2.1 (Module.finBasis D.host.F D.host.E a.2.2)



def LamO : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F] (Formalism.IndefR.PHeisTh.Ix T S → D.host.F) where
  toFun γ a := betaO S T (epsO S T a) γ
  map_add' γ γ' := by funext a; exact betaO_add_right S T _ γ γ'
  map_smul' q γ := by funext a; exact betaO_smul_right S T q _ γ







end Matrix

end Formalism.IndefR.Fin

end
end
