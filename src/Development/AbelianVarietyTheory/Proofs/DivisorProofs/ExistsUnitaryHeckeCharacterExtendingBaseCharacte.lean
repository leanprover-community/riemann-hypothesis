import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable (F : Type) [Field F] [NumberField F]

def finU : (Af F)ˣ →* (AF F)ˣ := Units.map (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_finU : Continuous (finU F) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

def sndU : (AF F)ˣ →* (Af F)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_circle_toUnits : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, by
    have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
    refine h.congr fun z => ?_
    simp⟩

theorem exists_cong_sub (K : Set (Af F)ˣ) (hK : K ∈ 𝓝 1) : ∃ M : ℕ, 0 < M ∧ ∀ u : (Af F)ˣ,
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ (u : Af F) - 1 = M • c) →
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ((u⁻¹ : (Af F)ˣ) : Af F) - 1 = M • c) → u ∈ K := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hK
  obtain ⟨T, hT, hTK⟩ := hK
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : Af F => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : Af F => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : Af F => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (Filter.inter_mem h1 h2)
  refine ⟨N, hN, fun u ⟨a, ha, e⟩ ⟨b, hb, e'⟩ => hTK (hTT ⟨?_, ?_⟩)⟩
  · change (u : Af F) ∈ T1
    rw [eq_add_of_sub_eq' e]; exact (hNW a ha).1
  · change MulOpposite.op ((u⁻¹ : (Af F)ˣ) : Af F) ∈ T2
    rw [eq_add_of_sub_eq' e']; exact (hNW b hb).2

theorem exists_cong_ker (lam : (AF F)ˣ →* Circle) (hlam : Continuous lam)
    (h : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) :
    ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  let ψ : (Af F)ˣ →* ℂˣ := Circle.toUnits.comp (lam.comp (finU F))
  have hψ : Continuous ψ := (continuous_circle_toUnits).comp (hlam.comp (continuous_finU F))
  have hK := (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (x := 1) (by simp)
  obtain ⟨M, hM, hMK⟩ := exists_cong_sub F _ hK
  refine ⟨M, hM, fun b hb hb' => ?_⟩
  obtain ⟨c, hc, e⟩ := hb
  obtain ⟨c', hc', e'⟩ := hb'
  have h2 : ψ (sndU F b) = 1 := hMK (sndU F b) ⟨c, hc, e⟩ ⟨c', hc', e'⟩
  have h3 : lam (finU F (sndU F b)) = 1 := by
    have := congrArg Units.val h2
    exact Subtype.ext (by simpa [ψ] using this)
  set a : (AF F)ˣ := b * (finU F (sndU F b))⁻¹ with ha
  have hfin : ((a : AF F)).2 = 1 := by
    show (b : AF F).2 * ((b⁻¹ : (AF F)ˣ) : AF F).2 = 1
    exact congrArg Prod.snd (Units.mul_inv b)
  have hA : At (evI F) ((a : AF F) - 1) := by
    intro u hu
    have hu1 : u.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
    refine Prod.ext ?_ ?_
    · show u.1 * ((a : AF F).1 - 1) = 0
      rw [hu1, zero_mul]
    · show u.2 * ((a : AF F).2 - 1) = 0
      rw [hfin, sub_self, mul_zero]
  have hb : b = a * finU F (sndU F b) := by rw [ha, inv_mul_cancel_right]
  rw [hb, map_mul, h a hA, h3, mul_one]

end GlobalTheory.HeckeExtend

end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity : ∀ (F : Type) [Field F] [NumberField F] (lam : (AF F)ˣ →* Circle), Continuous lam →
    (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) → ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  first | exact @GlobalTheory.HeckeExtend.exists_cong_ker | exact GlobalTheory.HeckeExtend.exists_cong_ker | (intros; apply GlobalTheory.HeckeExtend.exists_cong_ker <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend.TraceCE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def trAF : AF F ⊗[F] E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ (Algebra.trace F E).baseChange (AF F)

theorem trAF_tmul (s : AF F) (e : E) :
    trAF (s ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) * s := by
  simp [trAF, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem gen_eq (s : AF F) (o : 𝓞 E) :
    algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o = s ⊗ₜ[F] (o : E) := by
  show (s ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] (o : E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem intF_zero : (0 : AF F) ∈ intF F 1 := ⟨0, fun _ => zero_mem _, by rw [one_smul]; rfl⟩

theorem intF_add {x y : AF F} (hx : x ∈ intF F 1) (hy : y ∈ intF F 1) : x + y ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  obtain ⟨d, hd, e'⟩ := hy
  refine ⟨c + d, fun v => add_mem (hc v) (hd v), ?_⟩
  rw [one_smul] at e e' ⊢
  show x.2 + y.2 = c + d
  rw [e, e']

theorem intF_neg {x : AF F} (hx : x ∈ intF F 1) : -x ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  refine ⟨-c, fun v => neg_mem (hc v), ?_⟩
  rw [one_smul] at e ⊢
  show -x.2 = -c
  rw [e]

theorem intF_algebraMap (t : 𝓞 F) : algebraMap F (AF F) (t : F) ∈ intF F 1 :=
  ⟨algebraMap F (Af F) (t : F), fun v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v t,
    by rw [one_smul]; rfl⟩

theorem trAF_mem_of_mem_SE {z : AF F ⊗[F] E} (hz : z ∈ SE F E) : trAF z ∈ intF F 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, o, rfl⟩ := hg
    rw [gen_eq, trAF_tmul]
    have hi : IsIntegral ℤ (Algebra.trace F E (o : E)) := Algebra.isIntegral_trace o.2
    exact intF_one_mul (intF_algebraMap (⟨_, hi⟩ : 𝓞 F)) hs
  | zero => rw [map_zero]; exact intF_zero
  | add a b _ _ ha hb => rw [map_add]; exact intF_add ha hb
  | neg a _ ha => rw [map_neg]; exact intF_neg ha

theorem trAF_algebraMap (x : AF F) :
    trAF (algebraMap (AF F) (AF F ⊗[F] E) x) = Module.finrank F E • x := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, trAF_tmul]
  have h : Algebra.trace F E 1 = (Module.finrank F E : F) := by
    simpa using Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
  rw [h, map_natCast, nsmul_eq_mul]

theorem finrank_smul_mem_intF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  intro F E _ _ _ _ _ N x h
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  have h1 := trAF_algebraMap (E := E) x
  rw [← e, map_nsmul] at h1
  obtain ⟨c, hc, ec⟩ := trAF_mem_of_mem_SE hs
  refine ⟨c, hc, ?_⟩
  rw [← h1]
  rw [one_smul] at ec
  rw [← ec]
  rfl

end GlobalTheory.HeckeExtend.TraceCE

end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  first | exact @GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | exact GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF | (intros; apply GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F : Type} [Field F] [NumberField F]

variable (F) in

theorem intF_isOpen (M : ℕ) (hM : 0 < M) : IsOpen (intF F M) := by
  let S : AddSubgroup (Af F) :=
    { carrier := {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a}
      zero_mem' := ⟨0, fun v => zero_mem _, (smul_zero M).symm⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun v => add_mem (ha v) (hb v), (smul_add M a b).symm⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun v => neg_mem (ha v), (smul_neg M a).symm⟩ }
  have hS : IsOpen (S : Set (Af F)) :=
    S.isOpen_of_mem_nhds (g := 0) (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F M hM)
  have e : intF F M = Prod.snd ⁻¹' (S : Set (Af F)) := by
    ext x
    constructor
    · rintro ⟨c, hc, e⟩
      exact ⟨c, hc, e⟩
    · rintro ⟨c, hc, e⟩
      exact ⟨c, hc, e⟩
  rw [e]
  exact hS.preimage continuous_snd

theorem exists_intF_one_mul (M : ℕ) (hM : 0 < M) {x : AF F} (hx : x ∈ intF F M) :
    ∃ s ∈ intF F 1, (M : AF F) * s = x := by
  obtain ⟨c, hc, e⟩ := hx
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  refine ⟨algebraMap F (AF F) ((M : F)⁻¹) * x, ⟨c, hc, ?_⟩, ?_⟩
  · show (algebraMap F (AF F) ((M : F)⁻¹)).2 * x.2 = 1 • c
    rw [e, one_smul, nsmul_eq_mul]
    have h2 : (algebraMap F (AF F) ((M : F)⁻¹)).2 = algebraMap F (Af F) ((M : F)⁻¹) := rfl
    rw [h2, ← mul_assoc, ← map_natCast (algebraMap F (Af F)) M, ← map_mul, inv_mul_cancel₀ hM', map_one, one_mul]
  · rw [← mul_assoc, ← map_natCast (algebraMap F (AF F)) M, ← map_mul, mul_inv_cancel₀ hM', map_one, one_mul]

end GlobalTheory.HeckeExtend

theorem GlobalTheory.HeckeExtend.CE_isOpen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ), 0 < N → IsOpen (CE F E N : Set (AF F ⊗[F] E)) := by
  intro F E _ _ _ _ _ N hN
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b₀ := Module.finBasis F E
  have hint : ∀ i, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * b₀ i) := by
    intro i
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ E := Algebra.IsAlgebraic.trans ℤ ℚ E
    obtain ⟨y, hy, h⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := b₀ i) (Algebra.IsAlgebraic.isAlgebraic _)
    refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
    have h1 : (((y * y).natAbs : ℕ) : E) = (y : E) * (y : E) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y), Int.cast_mul]
    rw [h1, mul_assoc]
    rw [zsmul_eq_mul] at h
    exact (isIntegral_algebraMap (x := y)).mul h
  choose d hd hdint using hint
  let B := Algebra.TensorProduct.basis (AF F) b₀
  let U : Set (AF F ⊗[F] E) := ⋂ i, (fun z => B.repr z i) ⁻¹' intF F (N * d i)
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => (intF_isOpen F _ (Nat.mul_pos hN (hd i))).preimage ?_
    exact IsModuleTopology.continuous_of_linearMap (B.coord i)
  have h0 : (0 : AF F ⊗[F] E) ∈ U := by
    refine Set.mem_iInter.2 fun i => ⟨0, fun v => zero_mem _, ?_⟩
    show (B.repr 0 i).2 = (N * d i) • 0
    rw [map_zero, smul_zero]
    rfl
  have hsub : U ⊆ (CE F E N : Set (AF F ⊗[F] E)) := by
    intro z hz
    have hz' : ∀ i, B.repr z i ∈ intF F (N * d i) := fun i => Set.mem_iInter.1 hz i
    choose s hs hsx using fun i => exists_intF_one_mul (N * d i) (Nat.mul_pos hN (hd i)) (hz' i)
    refine mem_CE.2 ⟨∑ i, algebraMap (AF F) (AF F ⊗[F] E) (s i) * incAF F E ((⟨(d i : E) * b₀ i, hdint i⟩ : 𝓞 E) : E),
      sum_mem fun i _ => AddSubgroup.subset_closure ⟨s i, hs i, ⟨(d i : E) * b₀ i, hdint i⟩, rfl⟩, ?_⟩
    rw [Finset.smul_sum]
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsx i, Algebra.TensorProduct.basis_apply, nsmul_eq_mul, Algebra.smul_def]
    have h1 : incAF F E ((d i : E) * b₀ i) = (d i : AF F ⊗[F] E) * (1 ⊗ₜ b₀ i) := by
      rw [map_mul, map_natCast]
      rfl
    have hc : ((⟨(d i : E) * b₀ i, hdint i⟩ : 𝓞 E) : E) = (d i : E) * b₀ i := rfl
    rw [hc, h1, map_mul, map_natCast]
    push_cast
    ring
  exact (CE F E N).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds h0) hsub)
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_integralTensorAdeleMultiples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    IsOpen (CE F E N : Set (AF F ⊗[F] E)) := by
  first | exact @GlobalTheory.HeckeExtend.CE_isOpen | exact GlobalTheory.HeckeExtend.CE_isOpen | (intros; apply GlobalTheory.HeckeExtend.CE_isOpen <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section
namespace GlobalTheory.HeckeExtend.AtInf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def uInf (F : Type) [Field F] [NumberField F] : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def uFin (F : Type) [Field F] [NumberField F] : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

theorem uInf_add_uFin : uInf F + uFin F = 1 := by
  show ((1 : InfiniteAdeleRing F) + 0, (0 : FiniteAdeleRing (𝓞 F) F) + 1) = 1
  simp

theorem evI_uFin : evI F (uFin F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem pure_mem (N : ℕ) (hN : 0 < N) (a : AF F) (e : E) :
    ((uInf F * a) ⊗ₜ[F] e : AF F ⊗[F] E) ∈ CE F E N := by
  have halg : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsIntegral.isIntegral (R := ℚ) e).isAlgebraic
  obtain ⟨d, hd, hint⟩ := halg.exists_integral_multiple
  let o : 𝓞 E := ⟨d • e, hint⟩
  have ho : (o : E) = (d : E) * e := by simp [o, zsmul_eq_mul]
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd
  let c : F := ((N : F) * (d : F))⁻¹
  let s : AF F := algebraMap F (AF F) c * (uInf F * a)
  have hs : s ∈ intF F 1 := by
    refine ⟨0, fun v => zero_mem _, ?_⟩
    show (algebraMap F (AF F) c).2 * ((uInf F).2 * a.2) = 1 • 0
    simp [uInf]
  refine mem_CE.2 ⟨algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o,
    AddSubgroup.subset_closure ⟨s, hs, o, rfl⟩, ?_⟩
  have h1 : algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o = s ⊗ₜ[F] (o : E) := by
    simp [incAF, inclR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  have h2 : s = c • (uInf F * a) := (Algebra.smul_def c _).symm
  rw [h1, h2, TensorProduct.smul_tmul, ← TensorProduct.tmul_smul]
  congr 1
  rw [ho, Algebra.smul_def c, nsmul_eq_mul]
  simp only [c, map_inv₀, map_mul, map_natCast, map_intCast]
  field_simp

theorem uInf_smul_mem (N : ℕ) (hN : 0 < N) (w : AF F ⊗[F] E) : uInf F • w ∈ CE F E N := by
  induction w using TensorProduct.induction_on with
  | zero => rw [smul_zero]; exact zero_mem _
  | tmul a e => rw [TensorProduct.smul_tmul', smul_eq_mul]; exact pure_mem N hN a e
  | add x y hx hy => rw [smul_add]; exact add_mem hx hy

theorem mem_CE_of_atInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ w : AF F ⊗[F] E, At (evI F) w → w ∈ CE F E N := by
  intro F E _ _ _ _ _ N hN w hw
  have h0 : uFin F • w = 0 := hw (uFin F) evI_uFin
  have : w = uInf F • w := by
    conv_lhs => rw [← one_smul (AF F) w, ← uInf_add_uFin, add_smul, h0, add_zero]
  rw [this]
  exact uInf_smul_mem N hN w

end GlobalTheory.HeckeExtend.AtInf
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ w : AF F ⊗[F] E, At (evI F) w → w ∈ CE F E N := by
  first | exact @GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | exact GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf | (intros; apply GlobalTheory.HeckeExtend.AtInf.mem_CE_of_atInf <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory.HeckeExtend

theorem exists_int_of_mem_intF : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ), 0 < m →
    algebraMap F (AF F) y ∈ intF F m → ∃ r : 𝓞 F, y = m * r := by
  intro F _ _ y m hm hy
  obtain ⟨c, hc, e⟩ := hy
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y / m) ≤ 1 := by
    intro v
    have h1 : (y : v.adicCompletion F) = ((m : F) : v.adicCompletion F) * c v := by
      have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) e
      simp only [nsmul_eq_mul] at this
      have hL : (algebraMap F (AF F) y).2 v = (y : v.adicCompletion F) := rfl
      have hm' : ((m : FiniteAdeleRing (𝓞 F) F)) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) :=
        (map_natCast _ m).symm
      have hR : ((m : FiniteAdeleRing (𝓞 F) F) * c) v = ((m : F) : v.adicCompletion F) * c v := by
        rw [hm']; rfl
      rw [← hL, ← hR]
      exact this
    have h2 : v.valuation F y = v.valuation F (m : F) * Valued.v (c v) := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h1, map_mul,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hv0 : v.valuation F (m : F) ≠ 0 := (Valuation.ne_zero_iff _).2 hmF
    rw [map_div₀, h2, mul_div_cancel_left₀ _ hv0]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hc v)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y / (m : F)) key
  refine ⟨r, ?_⟩
  have : ((r : 𝓞 F) : F) = y / m := hr
  rw [this, mul_div_cancel₀ _ hmF]

end GlobalTheory.HeckeExtend
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ), 0 < m →
    algebraMap F (AF F) y ∈ intF F m → ∃ r : 𝓞 F, y = m * r := by
  first | exact @GlobalTheory.HeckeExtend.exists_int_of_mem_intF | exact GlobalTheory.HeckeExtend.exists_int_of_mem_intF | (intros; apply GlobalTheory.HeckeExtend.exists_int_of_mem_intF <;> assumption)
end

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory

theorem nat_le_four_of_dvd_of_embeddings_le_four :
    ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ) (r : 𝓞 F), y ≠ 0 → y = m * r →
    (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4) → m ≤ 4 := by
  intro F _ _ y m r hy hyr hφ
  set d := Module.finrank ℚ F with hd
  have hr : (r : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, mul_zero]
  have hm : (m : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, zero_mul]
  have hN : Algebra.norm ℚ y = (m : ℚ) ^ d * (Algebra.norm ℤ r : ℚ) := by
    rw [hyr, map_mul, Algebra.coe_norm_int]
    congr 1
    rw [show ((m : F)) = algebraMap ℚ F (m : ℚ) by simp, Algebra.norm_algebraMap]
  have hr0 : (Algebra.norm ℤ r : ℚ) ≠ 0 := by
    rw [Algebra.coe_norm_int]; exact (Algebra.norm_ne_zero_iff).2 hr
  have hr1 : (1 : ℝ) ≤ |((Algebra.norm ℤ r : ℤ) : ℝ)| := by
    have : Algebra.norm ℤ r ≠ 0 := by exact_mod_cast hr0
    exact_mod_cast Int.one_le_abs this
  have hlow : (m : ℝ) ^ d ≤ |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
    rw [hN]; push_cast
    rw [abs_mul, abs_pow, Nat.abs_cast]
    nlinarith [pow_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) d]
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have hup : |((Algebra.norm ℚ y : ℚ) : ℝ)| ≤ 4 ^ d := by
    have h1 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ y)‖ = |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
      simp
    rw [← h1, hprod, norm_prod]
    calc ∏ σ : F →ₐ[ℚ] ℂ, ‖σ y‖ ≤ ∏ _σ : F →ₐ[ℚ] ℂ, (4 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => hφ σ.toRingHom)
      _ = 4 ^ d := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card]
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have : (m : ℝ) ≤ 4 := (pow_le_pow_iff_left₀ (Nat.cast_nonneg m) (by norm_num) hd0).1 (hlow.trans hup)
  exact_mod_cast this

end GlobalTheory
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_le_four_of_dvd_of_embeddings_le_four' : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ) (r : 𝓞 F), y ≠ 0 → y = m * r →
    (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4) → m ≤ 4 := by
  atlas_forward_decl GlobalTheory.nat_le_four_of_dvd_of_embeddings_le_four
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtension_conjugation_involutive_fixedField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ ∀ x, σ x = x → ∃ f : F, algebraMap F E f = x := by
  first | exact @GlobalTheory.CMConjInvol.cm_conj_invol_fixed | exact GlobalTheory.CMConjInvol.cm_conj_invol_fixed | (intros; apply GlobalTheory.CMConjInvol.cm_conj_invol_fixed <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intF_half {x : AF F} {M : ℕ} (h : 2 • x ∈ intF F (2 * M)) : x ∈ intF F M := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨c, hc, ?_⟩
  change 2 • x.2 = (2 * M) • c at e
  have h2 : IsUnit (2 : Af F) := by
    have : algebraMap F (Af F) 2 = 2 := map_ofNat _ 2
    rw [← this]
    exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
  rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul, mul_assoc, Nat.cast_ofNat] at e
  rw [nsmul_eq_mul]
  exact h2.mul_left_cancel e

theorem intF_le {x : AF F} {M : ℕ} (h : x ∈ intF F (2 * M)) : x ∈ intF F M := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨2 • c, fun v => ?_, ?_⟩
  · have : (2 • c) v = c v + c v := by rw [two_nsmul]; rfl
    rw [this]
    exact add_mem (hc v) (hc v)
  · rw [e, smul_smul, mul_comm]

theorem CE_cA (σ : E →ₐ[F] E) {N : ℕ} {z : AF F ⊗[F] E} (h : z ∈ CE F E N) : cA σ z ∈ CE F E N := by
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  exact mem_CE.2 ⟨cA σ s, cA_mem_SE σ hs, by rw [← e, map_nsmul]⟩

theorem incAF_algebraMap (y : F) :
    incAF F E (algebraMap F E y) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) := by
  show (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E y) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E)]

theorem exists_emb_ext (φ : F →+* ℂ) : ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = φ := by
  letI : Algebra F ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  exact ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, (IsAlgClosed.lift : E →ₐ[F] ℂ).comp_algebraMap⟩

theorem key (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (hM : 0 < M)
    (lam : (AF F)ˣ →* Circle) (h1 : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1)
    (hMk : ∀ b : (AF F)ˣ, (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1)
    (a : (AF F)ˣ) (ha : idFF F E a ∈ (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)) :
    lam a = 1 := by
  obtain ⟨hσσ, hfix⟩ := GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hcm
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  have htr : ∀ (N : ℕ) (x : AF F), algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E (2 * (2 * N)) → x ∈ intF F N := by
    intro N x hx
    have := GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E _ x hx
    rw [h2] at this
    exact intF_le (intF_half this)
  have hcongF : ∀ b : (AF F)ˣ, idFF F E b ∈ WE F E (8 * M) → lam b = 1 := by
    intro b hb
    have e8 : 8 * M = 2 * (2 * (2 * M)) := by ring
    refine hMk b (intF_le (htr (2 * M) _ ?_)) (intF_le (htr (2 * M) _ ?_))
    · rw [← e8, map_sub, map_one]
      exact hb.1
    · rw [← e8, map_sub, map_one]
      have := hb.2
      rwa [← map_inv] at this
  obtain ⟨y, ⟨k, rfl⟩, w, hw, hyw⟩ := Subgroup.mem_sup.1 ha
  let cU : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cA σ).toMonoidHom
  have hcW : ∀ z ∈ WE F E (8 * M), cU z ∈ WE F E (8 * M) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have := CE_cA σ hz.1
      rwa [map_sub, map_one] at this
    · have := CE_cA σ hz.2
      rw [map_sub, map_one] at this
      rw [← map_inv]
      exact this
  have hfixa : cU (idFF F E a) = idFF F E a := Units.ext ((cA σ).commutes (a : AF F))
  have hcinc : cU (Units.map (incAF F E).toMonoidHom k) =
      Units.map (incAF F E).toMonoidHom (Units.map σ.toMonoidHom k) := Units.ext rfl
  let ζ : Eˣ := Units.map σ.toMonoidHom k * k⁻¹
  have hζW : Units.map (incAF F E).toMonoidHom ζ ∈ WE F E (8 * M) := by
    have e1 := congrArg cU hyw
    rw [map_mul, hfixa, hcinc, ← hyw] at e1
    have : Units.map (incAF F E).toMonoidHom ζ = w * (cU w)⁻¹ := by
      simp only [ζ, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, e1, mul_comm]
    rw [this]
    exact mul_mem hw (inv_mem (hcW w hw))
  have hζv : (ζ : E) = σ k * (k : E)⁻¹ := by simp [ζ]
  have hζ1 : (ζ : E) = 1 := by
    by_contra hne
    set x : E := (ζ : E) - 1 with hxdef
    have hx0 : x ≠ 0 := sub_ne_zero.2 hne
    have hxC : incAF F E x ∈ CE F E (8 * M) := by
      have := hζW.1
      rw [hxdef, map_sub, map_one]
      exact this
    obtain ⟨s, hs, hsx⟩ := mem_CE.1 hxC
    have hσx : incAF F E (σ x) = cA σ (incAF F E x) := rfl
    obtain ⟨y, hy⟩ := hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])
    have hyC : algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) ∈ CE F E (2 * (2 * (16 * M * M))) := by
      rw [← incAF_algebraMap, hy, map_mul, hσx, ← hsx, map_nsmul]
      refine mem_CE.2 ⟨s * cA σ s, SE_mul hs (cA_mem_SE σ hs), ?_⟩
      simp only [nsmul_eq_mul]
      push_cast
      ring
    have hyI := htr (16 * M * M) _ hyC
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple F y (16 * M * M) (by positivity) hyI
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact mul_ne_zero hx0 ((map_ne_zero σ).2 hx0) hy.symm
    have hbound : ∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4 := by
      intro φ
      obtain ⟨τ, hτ⟩ := exists_emb_ext (E := E) φ
      have hφ : φ y = τ (algebraMap F E y) := by rw [← hτ]; rfl
      have hτσ := hcm.2.2.2 τ
      have hk0 : τ (k : E) ≠ 0 := (map_ne_zero τ).2 k.ne_zero
      have hζn : ‖τ (ζ : E)‖ = 1 := by
        rw [hζv, map_mul, map_inv₀, hτσ, norm_mul, norm_inv, norm_star]
        exact mul_inv_cancel₀ (norm_ne_zero_iff.2 hk0)
      have hxn : ‖τ x‖ ≤ 2 := by
        calc ‖τ x‖ = ‖τ (ζ : E) - 1‖ := by rw [hxdef, map_sub, map_one]
        _ ≤ ‖τ (ζ : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hζn, norm_one]; norm_num
      rw [hφ, hy, map_mul, hτσ, norm_mul, norm_star]
      nlinarith [norm_nonneg (τ x)]
    have := GlobalTheory.T.nat_le_four_of_dvd_of_embeddings_le_four' F y (16 * M * M) r hy0 hr hbound
    nlinarith
  have hk : σ k = (k : E) := by
    rw [hζv] at hζ1
    exact (mul_inv_eq_one₀ k.ne_zero).1 hζ1
  obtain ⟨f, hf⟩ := hfix k hk
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact k.ne_zero hf.symm
  let fU : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)
  have hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU := by
    apply Units.ext
    show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)
    rw [← hf, incAF_algebraMap]
  have hw' : w = idFF F E (fU⁻¹ * a) := by
    rw [map_mul, map_inv, ← hinc, ← hyw]
    group
  have hb := hcongF (fU⁻¹ * a) (hw' ▸ hw)
  have hfU : lam fU = 1 := h1 (Units.mk0 f hf0)
  have : a = fU * (fU⁻¹ * a) := by group
  rw [this, map_mul, hfU, hb, mul_one]

theorem exists_extend_hecke : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  intro F E _ _ _ _ _ σ B hB lam hc h1 hinf
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨M, hM, hMk⟩ := GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity F lam hc hinf
  let V : Subgroup (AF F ⊗[F] E)ˣ := (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)
  have hkey : ∀ a : (AF F)ˣ, idFF F E a ∈ V → lam a = 1 := key σ hB.cm M hM lam h1 hMk
  have hN : 0 < 8 * M := by positivity
  have hWo : IsOpen (WE F E (8 * M) : Set (AF F ⊗[F] E)ˣ) := by
    have ho := GlobalTheory.T.isOpen_integralTensorAdeleMultiples F E (8 * M) hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hVo : IsOpen (V : Set (AF F ⊗[F] E)ˣ) := Subgroup.isOpen_mono le_sup_right hWo

  let ψ0 : (AF F)ˣ →* (AF F ⊗[F] E)ˣ ⧸ V := (QuotientGroup.mk' V).comp (idFF F E)
  have hker : ψ0.ker ≤ lam.ker := fun a ha => hkey a ((QuotientGroup.eq_one_iff _).1 ha)
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective u.toMul
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    show Additive.ofMul (Circle.exp (t / n) ^ n) = u
    rw [← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]
    rfl
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0)
    (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker lam hker))
  let κ : (AF F ⊗[F] E)ˣ ⧸ V →* Circle := MonoidHom.toAdditive.symm ρ
  have hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker lam hker x :=
    fun x => DFunLike.congr_fun hρ (Additive.ofMul x)
  have hV1 : ∀ z ∈ V, κ.comp (QuotientGroup.mk' V) z = 1 := fun z hz => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  refine ⟨κ.comp (QuotientGroup.mk' V), ⟨?_, fun x => hV1 _ (le_sup_left (a := (Units.map (incAF F E).toMonoidHom).range)
    ⟨x, rfl⟩)⟩, fun z hz => hV1 z (le_sup_right (a := (Units.map (incAF F E).toMonoidHom).range) ?_), fun a => hκ (a : (AF F)ˣ ⧸ ψ0.ker)⟩
  · refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hVo.mem_nhds (one_mem V)] with z hz
    exact (hV1 z hz).symm
  · have hN' := hN
    refine ⟨GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ hz, GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ ?_⟩
    intro u hu
    have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]

end GlobalTheory.HeckeExtend

end
end
