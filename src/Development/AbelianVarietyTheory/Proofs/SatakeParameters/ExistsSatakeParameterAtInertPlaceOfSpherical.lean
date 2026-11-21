import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorPreservesLevelInvariants

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_element_decompose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) (c : GAf L n), NG.Cong L n N c → ∃ a b : GAf L n, c = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
  first | exact @GlobalTheory.CongSplit.decomp | exact GlobalTheory.CongSplit.decomp | (intros; apply GlobalTheory.CongSplit.decomp <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

namespace GlobalTheory.HeckeStab

theorem heckeFunI_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ (GAf L n → W)), (∀ g, ∀ f ∈ S, NG.rt L n g f ∈ S) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ f ∈ S, heckeFunI L n U Dv h f ∈ S := by
  classical
  intro L _ _ _ n v w Dv U hUv W _ _ S hS h hh f hf
  have hfin : Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧
      Dv.hval h (Dv.loc x) ≠ 0} :=
    GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram) (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) U hUv h hh
  have key : heckeFunI L n U Dv h f = ∑ c ∈ hfin.toFinset,
      (if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        Dv.hval h (Dv.loc hc.choose) else 0) •
      NG.rt L n (if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        hc.choose else 1) f := by
    funext g
    unfold heckeFunI
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · simp only [dif_pos hc]
        rfl
      · simp only [dif_neg hc, zero_smul]
        rfl
    · intro c hc0
      rw [Function.mem_support] at hc0
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · rw [dif_pos hc] at hc0
        rw [Set.Finite.coe_toFinset]
        refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
        rw [h0, zero_smul]
      · exact absurd (dif_neg hc) hc0
  rw [key]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hS _ f hf)

end GlobalTheory.HeckeStab
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_preserves_rightTranslationStable : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ (GAf L n → W)), (∀ g, ∀ f ∈ S, NG.rt L n g f ∈ S) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ f ∈ S, heckeFunI L n U Dv h f ∈ S := by
  atlas_forward_decl GlobalTheory.HeckeStab.heckeFunI_mem
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_preserves_levelInvariants : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ u ∈ U, ∃ a b : GAf L n, u = a * b ∧ a ∈ U ∧ TrivOutside {v} a ∧ b ∈ U ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ κ ∈ U, NG.rt L n κ (heckeFunI L n U Dv h f) = heckeFunI L n U Dv h f := by
  first | exact @GlobalTheory.heckeFunI_rt_invariant | exact GlobalTheory.heckeFunI_rt_invariant | (intros; apply GlobalTheory.heckeFunI_rt_invariant <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

namespace GlobalTheory.InertLocUnitary

open TensorProduct

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : ReciprocityTheory.Aut.AL L) :
    ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L a) =
      Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
        (ReciprocityTheory.Aut.compAt L v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [ReciprocityTheory.Aut.compAt, ReciprocityTheory.Aut.conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem loc_mem_GU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ GU Dv.σw n := by
  set ψ : ReciprocityTheory.Aut.AL L →+* w.adicCompletion L :=
    (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L).comp
      (ReciprocityTheory.Aut.compAt L v) with hψ
  have hcomm : ∀ a, Dv.σw (ψ a) = ψ (ReciprocityTheory.Aut.conjAL L a) := by
    intro a
    simp only [hψ, RingHom.comp_apply, RingHom.coe_coe]
    rw [compAt_conjAL, Dv.comm]
  set M : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (x.1 : GL (Fin n) (ReciprocityTheory.Aut.AL L)).val with hM
  have hx : M * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M = 1 := x.2
  set X : Matrix (Fin n) (Fin n) (w.adicCompletion L) := M.map ψ with hX
  have hXval : ((Formalism.UG.bc (n := Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (ReciprocityTheory.Aut.compAt L v) (x : GL (Fin n) (ReciprocityTheory.Aut.AL L))) :
        GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = X := by
    ext i j; rfl
  have hcTX : Formalism.UG.cT Dv.σw X = (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M).map ψ := by
    ext i j
    simp [Formalism.UG.cT, ReciprocityTheory.Aut.conjT, hX, hcomm]
  have hXX : X * Formalism.UG.cT Dv.σw X = 1 := by
    rw [hcTX, hX, ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have hXX' : Formalism.UG.cT Dv.σw X * X = 1 := mul_eq_one_comm.mp hXX
  set P : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : GL (Fin n) (w.adicCompletion L)).val with hP
  set Q : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)).val with hQ
  have hPQ : P * Q = 1 := by rw [hP, hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJ : Formalism.UG.cT Dv.σw P * P = Formalism.UG.antiJ (w.adicCompletion L) n := Dv.Panti
  show Formalism.UG.cT Dv.σw (((Dv.loc x : GL (Fin n) _)) : Matrix _ _ _) * Formalism.UG.antiJ (w.adicCompletion L) n *
      ((Dv.loc x : GL (Fin n) _) : Matrix _ _ _) = Formalism.UG.antiJ (w.adicCompletion L) n
  have hloc : ((Dv.loc x : GL (Fin n) _) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = Q * X * P := by
    simp only [InertDatum.loc, Units.val_mul, hXval, hQ, hP]
  have cQP : Formalism.UG.cT Dv.σw Q * Formalism.UG.cT Dv.σw P = 1 := by
    rw [← Formalism.UG.cT_mul, hPQ, Formalism.UG.cT_one]
  rw [hloc, ← hJ, Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = Formalism.UG.cT Dv.σw P * Formalism.UG.cT Dv.σw X * (Formalism.UG.cT Dv.σw Q * Formalism.UG.cT Dv.σw P) * (P * Q) * X * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv.σw P * P := by
        rw [cQP, hPQ, Matrix.mul_one, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (Formalism.UG.cT Dv.σw X), hXX', Matrix.one_mul]

end GlobalTheory.InertLocUnitary

theorem GlobalTheory.InertLocUnitary.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n :=
  fun L _ _ _ n v w Dv x => GlobalTheory.InertLocUnitary.loc_mem_GU L n v w Dv x
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLocal_mem_localUnitaryGroup : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n := by
  atlas_forward_decl GlobalTheory.InertLocUnitary.main
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct

namespace GlobalTheory.InertUmaxInt

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

omit [IsCMField L] in

theorem compAt_mem_tensInt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {x : AL L}
    (hx : x ∈ ALint L) :
    compAt L v x ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, GlobalTheory.InertUmax.compAt_tmul]
      exact Subring.subset_closure (Or.inl ⟨⟨(y : L), y, rfl⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, GlobalTheory.InertUmax.compAt_tmul]
      exact Subring.subset_closure (Or.inr ⟨⟨a v, ha v⟩, rfl⟩)
  exact key hx

end GlobalTheory.InertUmaxInt

open GlobalTheory.InertUmaxInt in

theorem GlobalTheory.InertUmaxInt.loc_integral_of_mem_Umax : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ u : GAf L n, u ∈ Umax L n → ∀ i j, ((Dv.loc u : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L) := by
  intro L _ _ _ n v w Dv u hu i j
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have he : ∀ k l, Dv.e (compAt L v ((u.1 : Matrix (Fin n) (Fin n) (AL L)) k l)) ∈
      intL (w.adicCompletion L) := fun k l =>
    (Dv.integ _).1 (compAt_mem_tensInt L v (hu k l))
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (he l k)) (hP k j)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLocal_integral_of_mem_latticeStabilizer : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ u : GAf L n, u ∈ Umax L n → ∀ i j, ((Dv.loc u : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L) := by
  atlas_forward_decl GlobalTheory.InertUmaxInt.loc_integral_of_mem_Umax
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section
open TensorProduct

namespace GlobalTheory.InertLocSurj

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem compAt_conjAL (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [conjAL, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.map_tmul,
      GlobalTheory.InertUmax.compAt_tmul, Formalism.UG.sigR, AlgHom.coe_id, id_eq]
  | add a b ha hb => simp only [map_add]; rw [ha, hb]

theorem exists_supported (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (t : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ T : AL L, compAt L v T = t ∧ ∀ u, u ≠ v → compAt L u T = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, rfl⟩ := GlobalTheory.InertUmax.tensor_decomp b t
  refine ⟨b 0 ⊗ₜ GlobalTheory.InertUmax.sgl L v a + b 1 ⊗ₜ GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same]
  · intro u hu
    rw [map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

theorem exists_trivOutside_loc_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w), ∀ y : GL (Fin n) (w.adicCompletion L), y ∈ GU Dv.σw n →
    ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  intro L _ _ _ n v w Dv y hy
  classical
  have hy' : Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      Formalism.UG.antiJ (w.adicCompletion L) n := hy
  let Z : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((Dv.P * y * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)
  have hPP : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hZ : Formalism.UG.cT Dv.σw Z * Z = 1 := by
    simp only [Z, Units.val_mul, Formalism.UG.cT_mul]
    have h1 := Dv.Panti
    calc Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) _) * Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P : Matrix (Fin n) (Fin n) _) * (y : Matrix (Fin n) (Fin n) _) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _))
        = Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) _) *
            (Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _) * (Dv.P : Matrix (Fin n) (Fin n) _)) *
            (y : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _) * (Dv.P : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) := by
          rw [h1, hy']
      _ = Formalism.UG.cT Dv.σw ((Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P : Matrix (Fin n) (Fin n) _) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPP, Formalism.UG.cT_one, Matrix.one_mul]
  have hZ' : Z * Formalism.UG.cT Dv.σw Z = 1 := mul_eq_one_comm.mp hZ
  set sg := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (v.adicCompletion (maximalRealSubfield L)) with hsg
  let Xv : Matrix (Fin n) (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
    Z.map Dv.e.symm
  have hXZ : Xv.map Dv.e = Z := by ext i j; simp [Xv]
  have hX : Xv * conjT sg Xv = 1 := by
    have hcomm : ∀ z, Dv.e.symm (Dv.σw z) = sg (Dv.e.symm z) := by
      intro z
      apply Dv.e.injective
      rw [RingEquiv.apply_symm_apply, Dv.comm, RingEquiv.apply_symm_apply]
    have h2 := congrArg (fun M => M.map Dv.e.symm) hZ'
    simp only [Matrix.map_mul] at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at h2
    convert h2 using 2
    ext i j
    simp [conjT, Formalism.UG.cT, Xv, hcomm]
  choose T hTv hTu using GlobalTheory.InertLocSurj.exists_supported (L := L) v
  obtain ⟨E, hEv, hEu⟩ := GlobalTheory.InertLocSurj.exists_supported (L := L) v 1
  let A : Matrix (Fin n) (Fin n) (AL L) := fun i j => T (Xv i j) + if i = j then 1 - E else 0
  have hAv : A.map (compAt L v) = Xv := by
    ext i j
    show compAt L v (T (Xv i j) + if i = j then 1 - E else 0) = Xv i j
    by_cases h : i = j
    · rw [if_pos h, map_add, hTv, map_sub, map_one, hEv, sub_self, add_zero]
    · rw [if_neg h, map_add, hTv, map_zero, add_zero]
  have hAu : ∀ u, u ≠ v → A.map (compAt L u) = 1 := by
    intro u hu
    ext i j
    show compAt L u (T (Xv i j) + if i = j then 1 - E else 0) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [Matrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, map_add, hTu _ u hu, map_sub, map_one, hEu u hu, zero_add, sub_zero]
    · rw [if_neg h, if_neg h, map_add, hTu _ u hu, map_zero, add_zero]
  have hmap : ∀ u, (A * conjT (conjAL L) A).map (compAt L u) =
      A.map (compAt L u) * conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
        (u.adicCompletion (maximalRealSubfield L))) (A.map (compAt L u)) := by
    intro u
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp [conjT, GlobalTheory.InertLocSurj.compAt_conjAL]
  have hA : A * conjT (conjAL L) A = 1 := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.InertUmax.eq_zero_of_compAt
    intro u
    have h3 : (A * conjT (conjAL L) A).map (compAt L u) = (1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L u) := by
      rw [hmap, Matrix.map_one _ (map_zero _) (map_one _)]
      rcases eq_or_ne u v with rfl | hu
      · rw [hAv]; exact hX
      · rw [hAu u hu, conjT_one, Matrix.one_mul]
    have h4 := congrFun (congrFun h3 i) j
    simp only [Matrix.map_apply] at h4
    rw [map_sub, h4, sub_self]
  let g : GL (Fin n) (AL L) := ⟨A, conjT (conjAL L) A, hA, mul_eq_one_comm.mp hA⟩
  have hg : g ∈ GA L n := hA
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro u hu
    exact hAu u (by simpa using hu)
  · have hbc : Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) g) = Dv.P * y * Dv.P⁻¹ := by
      apply Units.ext
      show (A.map (compAt L v)).map Dv.e = Z
      rw [hAv, hXZ]
    unfold InertDatum.loc
    show Dv.P⁻¹ * Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) g) * Dv.P = y
    rw [hbc]
    group

end GlobalTheory.InertLocSurj
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trivOutside_inertLocal_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ y : GL (Fin n) (w.adicCompletion L), y ∈ GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  atlas_forward_decl GlobalTheory.InertLocSurj.exists_trivOutside_loc_eq
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open GlobalTheory.SatInd

namespace GlobalTheory.InertConv

theorem eq_of_coset {G : Type} [Group G] {K : Subgroup G} {k : Type} {H : G → k}
    (hH : ∀ (a : G) (c : K), H (a * c) = H a) {a b : G} (hab : (a : G ⧸ K) = b) : H a = H b := by
  have hc := QuotientGroup.eq.1 hab
  have := hH a ⟨a⁻¹ * b, hc⟩
  change H (a * (a⁻¹ * b)) = H a at this
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem finsum_eq_of_support_subset_range {α β M : Type} [AddCommMonoid M] {F : α → M} {e : β → α}
    (he : Function.Injective e) (hs : Function.support F ⊆ Set.range e) :
    ∑ᶠ c, F c = ∑ᶠ d, F (e d) := by
  rw [← finsum_mem_range he, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem conv_of (Dv : InertDatum L n v w) (U : Subgroup (GAf L n))
    (hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n))
    (hA : ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n)
    (hE : ∀ u ∈ Umax L n, ∀ i j, ((Dv.loc u : GL (Fin n) (w.adicCompletion L)) :
      Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L))
    (hC : ∀ y ∈ GU Dv.σw n, ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y)
    (W : Type) [AddCommGroup W] [Module ℂ W]
    (h : GU Dv.σw n → ℂ) (hh : h ∈ Hecke ℂ (KU Dv.σw n))
    (h' : GU Dv.σw n → ℂ) (hh' : h' ∈ Hecke ℂ (KU Dv.σw n))
    (f : GAf L n → W) (hf : ∀ κ ∈ U, NG.rt L n κ f = f) :
    heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f =
      heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  classical
  set K := KU Dv.σw n with hKdef
  let lam : GAf L n →* GU Dv.σw n := MonoidHom.codRestrict (GlobalTheory.SatInd.CosetFin.locHom Dv) _ hA
  have hlam : ∀ x, ((lam x : GU Dv.σw n) : GL (Fin n) (w.adicCompletion L)) = Dv.loc x := fun _ => rfl
  have hK1 : ∀ u ∈ Umax L n, lam u ∈ K := by
    intro u hu
    refine GlobalTheory.SatInd.DCoset.mem_KU_of_entries (lam u) (fun i j => hE u hu i j) (fun i j => ?_)
    rw [← map_inv]
    exact hE u⁻¹ (inv_mem hu) i j
  have hR : ∀ x x' : GAf L n, TrivOutside {v} x → TrivOutside {v} x' →
      ((x : GAf L n ⧸ U) = x' ↔ ((lam x : GU Dv.σw n ⧸ K) = lam x')) := by
    intro x x' hx hx'
    have ht : TrivOutside {v} (x⁻¹ * x') :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv hx) hx'
    rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]
    constructor
    · intro hu; exact hK1 _ ((hU _ ht).1 hu)
    · intro hk
      exact (hU _ ht).2 (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv _ ht fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j)
  have hCs : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, TrivOutside {v} x ∧ lam x = d.out := fun d => by
    obtain ⟨x, hx, e⟩ := hC _ d.out.2
    exact ⟨x, hx, Subtype.ext e⟩
  choose s hs1 hs2 using hCs
  have heT : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, (x : GAf L n ⧸ U) = (s d : GAf L n ⧸ U) ∧
      TrivOutside {v} x := fun d => ⟨s d, rfl, hs1 d⟩
  have hρ1 : ∀ d, TrivOutside {v} (heT d).choose := fun d => (heT d).choose_spec.2
  have hρ2 : ∀ d, ((lam (heT d).choose : GU Dv.σw n) : GU Dv.σw n ⧸ K) = d := fun d => by
    rw [(hR _ _ (hρ1 d) (hs1 d)).1 (heT d).choose_spec.1, hs2 d, QuotientGroup.out_eq']
  have he : Function.Injective (fun d : GU Dv.σw n ⧸ K => ((s d : GAf L n) : GAf L n ⧸ U)) := by
    intro d d' hdd
    have := (hR _ _ (hs1 d) (hs1 d')).1 hdd
    rwa [hs2, hs2, QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

  have step2 : ∀ (H : GU Dv.σw n → ℂ), (∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a) →
      ∀ (F : GAf L n → W) (g : GAf L n),
      heckeFunI L n U Dv H F g = ∑ᶠ d : GU Dv.σw n ⧸ K, H d.out • F (g * (heT d).choose) := by
    intro H hH F g
    show (∑ᶠ c : GAf L n ⧸ U, _) = _
    rw [finsum_eq_of_support_subset_range he]
    · refine finsum_congr fun d => ?_
      rw [dif_pos (heT d)]
      have hv : Dv.hval H (Dv.loc (heT d).choose) = H d.out := by
        rw [InertDatum.hval, dif_pos (hA _)]
        exact eq_of_coset hH (by rw [QuotientGroup.out_eq']; exact hρ2 d)
      rw [hv]
    · intro c hc
      rw [Function.mem_support] at hc
      by_cases hT : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · obtain ⟨x, hxc, hx⟩ := hT
        refine ⟨(lam x : GU Dv.σw n ⧸ K), ?_⟩
        show ((s _ : GAf L n) : GAf L n ⧸ U) = c
        rw [← hxc]
        refine (hR _ _ (hs1 _) hx).2 ?_
        rw [hs2, QuotientGroup.out_eq']
      · rw [dif_neg hT] at hc
        exact absurd rfl hc

  have hRi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a :=
    fun H hH a c => by simpa using hH.1 1 c a
  have hLi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (c : K) (a : GU Dv.σw n), H (c * a) = H a :=
    fun H hH c a => by simpa using hH.1 c 1 a
  have hconvR : ∀ (a : GU Dv.σw n) (c : K), conv K h h' (a * c) = conv K h h' a := by
    intro a c
    simp only [Formalism.UG.conv]
    refine finsum_congr fun x => ?_
    rw [← mul_assoc, hRi h' hh']
  have hfin : ∀ H ∈ Hecke ℂ K, Set.Finite {d : GU Dv.σw n ⧸ K | H d.out ≠ 0} := by
    rintro H ⟨-, S, hS⟩
    refine (S.finite_toSet.biUnion fun t _ => GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram t).subset ?_
    intro d hd
    obtain ⟨t, ht, a, b, hab⟩ := hS _ hd
    refine Set.mem_biUnion ht ⟨(a : GU Dv.σw n), a.2, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' d]
    rw [hab]
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  have hfU : ∀ a b : GAf L n, (a : GAf L n ⧸ U) = b → ∀ g, f (g * a) = f (g * b) := by
    intro a b hab g
    have hu := QuotientGroup.eq.1 hab
    have : f (g * a * (a⁻¹ * b)) = f (g * a) := congrFun (hf _ hu) (g * a)
    rw [← this, mul_assoc, mul_inv_cancel_left]
  funext g
  rw [step2 _ hconvR f g, step2 h (hRi h hh) _ g]
  have inner : ∀ d : GU Dv.σw n ⧸ K,
      heckeFunI L n U Dv h' f (g * (heT d).choose) =
        ∑ᶠ e : GU Dv.σw n ⧸ K, h' (d.out⁻¹ * e.out) • f (g * (heT e).choose) := by
    intro d
    rw [step2 h' (hRi h' hh') f]
    set x := lam (heT d).choose with hx
    have hk : x⁻¹ * d.out ∈ K := QuotientGroup.eq.1 (by rw [QuotientGroup.out_eq']; exact hρ2 d)
    have hL : ∀ y, h' (d.out⁻¹ * y) = h' (x⁻¹ * y) := by
      intro y
      have := hLi h' hh' ⟨(x⁻¹ * d.out)⁻¹, inv_mem hk⟩ (x⁻¹ * y)
      rw [← this]
      congr 1
      show _ = (x⁻¹ * d.out)⁻¹ * (x⁻¹ * y)
      group
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (GU Dv.σw n ⧸ K)))
    refine finsum_congr fun e => ?_
    simp only [MulAction.toPerm_apply]
    congr 1
    · rw [hL]
      refine eq_of_coset (hRi h' hh') ?_
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq',
        inv_smul_smul]
    · rw [mul_assoc]
      refine hfU _ _ ((hR _ _ (GlobalTheory.SatInd.CosetFin.trivOutside_mul (hρ1 d) (hρ1 e)) (hρ1 _)).2 ?_) g
      rw [map_mul, hρ2, ← hx, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, hρ2]
  rw [finsum_congr fun d => congrArg (h d.out • ·) (inner d)]
  have hSe : Set.Finite (⋃ (d : GU Dv.σw n ⧸ K) (_ : d ∈ {d : GU Dv.σw n ⧸ K | h d.out ≠ 0}),
      (fun c : GU Dv.σw n ⧸ K => (d.out • c : GU Dv.σw n ⧸ K)) '' {c : GU Dv.σw n ⧸ K | h' c.out ≠ 0}) :=
    (hfin h hh).biUnion fun d _ => (hfin h' hh').image _
  have hmem : ∀ d e : GU Dv.σw n ⧸ K, h d.out ≠ 0 → h' (d.out⁻¹ * e.out) ≠ 0 →
      e ∈ hSe.toFinset := by
    intro d e hd he'
    rw [Set.Finite.mem_toFinset]
    refine Set.mem_biUnion hd ⟨d.out⁻¹ • e, ?_, smul_inv_smul d.out e⟩
    have hc : (((d.out⁻¹ • e).out : GU Dv.σw n) : GU Dv.σw n ⧸ K) = ↑(d.out⁻¹ * e.out) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    show h' (d.out⁻¹ • e).out ≠ 0
    rw [eq_of_coset (hRi h' hh') hc]
    exact he'
  have hL1 : (∑ᶠ e : GU Dv.σw n ⧸ K, conv K h h' e.out • f (g * (heT e).choose)) =
      ∑ e ∈ hSe.toFinset, (∑ d ∈ (hfin h hh).toFinset, h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_]
    · refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      show (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out)) = _
      apply finsum_eq_sum_of_support_subset
      intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact left_ne_zero_of_mul hd
    · intro e he
      rw [Function.mem_support] at he
      have h1 : conv K h h' e.out ≠ 0 := fun h0 => he (by rw [h0, zero_smul])
      obtain ⟨d, hd⟩ : ∃ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact h1 (finsum_eq_zero_of_forall_eq_zero hcon)
      exact hmem d e (left_ne_zero_of_mul hd) (right_ne_zero_of_mul hd)
  have hR1 : (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out • ∑ᶠ e : GU Dv.σw n ⧸ K,
      h' (d.out⁻¹ * e.out) • f (g * (heT e).choose)) =
      ∑ d ∈ (hfin h hh).toFinset, ∑ e ∈ hSe.toFinset, (h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := (hfin h hh).toFinset) ?_]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [Set.Finite.mem_toFinset] at hd
      rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_, Finset.smul_sum]
      · exact Finset.sum_congr rfl fun e _ => by rw [mul_smul]
      · intro e he
        rw [Function.mem_support] at he
        exact hmem d e hd (fun h0 => he (by rw [h0, zero_smul]))
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hd (by rw [h0, zero_smul])
  rw [hL1, hR1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_smul]

theorem heckeFunI_conv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ h' ∈ Hecke ℂ (KU Dv.σw n), ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f = heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  intro L _ _ _ n v w Dv U hU W _ _ h hh h' hh' f hf
  exact conv_of Dv U hU (GlobalTheory.T.inertLocal_mem_localUnitaryGroup L n v w Dv) (GlobalTheory.T.inertLocal_integral_of_mem_latticeStabilizer L n v w Dv) (GlobalTheory.T.exists_trivOutside_inertLocal_eq L n v w Dv)
    W h hh h' hh' f hf

end GlobalTheory.InertConv
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ h' ∈ Hecke ℂ (KU Dv.σw n), ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f = heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  atlas_forward_decl GlobalTheory.InertConv.heckeFunI_conv
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct Formalism.UG

namespace GlobalTheory.OneAct

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem compAt_conjAL (z : AL L) :
    compAt L v (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (v.adicCompletion (maximalRealSubfield L)) (compAt L v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem compAt_mem_tensInt {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      exact ⟨⟨(y : L), y, rfl⟩, by rw [GlobalTheory.InertUmax.compAt_tmul]; rfl⟩
    · apply Subring.subset_closure
      right
      exact ⟨⟨a v, ha v⟩, by rw [GlobalTheory.InertUmax.compAt_tmul]⟩
  exact key hz

theorem loc_mem_GU (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ GU Dv.σw n := by
  set φ : AL L →+* w.adicCompletion L := (Dv.e : _ →+* _).comp (compAt L v) with hφdef
  have hφ : ∀ z, φ (conjAL L z) = Dv.σw (φ z) := fun z => by
    simp only [φ, RingHom.comp_apply, compAt_conjAL]
    exact Dv.comm _
  have hX : ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have hX' := mul_eq_one_comm.mp hX
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map φ with hAdef
  have hA : cT Dv.σw A * A = 1 := by
    have : cT Dv.σw A = (conjT (conjAL L) ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map φ := by
      ext i j; simp [cT, conjT, A, hφ]
    rw [this, ← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]
  have hloc : ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * A *
        (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := rfl
  have hPP : cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have hPP' : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 :=
    Units.mul_inv _
  show cT Dv.σw ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      antiJ (w.adicCompletion L) n *
      ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      antiJ (w.adicCompletion L) n
  rw [← Dv.Panti, hloc, cT_mul, cT_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT Dv.σw _) (cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))), hPP,
    Matrix.one_mul, ← Matrix.mul_assoc (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)), hPP',
    Matrix.one_mul, ← Matrix.mul_assoc (cT Dv.σw A) A, hA, Matrix.one_mul]

theorem mem_range_of_int {K : Type} [Field K] (S : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h1 i j⟩
  let N : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h2 i j⟩
  have hM : M.map S.subtype = (g : Matrix (Fin n) (Fin n) K) := by ext i j; rfl
  have hN : N.map S.subtype = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by ext i j; rfl
  have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) S => A.map S.subtype) := by
    intro A B h; ext i j; exact congrFun (congrFun h i) j
  have hMN : M * N = 1 := inj (by
    simp only [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hNM : N * M = 1 := inj (by
    simp only [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨M, N, hMN, hNM⟩, Units.ext ?_⟩
  exact hM

theorem loc_entries_int (Dv : InertDatum L n v w) {x : GAf L n} (hx : x ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈
      intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hA : ∀ k l, Dv.e (compAt L v (((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) k l)) ∈
      intL (w.adicCompletion L) := fun k l => (Dv.integ _).1 (compAt_mem_tensInt (hx k l))
  simp only [InertDatum.loc, Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hA l k)) (hP k j)

theorem loc_mem_KU (Dv : InertDatum L n v w) {x : GAf L n} (hx : x ∈ Umax L n) :
    (⟨Dv.loc x, loc_mem_GU Dv x⟩ : GU Dv.σw n) ∈ KU Dv.σw n := by
  refine ⟨loc_mem_GU Dv x, mem_range_of_int _ _ (loc_entries_int Dv hx) ?_⟩
  have : (Dv.loc x)⁻¹ = Dv.loc x⁻¹ := by
    rw [show Dv.loc x⁻¹ = GlobalTheory.SatInd.CosetFin.locHom Dv x⁻¹ from rfl, map_inv]; rfl
  show ∀ i j, (((Dv.loc x)⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ _
  rw [this]
  exact loc_entries_int Dv (inv_mem hx)

end GlobalTheory.OneAct

theorem GlobalTheory.OneAct.heckeFunI_unit : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (dosetInd ℂ (KU Dv.σw n) 1) f = f := by
  intro L _ _ _ n v w Dv U hU W _ _ f hf
  funext g
  unfold heckeFunI
  have hone : TrivOutside {v} (1 : GAf L n) := by
    intro u _
    show ((1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L u) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdK : ∀ y : GU Dv.σw n, y ∈ (DoubleCoset.doubleCoset (1 : GU Dv.σw n) (KU Dv.σw n : Set (GU Dv.σw n))
      (KU Dv.σw n : Set (GU Dv.σw n))) ↔ y ∈ KU Dv.σw n := by
    intro y
    rw [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simpa using (KU Dv.σw n).mul_mem ha hb
    · intro hy
      exact ⟨y, hy, 1, (KU Dv.σw n).one_mem, by simp⟩
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ U)]
  · have hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = ((1 : GAf L n) : GAf L n ⧸ U) ∧ TrivOutside {v} x :=
      ⟨1, rfl, hone⟩
    rw [dif_pos hc]
    obtain ⟨hx1, hx2⟩ := hc.choose_spec
    have hxU : hc.choose ∈ U := by
      have := QuotientGroup.eq.1 hx1
      simpa using this
    have hxM : hc.choose ∈ Umax L n := (hU _ hx2).1 hxU
    have hval : Dv.hval (dosetInd ℂ (KU Dv.σw n) 1) (Dv.loc hc.choose) = 1 := by
      unfold InertDatum.hval
      rw [dif_pos (GlobalTheory.OneAct.loc_mem_GU Dv _)]
      unfold dosetInd
      rw [Set.indicator_of_mem ((hdK _).2 (GlobalTheory.OneAct.loc_mem_KU Dv hxM))]
      rfl
    rw [hval, one_smul]
    exact congrFun (hf _ hxU) g
  · intro c hc1
    split_ifs with hc
    · obtain ⟨hx1, hx2⟩ := hc.choose_spec
      have hval : Dv.hval (dosetInd ℂ (KU Dv.σw n) 1) (Dv.loc hc.choose) = 0 := by
        unfold InertDatum.hval
        split_ifs with hm
        · unfold dosetInd
          apply Set.indicator_of_notMem
          intro hmem
          have hK := (hdK _).1 hmem
          have hxM : hc.choose ∈ Umax L n :=
            GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv _ hx2 (fun i j => GlobalTheory.SatInd.CosetFin.entries_int hK i j)
          apply hc1
          rw [← hx1]
          exact QuotientGroup.eq.2 (by simpa using (hU _ hx2).2 hxM)
        · rfl
      rw [hval, zero_smul]
    · rfl
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_sphericalUnit_eq_id : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (dosetInd ℂ (KU Dv.σw n) 1) f = f := by
  atlas_forward_decl GlobalTheory.OneAct.heckeFunI_unit
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

namespace GlobalTheory.InertHeckeLin

open Classical in
theorem heckeFunI_bilinear : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ h' ∈ Hecke ℂ (KU Dv.σw n), ∀ (c : ℂ) (f f' : GAf L n → W), heckeFunI L n U Dv (h + h') f = heckeFunI L n U Dv h f + heckeFunI L n U Dv h' f ∧ heckeFunI L n U Dv (c • h) f = c • heckeFunI L n U Dv h f ∧ heckeFunI L n U Dv h (f + f') = heckeFunI L n U Dv h f + heckeFunI L n U Dv h f' ∧ heckeFunI L n U Dv h (c • f) = c • heckeFunI L n U Dv h f := by
  intro L _ _ _ n v w Dv U hU W _ _ h hh h' hh' c f f'
  have hfin : ∀ k ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
      (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval k (Dv.loc x) ≠ 0} := fun k hk =>
    GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram) (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) U hU k hk
  have hsupp : ∀ k ∈ Hecke ℂ (KU Dv.σw n), ∀ (φ : GAf L n → W) (g : GAf L n),
      (Function.support (fun c : GAf L n ⧸ U =>
        if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
          Dv.hval k (Dv.loc hc.choose) • φ (g * hc.choose) else 0)).Finite := by
    intro k hk φ g
    refine (hfin k hk).subset ?_
    intro c hc
    simp only [Function.mem_support] at hc
    split_ifs at hc with h1
    · refine ⟨h1.choose, h1.choose_spec.1, h1.choose_spec.2, ?_⟩
      intro h0
      rw [h0, zero_smul] at hc
      exact hc rfl
    · exact absurd rfl hc
  have hadd : ∀ y, Dv.hval (h + h') y = Dv.hval h y + Dv.hval h' y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  have hsmul : ∀ y, Dv.hval (c • h) y = c * Dv.hval h y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h' hh' f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hadd, add_smul]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hsmul, mul_smul]
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h hh f' g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [smul_add]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs
    · exact smul_comm _ _ _
    · rw [smul_zero]

end GlobalTheory.InertHeckeLin
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_bilinear : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ h' ∈ Hecke ℂ (KU Dv.σw n), ∀ (c : ℂ) (f f' : GAf L n → W), heckeFunI L n U Dv (h + h') f = heckeFunI L n U Dv h f + heckeFunI L n U Dv h' f ∧ heckeFunI L n U Dv (c • h) f = c • heckeFunI L n U Dv h f ∧ heckeFunI L n U Dv h (f + f') = heckeFunI L n U Dv h f + heckeFunI L n U Dv h f' ∧ heckeFunI L n U Dv h (c • f) = c • heckeFunI L n U Dv h f := by
  atlas_forward_decl GlobalTheory.InertHeckeLin.heckeFunI_bilinear
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

noncomputable section

namespace GlobalTheory.SatExists

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : TrivOutside {v} (1 : GAf L n) := by
  intro v' _
  show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v') = 1
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trivOutside_mul {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {v} y) : TrivOutside {v} (x * y) := by
  intro v' hv'
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1
  rw [Units.val_mul, Matrix.map_mul, hx v' hv', hy v' hv', Matrix.one_mul]

theorem trivOutside_inv {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : GAf L n}
    (hx : TrivOutside {v} x) : TrivOutside {v} x⁻¹ := by
  intro v' hv'
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v' hv', Matrix.mul_one] at e

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  intro L _ _ _ n π v w _ hsph Dv
  obtain ⟨f₀, hf₀S, hf₀0, hf₀K⟩ := hsph
  obtain ⟨-, N, hN, hNf⟩ := π.irrS.1.le hf₀S
  let U : Subgroup (GAf L n) :=
    Subgroup.closure ({κ | NG.Cong L n N κ} ∪ {κ | κ ∈ Umax L n ∧ TrivOutside {v} κ})
  have hUmax : U ≤ Umax L n := (Subgroup.closure_le _).2 (by
    rintro κ (hκ | hκ)
    · exact hκ.1
    · exact hκ.1)
  have hUv : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n) := fun κ hκ =>
    ⟨fun h => hUmax h, fun h => Subgroup.subset_closure (Or.inr ⟨h, hκ⟩)⟩
  have hCU : ∀ κ, NG.Cong L n N κ → κ ∈ U := fun κ hκ => Subgroup.subset_closure (Or.inl hκ)
  have hf₀U : ∀ κ ∈ U, NG.rt L n κ f₀ = f₀ := by
    intro κ hκ
    induction hκ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact funext fun g => hNf x hx g
      · exact hf₀K x hx.1 hx.2
    | one => exact funext fun g => by change f₀ (g * 1) = f₀ g; rw [mul_one]
    | mul x y _ _ hx hy =>
      refine funext fun g => ?_
      change f₀ (g * (x * y)) = f₀ g
      have h1 : f₀ (g * x * y) = f₀ (g * x) := congrFun hy (g * x)
      have h2 : f₀ (g * x) = f₀ g := congrFun hx g
      rw [← mul_assoc, h1, h2]
    | inv x _ hx =>
      refine funext fun g => ?_
      change f₀ (g * x⁻¹) = f₀ g
      have h1 : f₀ (g * x⁻¹ * x) = f₀ (g * x⁻¹) := congrFun hx (g * x⁻¹)
      rw [← h1, inv_mul_cancel_right]
  have hdec : ∀ u ∈ U, ∃ a b : GAf L n, u = a * b ∧ a ∈ U ∧ TrivOutside {v} a ∧ b ∈ U ∧
      ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨a, b, e, ha, hat, hb, hc⟩ := GlobalTheory.T.congruence_element_decompose L n v N x hx
        exact ⟨a, b, e, (hUv a hat).2 ha, hat, hCU b hb, hc⟩
      · exact ⟨x, 1, (mul_one x).symm, Subgroup.subset_closure (Or.inr hx), hx.2, one_mem _,
          fun y _ => by rw [mul_one, one_mul]⟩
    | one => exact ⟨1, 1, (mul_one 1).symm, one_mem _, trivOutside_one v, one_mem _,
        fun y _ => by rw [mul_one, one_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      obtain ⟨a', b', rfl, ha', hat', hb', hbc'⟩ := hy
      refine ⟨a * a', b * b', ?_, mul_mem ha ha', trivOutside_mul hat hat', mul_mem hb hb', fun z hz => ?_⟩
      · simp only [mul_assoc]
        rw [← mul_assoc b a', ← hbc a' hat', mul_assoc]
      · rw [← mul_assoc, hbc z hz, mul_assoc, hbc' z hz, ← mul_assoc]
    | inv x _ hx =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      refine ⟨a⁻¹, b⁻¹, ?_, inv_mem ha, trivOutside_inv hat, inv_mem hb, fun z hz => ?_⟩
      · rw [mul_inv_rev, eq_mul_inv_iff_mul_eq, mul_assoc, hbc a⁻¹ (trivOutside_inv hat), inv_mul_cancel_left]
      · rw [mul_inv_eq_iff_eq_mul, mul_assoc, hbc z hz, inv_mul_cancel_left]
  let V : Submodule ℂ (GAf L n → π.W) :=
    { carrier := {f | f ∈ π.S ∧ ∀ κ ∈ U, NG.rt L n κ f = f}
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      add_mem' := fun ha hb => ⟨π.S.add_mem ha.1 hb.1, fun κ hκ => by rw [map_add, ha.2 κ hκ, hb.2 κ hκ]⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  haveI : FiniteDimensional ℂ V := by
    have := GlobalTheory.AlgFormsFin.fixedForms_finite L n π.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n π.ρ N) ?_
    rintro f ⟨hfS, hfU⟩
    exact ⟨(π.irrS.1.le hfS).1, fun κ hκ g => congrFun (hfU κ (hCU κ hκ)) g⟩
  have hf₀V : f₀ ∈ V := ⟨hf₀S, hf₀U⟩
  haveI : Nontrivial V := ⟨⟨⟨f₀, hf₀V⟩, 0, fun e => hf₀0 (congrArg Subtype.val e)⟩⟩
  let T : Hecke ℂ (KU Dv.σw n) → Module.End ℂ V := fun h =>
    { toFun := fun f => ⟨heckeFunI L n U Dv h.1 f.1,
        GlobalTheory.T.inertHeckeOperator_preserves_rightTranslationStable L n v w Dv U hUv π.W π.S π.irrS.1.stable h.1 h.2 f.1 f.2.1,
        GlobalTheory.T.inertHeckeOperator_preserves_levelInvariants L n v w Dv U hUv hdec π.W h.1 h.2 f.1 f.2.2⟩
      map_add' := fun f f' => Subtype.ext ((GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 1 f.1 f'.1).2.2.1)
      map_smul' := fun c f => Subtype.ext ((GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.2.2) }
  have hT : ∀ h (f : V), ((T h f : V) : GAf L n → π.W) = heckeFunI L n U Dv h.1 f.1 := fun _ _ => rfl
  have hcomm : ∀ a b, T a * T b = T b * T a := fun a b => LinearMap.ext fun f => Subtype.ext (by
    change heckeFunI L n U Dv a.1 (heckeFunI L n U Dv b.1 f.1) = heckeFunI L n U Dv b.1 (heckeFunI L n U Dv a.1 f.1)
    rw [← GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W a.1 a.2 b.1 b.2 f.1 f.2.2,
      ← GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W b.1 b.2 a.1 a.2 f.1 f.2.2,
      GlobalTheory.UnitarySwap.heckeCommU _ Dv.ϖ Dv.σw _ n ℂ Dv.unram a.1 a.2 b.1 b.2])
  obtain ⟨f, hf0, hμ⟩ := GlobalTheory.exists_common_eigenvector_of_commute T hcomm
  choose μ hμ using hμ
  have ev : ∀ h : Hecke ℂ (KU Dv.σw n), heckeFunI L n U Dv h.1 f.1 = μ h • f.1 := fun h =>
    congrArg Subtype.val (hμ h)
  have hf'0 : (f : GAf L n → π.W) ≠ 0 := fun e => hf0 (Subtype.ext e)
  have inj := smul_left_injective ℂ hf'0
  let l : Hecke ℂ (KU Dv.σw n) →ₗ[ℂ] ℂ :=
    { toFun := μ
      map_add' := fun h h' => inj (by
        change μ (h + h') • f.1 = (μ h + μ h') • f.1
        rw [← ev, add_smul, ← ev, ← ev]
        exact (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 1 f.1 f.1).1)
      map_smul' := fun c h => inj (by
        change μ (c • h) • f.1 = (c * μ h) • f.1
        rw [← ev, mul_smul, ← ev]
        exact (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.1) }
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq Dv.unram l
    (inj (by
      change μ _ • f.1 = (1 : ℂ) • f.1
      rw [← ev, one_smul]
      exact GlobalTheory.T.inertHeckeOperator_sphericalUnit_eq_id L n v w Dv U hUv π.W f.1 f.2.2))
    (fun h h' => inj (by
      change μ _ • f.1 = (μ h * μ h') • f.1
      rw [← ev]
      change heckeFunI L n U Dv (conv (KU Dv.σw n) h.1 h'.1) f.1 = _
      rw [GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 f.1 f.2.2, ev h',
        (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 (μ h') f.1 f.1).2.2.2, ev h, smul_smul, mul_comm]))
  refine ⟨fun i => (α i : ℂ), f.1, f.2.1, hf'0, U, f.2.2, hUv, fun h hh => ?_⟩
  rw [ev ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.SatExists
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  atlas_forward_decl GlobalTheory.SatExists.exists_satAt
end
