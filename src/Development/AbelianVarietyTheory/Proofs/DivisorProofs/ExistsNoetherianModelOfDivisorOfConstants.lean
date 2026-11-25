module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIndEtaleIsDomainIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianNormalLocalApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnitsNoeth

open GlobalTheory.NormalApprox

theorem essFiniteType_loc {T : Type} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (S : Finset T) :
    Algebra.EssFiniteType ℤ (loc S) := by
  haveI : Module.Finite (gen S) (integralClosure (gen S) (FractionRing (gen S))) :=
    GlobalTheory.finite_integralClosure_of_essFiniteType_int (gen S)
  haveI : Algebra.EssFiniteType ℤ (gen S) := Algebra.EssFiniteType.of_finiteType ℤ _
  haveI : Algebra.EssFiniteType (gen S) (integralClosure (gen S) (FractionRing (gen S))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  set_option synthInstance.maxHeartbeats 200000 in
    haveI h1 : Algebra.EssFiniteType ℤ (integralClosure (gen S) (FractionRing (gen S))) :=
      Algebra.EssFiniteType.comp ℤ (gen S) _
  have h2 : (algebraMap ℤ (norm S)).EssFiniteType := by
    have e : algebraMap ℤ (norm S) =
        (normEquiv S).symm.toRingHom.comp (algebraMap ℤ (integralClosure (gen S) (FractionRing (gen S)))) :=
      RingHom.ext_int _ _
    rw [e]
    exact RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.2 h1)
      (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_surjective (normEquiv S).symm.toRingHom (normEquiv S).symm.surjective))
  haveI : Algebra.EssFiniteType ℤ (norm S) := RingHom.essFiniteType_algebraMap.1 h2
  haveI := loc_isLocalization S
  haveI : Algebra.EssFiniteType (norm S) (loc S) := Algebra.EssFiniteType.of_isLocalization _ (unitsIn S)
  exact Algebra.EssFiniteType.comp ℤ (norm S) (loc S)

end GlobalTheory.VertUnitsNoeth

namespace GlobalTheory.VertUnitsNoeth

open GlobalTheory.NormalApprox TensorProduct

end GlobalTheory.VertUnitsNoeth

namespace GlobalTheory.VertUnitsNoeth

open GlobalTheory.NormalApprox

theorem mem_originIdeal_iff' {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal T ≤ (maximalIdeal T).comap (Polynomial.constantCoeff (R := T)) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simpa using ha
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
    have := hle hf
    simpa [Polynomial.coeff_zero_eq_eval_zero] using this
  · intro hf
    have h1 : Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
    have h2 : f - Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_sub_C))
    simpa using Ideal.add_mem _ h1 h2

theorem comap_originIdeal' (A T : Type) [CommRing A] [IsLocalRing A] [CommRing T] [IsLocalRing T]
    (i : A →+* T) [IsLocalHom i] :
    (GlobalTheory.KeyOriginCut.originIdeal T).comap (Polynomial.mapRingHom i) = GlobalTheory.KeyOriginCut.originIdeal A := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff', mem_originIdeal_iff', Polynomial.coe_mapRingHom,
    Polynomial.coeff_map, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_map_iff]

theorem isIntegrallyClosed_of_absIntClosed' (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsIntegrallyClosed T := by
  apply _root_.GlobalTheory.LocIndEtale.isIntegrallyClosed_of_forall_monic_root <;> assumption

end GlobalTheory.VertUnitsNoeth
