import Mathlib
import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow
set_option maxSynthPendingDepth 1

noncomputable section

open WittVector Filter Topology

namespace GroundTheory.PAdicHodge

section Coordinates

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]



variable [CharP R p]


end Coordinates


namespace AInf

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p

variable (K p) in

@[instance_reducible]
def pAdicTopology : TopologicalSpace (AInf K p) :=
  (Ideal.span {(p : AInf K p)}).adicTopology

@[instance_reducible]
def teichmullerAdicTopology (ϖ : 𝒪♭) : TopologicalSpace (AInf K p) :=
  (Ideal.span {teichmuller p ϖ}).adicTopology

variable (K p) in

@[instance_reducible]
def weakTopology : TopologicalSpace (AInf K p) :=
  TopologicalSpace.induced (fun x : AInf K p => x.coeff) inferInstance

theorem mem_span_pow_iff_norm_le (ϖ x : 𝒪♭) (k : ℕ) :
    x ∈ Ideal.span {ϖ ^ k} ↔ ‖x‖ ≤ ‖ϖ‖ ^ k := by
  rw [Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, norm_pow]







theorem continuous_coeff (i : ℕ) :
    @Continuous (AInf K p) 𝒪♭ (weakTopology K p) _ fun y => y.coeff i := by
  let := weakTopology K p
  exact (continuous_apply i).comp continuous_induced_dom









omit hp [IsPerfectoidField K p] in

theorem smodEq_pow_iff {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem isAdicComplete_p : IsAdicComplete (Ideal.span {(p : AInf K p)}) (AInf K p) :=
  inferInstance





omit hp [IsPerfectoidField K p] in

theorem _root_.Ideal.continuous_of_map_le {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B]
    [RingHomClass F A B] (f : F) {I : Ideal A} {J : Ideal B} (h : I.map f ≤ J) :
    @Continuous A B I.adicTopology J.adicTopology f := by
  refine (@continuous_iff_continuousAt A B I.adicTopology J.adicTopology f).2 fun x => ?_
  change Tendsto f (@nhds A I.adicTopology x) (@nhds B J.adicTopology (f x))
  rw [(I.hasBasis_nhds_adic x).tendsto_iff (J.hasBasis_nhds_adic (f x))]
  intro n _
  refine ⟨n, trivial, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  refine ⟨f d, ?_, (map_add f x d).symm⟩
  have : f d ∈ (I.map f) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hd
  exact Ideal.pow_right_mono h n this

local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)















end AInf

end GroundTheory.PAdicHodge
