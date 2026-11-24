module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem adicCont_ringHom_comp_of_map_mem {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} (f : R →+* S) (hIJ : ∀ x ∈ I, f x ∈ J) {u : Γ → R}
    (hu : AdicCont I u) : AdicCont J fun g => f (u g) := by
  intro N
  have hle : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hIJ) N
  have hc := (hu N).comp (Ideal.quotientMap (J ^ N) f hle)
  convert hc using 1
  funext g
  simp [Ideal.quotientMap_mk]

theorem UpperTheory.V.Fr.alg_lift :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsModel O C 𝔪 ρ → ∀ (Q : Type) [CommRing Q] [Algebra O Q] [IsCO O Q] (p : D →ₐ[O] Q), (∀ x ∈ 𝔪, p x ∈ maximalIdeal Q) → IsLift O (ρ.map (p : D →+* Q)) := by
  intro l _ O _ _ F n C _ _ _ D _ _ _ _ 𝔪 ρ hm Q _ _ _ p hp
  have hres : ∀ c : C, res O Q (p (algebraMap C D c)) = res O C c := fun c =>
    res_map (p.comp (IsScalarTower.toAlgHom O C D)) c
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
  · exact adicCont_ringHom_comp_of_map_mem (p : D →+* Q) hp (hm.cont.1 i j)
  · exact adicCont_ringHom_comp_of_map_mem (p : D →+* Q) hp (hm.cont.2 v i)
  · obtain ⟨c, hc1, hc2⟩ := hm.dg g i
    show res O Q (p (ρ.r g i i)) = _
    rw [← hc1, hres, hc2, RingHom.id_apply]
  · obtain ⟨c, hc1, hc2⟩ := hm.psi v i g
    show res O Q (p ↑(ρ.ψ v i g)) = _
    rw [← hc1, hres, hc2, RingHom.id_apply]
  · show res O Q (p (ρ.r g i j)) = 0
    rw [res_eq_zero_iff]
    exact hp _ (hm.off g i j hij)
