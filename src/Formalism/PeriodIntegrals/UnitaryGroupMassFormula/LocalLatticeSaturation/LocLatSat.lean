module

public import Formalism.PeriodIntegrals.LocLatSat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeSaturation.BcGSmulR
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace PI.LocLatSat.UnitaryGroupMassFormula

variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}

theorem steps {ι : Type*} [DecidableEq ι] (g : ι → (Fin n → K) →ₗ[K] K)
    (Λ : Submodule R (Fin n → K)) (hΛ : Λ.FG) {x : Fin n → S} (hx : x ∈ latG φ O Λ)
    (T : Finset ι) (h0 : ∀ i ∈ T, fP φ (g i) x = 0) :
    x ∈ latG φ O (Λ ⊓ ⨅ i ∈ T, (LinearMap.ker (g i)).restrictScalars R) := by
  induction T using Finset.induction_on with
  | empty => simpa using hx
  | @insert a T ha ih =>
    have hx' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have hfr : IsFractional R⁰ ((Λ ⊓ ⨅ i ∈ T, (LinearMap.ker (g i)).restrictScalars R).map
        ((g a).restrictScalars R)) := by
      have hfg : (Λ.map ((g a).restrictScalars R)).FG := hΛ.map _
      exact FractionalIdeal.isFractional_of_le (J := ⟨_, FractionalIdeal.isFractional_of_fg hfg⟩)
        (Submodule.map_mono inf_le_left)
    have hs := step φ O _ (g a) hfr hx' (h0 a (Finset.mem_insert_self a T))
    have e : Λ ⊓ ⨅ i ∈ insert a T, (LinearMap.ker (g i)).restrictScalars R =
        (Λ ⊓ ⨅ i ∈ T, (LinearMap.ker (g i)).restrictScalars R) ⊓
          (LinearMap.ker (g a)).restrictScalars R := by
      rw [Finset.iInf_insert]
      exact (inf_left_comm _ _ _).trans (inf_comm _ _)
    rw [e]
    exact hs

theorem sat (Λ : Submodule R (Fin n → K)) (hΛ : Λ.FG) (W : Submodule K (Fin n → K)) :
    (latG φ O (Λ ⊓ W.restrictScalars R) : Set (Fin n → S)) =
      (latG φ O Λ : Set (Fin n → S)) ∩ Submodule.span S (bcG φ '' (W : Set (Fin n → K))) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨?_, ?_⟩
    · have hle : Λ ⊓ W.restrictScalars R ≤ Λ := inf_le_left
      exact Submodule.span_mono (Set.image_mono hle) hx
    · have hle : Submodule.span O (bcG φ '' ((Λ ⊓ W.restrictScalars R : Submodule R _) : Set (Fin n → K))) ≤
          (Submodule.span S (bcG φ '' (W : Set (Fin n → K)))).restrictScalars O := by
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        exact Submodule.subset_span ⟨v, hv.2, rfl⟩
      exact hle hx
  · rintro x ⟨hxΛ, hxW⟩

    let b := Module.Basis.ofVectorSpace K W.dualAnnihilator
    haveI : Fintype (Module.Basis.ofVectorSpaceIndex K W.dualAnnihilator) := Fintype.ofFinite _
    let g : Module.Basis.ofVectorSpaceIndex K W.dualAnnihilator → (Fin n → K) →ₗ[K] K := fun i => (b i : Module.Dual K _)
    have hg : ∀ i w, w ∈ W → g i w = 0 := by
      intro i w hw
      exact (Submodule.mem_dualAnnihilator _).mp (b i).2 w hw
    have h0 : ∀ i ∈ (Finset.univ : Finset _), fP φ (g i) x = 0 := by
      intro i _
      have hle : Submodule.span S (bcG φ '' (W : Set (Fin n → K))) ≤ LinearMap.ker (fP φ (g i)) := by
        rw [Submodule.span_le]
        rintro _ ⟨w, hw, rfl⟩
        show fP φ (g i) (bcG φ w) = 0
        rw [baseChange_apply_baseChange, hg i w hw, map_zero]
      exact hle hxW
    have hs := steps φ O g Λ hΛ hxΛ Finset.univ h0
    have hle2 : Λ ⊓ ⨅ i ∈ (Finset.univ : Finset _), (LinearMap.ker (g i)).restrictScalars R ≤
        Λ ⊓ W.restrictScalars R := by
      intro v hv
      refine ⟨hv.1, ?_⟩
      have hv2 : ∀ i, (b i : Module.Dual K (Fin n → K)) v = 0 := by
        intro i
        have h := (Submodule.mem_iInf _).mp ((Submodule.mem_inf.mp hv).2) i
        exact (Submodule.mem_iInf _).mp h (Finset.mem_univ i)
      show v ∈ W
      rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := W), Submodule.mem_dualCoannihilator]
      intro ψ hψ
      have e := congrArg (fun d : W.dualAnnihilator => (d : Module.Dual K (Fin n → K)) v)
        (b.sum_repr ⟨ψ, hψ⟩)
      simp only at e
      rw [← e]
      rw [Submodule.coe_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Submodule.coe_smul, LinearMap.smul_apply, hv2, smul_zero]
    exact Submodule.span_mono (Set.image_mono hle2) hs

theorem locLatSat : PI.LocLatSat.Stmt := by
  intro F E _ _ _ _ _ sig p A n Λ W hΛ
  exact sat A.ιE A.O Λ hΛ W

end PI.LocLatSat.UnitaryGroupMassFormula
