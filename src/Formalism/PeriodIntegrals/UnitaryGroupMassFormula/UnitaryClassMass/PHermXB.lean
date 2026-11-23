module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermSk
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem local_switching_lattice : LocSw := by
  intro F E _ _ _ _ _ _ σ hσ hfix V _ _ p hp t ht X
  have hσσ : ∀ a, σ (σ a) = a := fun a => by rw [hσ, hσ, star_star]
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  have hcomm : ∀ c : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) c) =
      algebraMap F E (algebraMap (𝓞 F) F c) := by
    intro c
    first
    | rfl
    | rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hSw : Sw F E t ≤ hcompl (K := E) p := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := Submonoid.mem_map.1 hs
    apply Submonoid.subset_closure
    rw [Set.mem_setOf_eq]
    have hcp : algebraMap (𝓞 F) (𝓞 E) c ∉ p := by
      intro h'
      apply Ideal.mem_primeCompl_iff.1 hc
      rw [ht, Ideal.mem_comap]
      exact h'
    refine ⟨hcp, fun t' ht' => ?_⟩
    have h3 : t' = algebraMap (𝓞 F) (𝓞 E) c := by
      apply hinj
      rw [ht', hcomm, ← hσ, AlgHom.commutes]
    rw [h3]
    exact hcp
  have key : ∀ s ∈ hcompl (K := E) p, ∃ r : 𝓞 E, r * s ∈ Sw F E t := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨hsp, hconj⟩ := hs
      have hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E s)) :=
        (NumberField.RingOfIntegers.isIntegral_coe s).map σ.toRingHom.toIntAlgHom
      let sb : 𝓞 E := ⟨σ (algebraMap (𝓞 E) E s), hint⟩
      have hsb : algebraMap (𝓞 E) E sb = star (algebraMap (𝓞 E) E s) := by
        rw [← hσ]
        rfl
      have hsbp : sb ∉ p := hconj sb hsb
      have hfixN : σ (algebraMap (𝓞 E) E (sb * s)) = algebraMap (𝓞 E) E (sb * s) := by
        rw [map_mul, map_mul, hsb, ← hσ, hσσ, mul_comm]
      obtain ⟨c, hc⟩ := hfix _ hfixN
      have hcint : IsIntegral ℤ c := by
        rw [← isIntegral_algebraMap_iff (B := E), hc]
        exact NumberField.RingOfIntegers.isIntegral_coe (sb * s)
      let c' : 𝓞 F := ⟨c, hcint⟩
      have hc' : algebraMap (𝓞 F) (𝓞 E) c' = sb * s := by
        apply hinj
        rw [hcomm, ← hc]
        rfl
      refine ⟨sb, Submonoid.mem_map.2 ⟨c', ?_, hc'⟩⟩
      rw [Ideal.mem_primeCompl_iff, ht, Ideal.mem_comap, hc']
      exact fun h' => (hp.isPrime.mem_or_mem h').elim hsbp hsp
    | one => exact ⟨1, by rw [one_mul]; exact (Sw F E t).one_mem⟩
    | mul x y _ _ hx hy =>
      obtain ⟨r1, h1⟩ := hx
      obtain ⟨r2, h2⟩ := hy
      refine ⟨r1 * r2, ?_⟩
      rw [show r1 * r2 * (x * y) = r1 * x * (r2 * y) by ring]
      exact (Sw F E t).mul_mem h1 h2
  unfold loc
  ext x
  constructor
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨r, hr⟩ := key s hs
    exact (show ∃ s ∈ Sw F E t, s • x ∈ X from
      ⟨r * s, hr, by rw [mul_smul]; exact X.smul_mem r hsx⟩)
  · rintro ⟨s, hs, hsx⟩
    exact (show ∃ s ∈ hcompl (K := E) p, s • x ∈ X from ⟨s, hSw hs, hsx⟩)

end PI.UnitaryGroupMassFormula.UJClassMass

end
