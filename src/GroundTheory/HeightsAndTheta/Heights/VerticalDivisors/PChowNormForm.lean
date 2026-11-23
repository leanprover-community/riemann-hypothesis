module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem specRest_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {n e : ℕ}
    (φ : R →+* S) (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by
  unfold specRest
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext ij
    obtain ⟨i, j⟩ := ij
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem ChowNormForm.proof (h₁ : ChowNormFormGeneric.Statement)
    (h₂ : SecAlgFieldChange.Statement) : ChowNormForm.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  have hinj : Function.Injective
      ((MvPolynomial.aeval y : MvPolynomial (Par e n) k →ₐ[k] E) : MvPolynomial (Par e n) k →+* E) :=
    hy
  set φ : GenParField k e n →+* E := IsFractionRing.lift hinj with hφ
  have hφC : φ.comp (algebraMap k (GenParField k e n)) = algebraMap k E := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k),
      hφ, IsFractionRing.lift_algebraMap]
    simp
  have hy' : y = φ ∘ genPar k e n := by
    funext p
    simp [hφ, genPar, IsFractionRing.lift_algebraMap]
  have hQ' : Q.map (MvPolynomial.map (algebraMap k E)) =
      (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))).map (MvPolynomial.map φ) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun p => by rw [RingHom.comp_apply, map_map, hφC]
  obtain ⟨hfin₀, c, hc, heq⟩ := h₁ k n e Q g hQ hg
  obtain ⟨hfin, hnorm⟩ := h₂ (GenParField k e n) E φ n e _ (genPar k e n) hfin₀
  rw [hQ', hy']
  refine ⟨hfin, φ c, (map_ne_zero φ).mpr hc, ?_⟩
  rw [← hnorm, ← hφC, ← specRest_map, heq, _root_.map_mul, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
