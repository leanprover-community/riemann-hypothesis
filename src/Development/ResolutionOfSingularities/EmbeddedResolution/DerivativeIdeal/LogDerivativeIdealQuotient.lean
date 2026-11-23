module

public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
public import Mathlib.RingTheory.Ideal.Maps
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivationOfSurjective
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type*) [CommRing k] {S T : Type*} [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

theorem map_logDerivIdeal_ker_le_derivIdeal_map (f : S →ₐ[k] T)
    (hf : Function.Surjective f) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdeal k (RingHom.ker f.toRingHom) J)
      ≤ derivIdeal k (Ideal.map f.toRingHom J) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_derivIdeal k (Ideal.map f.toRingHom J) (Ideal.mem_map_of_mem f.toRingHom hx)
  · intro D hD x hx
    have hD' : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom :=
      (mem_tangentDerivations k (RingHom.ker f.toRingHom) D).mp hD
    have hmem : f x ∈ Ideal.map f.toRingHom J := Ideal.mem_map_of_mem f.toRingHom hx
    have h2 := derivation_apply_mem_derivIdeal k (Ideal.map f.toRingHom J)
      (derivationOfSurjective f hf D hD') hmem
    rw [derivationOfSurjective_apply] at h2
    rw [Ideal.mem_comap]
    exact h2

theorem map_logDerivIdealIterate_ker_le_derivIdealIterate_map (f : S →ₐ[k] T)
    (hf : Function.Surjective f) (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k (RingHom.ker f.toRingHom) r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ]
      exact (map_logDerivIdeal_ker_le_derivIdeal_map k f hf _).trans (derivIdeal_mono k ih)

theorem map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker (f : S →ₐ[k] T)
    (hf : Function.Surjective f) {P : Ideal S} (hP : P = RingHom.ker f.toRingHom)
    (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k P r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  subst hP
  exact map_logDerivIdealIterate_ker_le_derivIdealIterate_map k f hf r J

end FunctorialResolution.EmbeddedResolution
