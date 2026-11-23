module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.TypePlacesExhaust

variable {R : Ranks} (H : Host R)

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

def conjPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap ((cInt H).symm : 𝓞 H.E →+* 𝓞 H.E) (cInt H).symm.surjective w

variable {H}

theorem mem_conjPl (w : HeightOneSpectrum (𝓞 H.E)) (y : 𝓞 H.E) :
    y ∈ (conjPl H w).asIdeal ↔ (cInt H).symm y ∈ w.asIdeal := Iff.rfl

theorem isConjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (conjPl H w) := by
  intro x y hy
  have e : y = cInt H x := RingOfIntegers.ext (by rw [hy]; rfl)
  subst e
  rw [mem_conjPl, RingEquiv.symm_apply_apply]

theorem conjPl_injective : Function.Injective (conjPl H) := by
  intro w w' h
  apply HeightOneSpectrum.ext
  ext x
  have := congrArg (fun u : HeightOneSpectrum (𝓞 H.E) => cInt H x ∈ u.asIdeal) h
  simp only [mem_conjPl, RingEquiv.symm_apply_apply] at this
  exact Iff.of_eq this

theorem conjPl_mem_placesOver {p : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E p) :
    conjPl H w ∈ placesOver H.E p := by
  show ((p : ℕ) : 𝓞 H.E) ∈ (conjPl H w).asIdeal
  rw [mem_conjPl, map_natCast]
  exact hw

theorem finrank_E (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem eq_plGw_or_isConjPl : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    ∃ v : D.nd.PlG k, w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w := by
  apply GlobalTheory.TypePlaceCover.place_cover <;> assumption

end GlobalTheory.TypePlacesExhaust
