module

public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.EqOffBound
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.Assemble
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.SplitElementExistsHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore

@[expose] public section

noncomputable section

namespace GlobalTheory.EqOffSplitOfSplit

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem isSplit_conj (D : D7) {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : GL3Theta.SplitP D P)
    (hQ : ∀ x : 𝓞 D.host.E, x ∈ Q.asIdeal ↔ Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ P.asIdeal) : GL3Theta.SplitP D Q := by
  obtain ⟨a, b, hab, ha, hb⟩ := hP
  have hb' : b = Formalism.L2.PairingIndexBounds.Rec.cO D a := Subtype.ext (hab.trans rfl)
  refine ⟨b, a, ?_, ?_, ?_⟩
  · rw [hab]; exact (Formalism.L2.PairingIndexBounds.Rec.conj_conj' D (a : D.host.E)).symm
  · rw [hQ, hb', Formalism.L2.PairingIndexBounds.Rec.cO_cO]; exact ha
  · rw [hQ, ← hb']; exact hb

theorem eqOffSplit_of_eqOff : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ)
    (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := by
  intro D P n L L₀ hP hoff
  obtain ⟨m, hm⟩ := hoff
  obtain ⟨x, hx0, hxP, hxM⟩ := Formalism.L2.PairingIndexBounds.Rec.genPow D P
  have hc0 : ∀ y : 𝓞 D.host.E, y ≠ 0 → Formalism.L2.PairingIndexBounds.Rec.cO D y ≠ 0 := fun y hy h => hy (by
    rw [← Formalism.L2.PairingIndexBounds.Rec.cO_cO D y, h, map_zero])
  have hg0 : x ^ m ≠ 0 := pow_ne_zero m hx0
  obtain ⟨h1, h2⟩ := hm (x ^ m) (Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m)) rfl (Ideal.pow_mem_pow hxP m)
  refine ⟨x ^ m * Formalism.L2.PairingIndexBounds.Rec.cO D (x ^ m), mul_ne_zero hg0 (hc0 _ hg0), fun Q hQ => ?_, h1, h2⟩
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have e : P.asIdeal = Q.asIdeal := hxM _ Q.isPrime (Q.isPrime.mem_of_pow_mem m h)
    have e' : P = Q := HeightOneSpectrum.ext e
    exact e' ▸ hP
  · rw [map_pow] at h
    have h3 : Formalism.L2.PairingIndexBounds.Rec.cO D x ∈ Q.asIdeal := Q.isPrime.mem_of_pow_mem m h
    have e : P.asIdeal = (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).asIdeal :=
      hxM _ (Formalism.L2.PairingIndexBounds.Rec.cQ D Q).isPrime ((Formalism.L2.PairingIndexBounds.Rec.mem_cQ D Q x).2 h3)
    refine isSplit_conj D hP fun y => ?_
    rw [e, Formalism.L2.PairingIndexBounds.Rec.mem_cQ, Formalism.L2.PairingIndexBounds.Rec.cO_cO]

end GlobalTheory.EqOffSplitOfSplit
