module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction
import Formalism.LocalToGlobal.IndefiniteReal.DeterminantProjection

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin

namespace SplitChar

theorem exists_place_two (F : Type) [Field F] [NumberField F] :
    ∃ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal := by
  have h2 : ¬ IsUnit (2 : 𝓞 F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 by simp, Algebra.norm_algebraMap] at hn
    have hr : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    have hge : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 F) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Module.finrank ℤ (𝓞 F) := pow_le_pow_right₀ (by norm_num) hr
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have h2mem : (2 : 𝓞 F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h0 : (2 : 𝓞 F) = 0 := (Submodule.mem_bot _).mp h2mem
    have h0' : (2 : F) = 0 := by
      have := congrArg (algebraMap (𝓞 F) F) h0
      rwa [map_ofNat, map_zero] at this
    exact two_ne_zero h0'
  exact ⟨⟨M, hM.isPrime, hM0⟩, h2mem⟩

theorem exists_splitIdem_D (D : D7) : ∃ e, IsSplitIdem D e := by
  obtain ⟨v, hv⟩ := exists_place_two D.host.F
  obtain ⟨e, ε, he, -, -⟩ := twoSplitIdem D v hv
  exact ⟨e, he⟩

variable {D : D7}

end SplitChar

end Formalism.IndefR.Fin

end
