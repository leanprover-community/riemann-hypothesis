module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartPhiE
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

variable {D : D7}

instance intEF : Algebra.IsIntegral (𝓞 D.host.F) (𝓞 D.host.E) := inferInstance

def belowPl (P : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.F) where
  asIdeal := P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)

theorem idem_exists_at (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ¬ Lev.IsConjPl (D := D) P P) :
    ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e P ∧
      ∀ v : HeightOneSpectrum (𝓞 D.host.F), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal →
        ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨e, he, ε, hε, heq⟩ := idem_at P hP (belowPl P) rfl
  refine ⟨e, he, fun v hv => ⟨ε, ?_, heq⟩⟩
  have hb : belowPl P = v := HeightOneSpectrum.ext hv
  exact hb ▸ hε

theorem twoSplitIdem (D : D7) : TwoSplitIdem D := by
  have hTS : TwoSplits D := by
    exact twoSplits D
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    exact FaithfulSMul.algebraMap_injective _ _
  intro v hv
  have hker : RingHom.ker (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQ, Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQm.isPrime, hQ0⟩
  have h2 : (2 : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h2' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) 2 ∈ Q := by
      rw [← Ideal.mem_comap]
      change (2 : 𝓞 D.host.F) ∈ Ideal.under (𝓞 D.host.F) Q
      rw [hQ]
      exact hv
    rw [map_ofNat] at h2'
    exact h2'
  obtain ⟨e, he, hall⟩ := idem_exists_at P (hTS P h2)
  obtain ⟨ε, hε, heq⟩ := hall v hQ
  exact ⟨e, ε, he.1, hε, heq⟩

end Formalism.IndefR.Fin

end
