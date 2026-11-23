module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExistsUnifFv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.EventuallySmulSub
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.VolFromSW

@[expose] public section

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def unifV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Fv F v :=
  ((v.valuation_exists_uniformizer F).choose : Fv F v)

theorem unifV_val {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := by
  rw [unifV, v.valuedAdicCompletion_eq_valuation', (v.valuation_exists_uniformizer F).choose_spec]

theorem unifV_spec {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    unifV v ≠ 0 ∧ Tendsto (fun k : ℕ => unifV v ^ k) atTop (𝓝 0) ∧
      unifV v ∈ v.adicCompletionIntegers F := by
  have hv := unifV_val v
  have h1 : Valued.v (unifV v) < 1 := by
    rw [hv]
    decide
  refine ⟨fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖unifV v‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

def hF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
    (n : ℕ) : AddSubgroup (HermR (Fv F v) σ a) :=
  smulSub (unifV v ^ (n + 1)) (hermO b v σ a)

end PI.VolStabSW
