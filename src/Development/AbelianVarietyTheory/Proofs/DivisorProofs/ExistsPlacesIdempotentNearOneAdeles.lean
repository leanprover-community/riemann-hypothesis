module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section
namespace GlobalTheory

open Filter

theorem placesIdem_mem_nhds_one (F : Type) [Field F] [NumberField F] (U : Set (AF F)) (hU : U ∈ 𝓝 (1 : AF F)) :
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  classical
  let x : Finset (HeightOneSpectrum (𝓞 F)) → Π v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun T v => if v ∈ T then ⟨1, (v.adicCompletionIntegers F).one_mem⟩ else ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  let one' : Π v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨1, (v.adicCompletionIntegers F).one_mem⟩
  let sm := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AF F := fun T => ((1 : Ainf F), (sm (x T) : Af F))
  have hx : Tendsto x atTop (𝓝 one') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_atTop_of_eventually_const (i₀ := {v})
    intro T hT
    simp [x, one', hT (Finset.mem_singleton_self v)]
  have h1 : (sm one' : Af F) = 1 := by
    ext v; rfl
  have he : Tendsto e atTop (𝓝 (1 : AF F)) := by
    have hc : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
    have h2 : Tendsto (fun T => (sm (x T) : Af F)) atTop (𝓝 (1 : Af F)) := by
      have h3 := (hc.tendsto one').comp hx
      rw [h1] at h3
      exact h3
    exact Tendsto.prodMk_nhds tendsto_const_nhds h2
  obtain ⟨T, hT⟩ := (he.eventually hU).exists
  refine ⟨Finset.univ, T, e T, ⟨?_, ?_, ?_, ?_⟩, hT⟩
  · intro w _; rfl
  · intro w hw; exact absurd (Finset.mem_univ w) hw
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 1
    simp [x, hv]
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 0
    simp [x, hv]

theorem placesIdem_tendsto_one : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) →
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U :=
  fun F _ _ U hU => placesIdem_mem_nhds_one F U hU

end GlobalTheory
