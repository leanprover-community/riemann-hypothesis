module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDerivFamily
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesContinuationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVerticalBoundStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.SiegelEisHalf

theorem eisHalf : EisHalf := by
  unfold SiegelEisensteinSeries.EisHalf
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨Ê, t₁, hsum, hdiff⟩ := GlobalTheory.T.eisenstein_series_continuation F E σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t₀, h23⟩ := GlobalTheory.T.eisenstein_vertical_bound F E σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t, ht₀, ht₁⟩ : ∃ t : ℝ, t₀ ≤ t ∧ t₁ ≤ t := ⟨max t₀ t₁, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ z : ℂ, t < z.re → ∀ x : GlobalTheory.ThK.Dbl.G2 σ Y,
      HasSum (GlobalTheory.ThK.Dbl.eisTerm (GlobalTheory.ThK.Dbl.flat a f s₁ z) x) (Ê z x) :=
    fun z hz x => hsum z (lt_of_le_of_lt ht₁ hz) x
  obtain ⟨hmod, hcont, hbd⟩ := h23 t Ê ht₀ hsum'
  let v : ℂ → ↥(GlobalTheory.ThK.Dbl.modFun σ Y) := fun z =>
    if hz : t < z.re then ⟨fun x => Ê z x, hmod z hz⟩ else 0
  have hv : ∀ z : ℂ, t < z.re → ∀ x : GlobalTheory.ThK.Dbl.G2 σ Y,
      (↑(v z) : GlobalTheory.ThK.Dbl.G2 σ Y → ℂ) x = Ê z x := by
    intro z hz x
    simp only [v]
    rw [dite_eq_left hz]
  refine ⟨t, v, fun z hz x => by rw [hv z hz x]; exact hsum' z hz x, ?_⟩
  have hS : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS
  · intro x
    exact ((hdiff x).mono fun z hz => lt_of_le_of_lt ht₁ hz).congr fun z hz => hv z hz x
  · exact hcont.congr fun y hy => hv y.1 hy.1 y.2
  · intro Q hQS hQ
    rcases Q.eq_empty_or_nonempty with hQe | hne
    · exact ⟨0, 0, fun z hz => by simp [hQe] at hz⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hQ.exists_isMinOn hne Complex.continuous_re.continuousOn
      obtain ⟨z₁, _, hmax⟩ := hQ.exists_isMaxOn hne Complex.continuous_re.continuousOn
      obtain ⟨C, N, hC⟩ := hbd z₀.re z₁.re (hQS hz₀)
      refine ⟨C, N, fun z hz x => ?_⟩
      rw [hv z (hQS hz) x]
      exact hC z (isMinOn_iff.mp hmin z hz) (isMaxOn_iff.mp hmax z hz) x

end GlobalTheory.CompanionTheory.SiegelEisHalf

end
