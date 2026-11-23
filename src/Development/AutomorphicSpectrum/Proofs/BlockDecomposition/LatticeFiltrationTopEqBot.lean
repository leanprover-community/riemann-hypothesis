module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPowStatement
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

@[expose] public section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatNil

theorem isDPMorphism_ι {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M) := by
  refine ⟨Ideal.map_comap_le, ?_⟩
  intro n a ha
  exact (Lat.ι_γ f ξ l M hc ha).symm

theorem dividedPowerFiltration_eq_bot : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), pdP (Lat.γ f ξ l M hc) m = ⊥ := by
  intro W B _ _ _ f ξ l M m h hc
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  have h1 : Lat.ι f ξ l M x ∈ pdP (Lat.γB f ξ) m := dividedPowerFiltration_map (isDPMorphism_ι f ξ l M hc) m hx
  rw [GlobalTheory.T.divided_power_filtration_span_pow f ξ m, h.nil, Ideal.mem_span_singleton, zero_dvd_iff] at h1
  exact Lat.ι_injective f ξ l M (by rw [h1, map_zero])

end GlobalTheory.CompanionTheory.LatNil
