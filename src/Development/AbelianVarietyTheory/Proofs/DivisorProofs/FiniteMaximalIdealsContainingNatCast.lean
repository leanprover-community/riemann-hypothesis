module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
public import Mathlib.RingTheory.DedekindDomain.Factorization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowDat

theorem finite_maximal_ideals_containing_natCast :
    ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite := by
  intro E _ _ n hn
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  have hI : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hn0
  refine ((Ideal.finite_factors hI).image
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) => v.asIdeal)).subset ?_
  rintro 𝔮 ⟨hmax, hmem⟩
  have hne : 𝔮 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hn0 hmem
  refine ⟨⟨𝔮, hmax.isPrime, hne⟩, ?_, rfl⟩
  show 𝔮 ∣ Ideal.span {(n : 𝓞 E)}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hmem

end GlobalTheory.LowDat
