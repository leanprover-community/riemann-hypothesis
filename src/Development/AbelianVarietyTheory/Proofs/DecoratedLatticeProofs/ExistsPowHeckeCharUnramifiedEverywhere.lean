module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.Corev.UnrPow

theorem exists_pow_unrAt : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L),
    ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  intro L _ _ χ
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := GlobalTheory.Mem.FinOrder.exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    exact hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu m) (hx x hu)
  choose m hm0 hm using hm
  refine ⟨∏ v ∈ hfin.toFinset, m v, Finset.prod_pos fun v _ => hm0 v, fun v x hx => ?_⟩
  show χ.loc v x ^ (∏ v ∈ hfin.toFinset, m v) = 1
  by_cases hv : χ.UnrAt v
  · rw [hv x hx, one_pow]
  · obtain ⟨d, hd⟩ : m v ∣ ∏ v ∈ hfin.toFinset, m v := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
    rw [hd, pow_mul, hm v x hx, one_pow]

end GlobalTheory.Corev.UnrPow
