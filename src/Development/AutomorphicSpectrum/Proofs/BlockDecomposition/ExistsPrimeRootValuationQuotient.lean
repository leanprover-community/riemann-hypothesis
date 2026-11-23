module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.MapWXi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableQuotientOfValuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectivePreservesClosednessComparability
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem untilt_mod_varpi_sq : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest →
    ∃ ϖ : A.U, ϖ ^ l = (l : A.U) ∧ R.Val0 (A.U ⧸ Ideal.span {ϖ ^ 2}) ∧
      R.Aic (A.U ⧸ Ideal.span {ϖ ^ 2}) := by
  intro l _ A hA
  obtain ⟨t, ht⟩ := A.frob_bijective.2 A.pi
  have ht' : t ^ l = A.pi := ht
  have hpow : A.sharp t ^ l = (l : A.U) := by
    rw [← map_pow, ht', A.sharp_pi]
  refine ⟨A.sharp t, hpow, ?_⟩
  have hle : Ideal.span {(l : A.U) ^ 1} ≤ Ideal.span {A.sharp t ^ 2} := by
    rw [pow_one, ← hpow]
    exact Ideal.span_singleton_le_span_singleton.2
      (pow_dvd_pow _ (Fact.out : l.Prime).two_le)
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  let g : A.A →+* A.U ⧸ Ideal.span {A.sharp t ^ 2} :=
    (Ideal.Quotient.factor hle).comp A.aToU1
  have hg : Function.Surjective g :=
    (Ideal.Quotient.factor_surjective hle).comp hsurj
  have hπ : ∀ a ∈ Ideal.span {A.pi}, g a = 0 := fun a ha => by
    rw [← hker] at ha
    change Ideal.Quotient.factor hle (A.aToU1 a) = 0
    rw [RingHom.mem_ker.1 ha, map_zero]
  let g' : A.A ⧸ Ideal.span {A.pi} →+* A.U ⧸ Ideal.span {A.sharp t ^ 2} :=
    Ideal.Quotient.lift _ g hπ
  have hg' : Function.Surjective g' := Ideal.Quotient.lift_surjective_of_surjective _ hπ hg
  exact ⟨(GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective g' hg').2
      (GlobalTheory.CompanionTheory.ValQuot.valuation_comparable_quotient A.pi hA.2),
    (GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective g hg).1 hA.1⟩

end GlobalTheory.CompanionTheory.Untilt
