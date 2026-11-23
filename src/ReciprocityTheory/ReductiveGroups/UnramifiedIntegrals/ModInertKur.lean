module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocA
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocB
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocC
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocD
import ReciprocityTheory.NeutralLocalFields.HilbertClassField

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem inertKur {d l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (x : Om d)
    (hx : ∀ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ → σ x = x) : ι (x : ℂ) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨e, he⟩ := locEmb d l ι
  have hs : (e (algebraMap (KQ d) (Om d) (sqK d))) ^ 2 = -(d : PadicAlgCl l) := by
    have h1 : (algebraMap (KQ d) (Om d) (sqK d)) ^ 2 = -(d : Om d) := by
      apply Subtype.ext
      simpa [sqK] using sqD_sq d
    rw [← map_pow, h1, map_neg, map_natCast]
  have hint : IsIntegral ℚ_[l] (e (algebraMap (KQ d) (Om d) (sqK d))) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ_[l]), Polynomial.monic_X_pow_add_C _ (by norm_num), ?_⟩
    simp [hs]
  have hK := IntermediateField.adjoin.finiteDimensional hint
  have hmem := fixed_mem_Kur _ hK (e x) (fun ρ hρ => by
    obtain ⟨σ, hσ, hc⟩ := locLift ι e he ρ hρ
    rw [← hc, hx σ hσ])
  rw [← he]
  exact kur_le hl hld hs hmem

end ReciprocityTheory.ChartRestriction.L1
