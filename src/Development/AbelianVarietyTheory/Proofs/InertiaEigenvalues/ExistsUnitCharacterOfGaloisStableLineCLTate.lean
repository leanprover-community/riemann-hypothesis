module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_unit_character_of_stable_line (l : ℕ) [Fact l.Prime] (y : ℂ_[l]) (hy : y ≠ 0)
    (h : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) :
    ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l,
      Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  choose x hx using h
  have hn : ∀ g, ‖x g‖ = 1 := fun g => by
    have h1 := GlobalTheory.RingBasics.norm_σC g y
    rw [hx, norm_mul, norm_algebraMap'] at h1
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 hy) (h1.trans (one_mul _).symm)
  have hm : ∀ g k, x (g * k) = x g * x k := fun g k => by
    apply (algebraMap ℚ_[l] ℂ_[l]).injective
    apply mul_right_cancel₀ hy
    rw [← hx, GlobalTheory.RingBasics.σC_mul, hx k, map_mul, TateTwist.σC_algebraMap, hx g, map_mul]
    ring
  refine ⟨MonoidHom.mk' (fun g => PadicInt.mkUnits (hn g)) fun g k => ?_, fun g => hx g⟩
  apply Units.ext
  apply Subtype.ext
  exact hm g k

end GlobalTheory.Per
