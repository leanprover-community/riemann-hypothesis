module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

noncomputable def autEmb {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) : Emb F :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).embedding

theorem autEmb_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) (y : F) :
    ((autEmb g i y : ℝ) : ℂ) = g ((i y : ℝ) : ℂ) :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).coe_embedding_apply y

theorem autEmb_injective {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) :
    Function.Injective (autEmb (F := F) g) := by
  intro i j h
  ext y
  have h1 : g ((i y : ℝ) : ℂ) = g ((j y : ℝ) : ℂ) := by
    rw [← autEmb_apply, ← autEmb_apply, h]
  exact_mod_cast g.injective h1

theorem aut_perm_emb : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ),
    ∃ π : Equiv.Perm (Emb F), ∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ) := by
  intro F _ _ _ g
  refine ⟨Equiv.ofBijective (autEmb g) (Finite.injective_iff_bijective.mp (autEmb_injective g)), ?_⟩
  intro i y
  exact (autEmb_apply g i y).symm

end GlobalTheory.HilbFam
