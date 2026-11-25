module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

open GlobalTheory.DefU

namespace GlobalTheory.Cong

theorem ofType_of_finPart_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n)
    (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) →
    OfType (fun τ => W.at τ) K π.V := by
  intro E _ _ _ n π W K f hf hf0 hK
  refine ⟨π.isAut, fun τ => ?_, ?_⟩
  · have h : (AU.mk π).HasWt (InfinitePlace.mk τ).embedding (W (InfinitePlace.mk τ)) :=
      hasWeightAt_of_finPart π W hf hf0 (InfinitePlace.mk τ)
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · have h' := h
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), e] at h'
      exact h'
    · have h2 := h.conjugate
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ] at h2
      exact h2
  · have hne : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v, f.1 v ≠ 0 := by
      by_contra! hc
      exact hne (LinearMap.ext hc)
    refine ⟨f.1 v, AutSub.mem_finPart.1 hf v, hv, fun x hx => ?_⟩
    funext g
    rw [RU_apply]
    exact hK x hx v g

end GlobalTheory.Cong

end
