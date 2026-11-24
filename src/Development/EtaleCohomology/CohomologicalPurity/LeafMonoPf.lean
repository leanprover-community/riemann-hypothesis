module

public import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

theorem mono_freeP (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((freeP R).map g) := by
  have : ∀ U, Mono (((freeP R).map g).app U) := by
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 inferInstance
    rw [ModuleCat.mono_iff_injective]
    dsimp [freeP]
    exact Finsupp.mapDomain_injective (fun a b h => ULift.ext (hg (congrArg ULift.down h)))
  exact NatTrans.mono_of_mono_app _

theorem mono_free (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((free R).map g) := by
  have := mono_freeP R g
  dsimp [free]
  infer_instance

theorem LeafMono_of : LeafMono := by
  intro R _ U E f hf p
  have hk : ∀ k : ℕ, Mono (((chainsN R).map f).f k) := by
    intro k
    have : Mono (f.app (op (SimplexCategory.mk k))) := inferInstance
    have := mono_free R (f.app (op (SimplexCategory.mk k)))
    simp only [chainsN, Functor.comp_map, AlgebraicTopology.alternatingFaceMapComplex_map_f]
    exact this
  by_cases h : ∃ k : ℕ, -(k : ℤ) = p
  · obtain ⟨k, rfl⟩ := h
    have e := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k:ℤ)) rfl
    change Mono (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f _)
    rw [e]
    have := hk k
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) := by
      apply HomologicalComplex.isZero_extend_X
      intro k hk; exact h ⟨k, hk⟩
    exact hz.mono _
