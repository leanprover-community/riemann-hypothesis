module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Group.Matrix
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

noncomputable section

namespace Formalism.D

def adeleOfParts (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F)
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (x, y)

def siegelSetsSL2Adelic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ (Ω K : Set (Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F))) (t₀ : ℝ),
      IsCompact Ω ∧ (∀ p ∈ Ω, (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0) ∧ IsCompact K ∧ 0 < t₀ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F),
        ∃ γ ∈ (Matrix.SpecialLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F))).range,
        ∃ p ∈ Ω, ∃ t : ℝ, t₀ ≤ t ∧
        ∃ a a' : InfiniteAdeleRing F,
          (∀ w, a w * a' w = 1 ∧ InfinitePlace.Completion.extensionEmbedding w (a w) = (t : ℂ)) ∧
          ∃ k ∈ K, ((γ * g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F)) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
            (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) *
              !![adeleOfParts F a 1, 0; 0, adeleOfParts F a' 1] *
              (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))

end Formalism.D

end
