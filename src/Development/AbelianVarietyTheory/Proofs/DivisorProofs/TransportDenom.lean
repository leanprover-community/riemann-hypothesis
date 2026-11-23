module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom


open Formalism.UG in
theorem transport_denom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)),
    ∃ C : ℝ, ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ∧
      ∀ (M : ℕ) (y : Fin n × Fin d → AF F), IsMulInt F (M * N) y →
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).1 ∧
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).2 :=
  @GlobalTheory.ThetaLevel.transport_denom

end GlobalTheory.ThetaDenom

end
