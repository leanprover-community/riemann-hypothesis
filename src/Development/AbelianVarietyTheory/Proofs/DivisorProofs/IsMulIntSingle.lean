module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom


variable (F : Type) [Field F] [NumberField F] in
def IsMulInt {κ : Type} (M : ℕ) (z : κ → AF F) : Prop :=
  (∀ i, (z i).1 = 0) ∧ ∀ v i, ‖evFin F v (z i)‖ ≤ ‖(M : Fv F v)‖

theorem IsMulInt.mono {F : Type} [Field F] [NumberField F] {κ : Type} {k m : ℕ} {a : κ → AF F}
    (h : IsMulInt F (k * m) a) : IsMulInt F m a := by
  refine ⟨h.1, fun v i => (h.2 v i).trans ?_⟩
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (_root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one v k)

def sand {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) :
    Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AF F ⊗[F] E) where
  toFun X := g * X * hᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.ThetaDenom

end
