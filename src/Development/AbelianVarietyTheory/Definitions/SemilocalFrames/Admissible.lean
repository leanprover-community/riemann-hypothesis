module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.HermitianCurvature.StatementD
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

noncomputable section

def aT (k r : ℕ) (α : ℂ) : B.Mat k r :=
  Matrix.diagonal fun i => if i.val < r then α ^ (r - i.val)
    else if i.val ≤ r + k then 1 else ((star α) ^ (i.val - (r + k)))⁻¹

def conjF {k r : ℕ} {V : Type*} (α : ℂ) (F : B.Mat k r → V) : B.Mat k r → V :=
  fun x => F (aT k r α * x * (aT k r α)⁻¹)

def KH (k r : ℕ) : Set (B.Mat k r) :=
  UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)

def IsStdOf {k r : ℕ} (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (Bs : B.RealPlaceData k r L.Wp L.Wq) : Prop :=
  Bs.z = L.z ∧ Bs.z' = L.z' ∧ Bs.π = L.π ∧ Bs.π' = L.π' ∧ Bs.μW = L.μW ∧ Bs.μW' = L.μW' ∧
    Bs.μN = D.muN k r ∧ Bs.μsec = μsec

def IsRatioN (k r : ℕ) (cN : ℝ) : Prop :=
  0 < cN ∧ Formalism.MainNotions.S.haarLie (Nset k r) 1 = ENNReal.ofReal cN • D.muN k r

def lamN {k r : ℕ} (L : Formalism.MainNotions.S.LocBessel k r) (cN : ℝ) : ℝ :=
  L.κN.toReal * cN * ‖cStd / L.c‖ ^ B.kap k r

end

end GlobalTheory.ThA
