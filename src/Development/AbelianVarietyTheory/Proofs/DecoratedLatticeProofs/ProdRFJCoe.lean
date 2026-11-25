module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

noncomputable section
namespace GlobalTheory.HaarR

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def prodR (p : ℕ) (q : GL n k × N k n c p) : R k n c p :=
  ⟨embX c q.1 * (q.2 : GL (n ⊕ Fin c) k), mul_mem (Subgroup.mem_sup_left ⟨q.1, rfl⟩) (Subgroup.mem_sup_right q.2.2)⟩

def prodRFJ (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) : RFJ k n c ρ :=
  ⟨embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2,
    mul_mem (Subgroup.mem_sup_right (mul_mem (Subgroup.mem_sup_left ⟨q.1.1, rfl⟩) (Subgroup.mem_sup_right q.1.2.2)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c ρ).2.2.2.2.2.2.2 (ρ + 1) q.2 (Nat.lt_succ_self ρ)).1))⟩

@[simp] theorem prodR_coe (p : ℕ) (q : GL n k × N k n c p) :
    (prodR p q : GL (n ⊕ Fin c) k) = embX c q.1 * (q.2 : GL (n ⊕ Fin c) k) := rfl

@[simp] theorem prodRFJ_coe (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    (prodRFJ ρ q : GL (n ⊕ Fin c) k) = embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2 := rfl

def cjE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) : N k n c (ρ + 1) :=
  ⟨colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹,
    (GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ h1 h2).2 β u u.2⟩

@[simp] theorem cjE_coe (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) :
    (cjE ρ h1 h2 β u : GL (n ⊕ Fin c) k) = colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹ := rfl

end GlobalTheory.HaarR
end
