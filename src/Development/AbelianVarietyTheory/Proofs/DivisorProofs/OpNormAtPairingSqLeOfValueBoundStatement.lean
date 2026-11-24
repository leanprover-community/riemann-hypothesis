module

public import Formalism.HarderNarasimhan.QuotRealize
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormAtPairingSqLeOfValueBound
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem _root_.GlobalTheory.T.opNormAt_pairing_sq_le_of_value_bound : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (c n : ℕ) (X : InfinitePlace K → Matrix (Fin c) (Fin c) ℂ) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K)) (v : InfinitePlace K) (A : ℝ), IsUnit (X v).det → IsUnit (X0 v).det → (∀ y F, v (g y F) ^ 2 ≤ Real.exp A * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin c)) X v y ^ 2 * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2) → Formalism.HN.opNormAt (Pi.basisFun K (Fin c)) X (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v g ^ 2 ≤ Real.exp A := by
  first | exact @GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le | exact GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le | (intros; apply GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le <;> assumption)
