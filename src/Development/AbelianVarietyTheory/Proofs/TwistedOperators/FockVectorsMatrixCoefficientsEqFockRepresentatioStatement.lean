module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsMatrixCoefficientsEqFockRepresentatio
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.fockVectors_matrixCoefficients_eq_fockRepresentation : ∀ (p q r s n : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (ι Z : Type) (G fr : Mn n) (ε : Fin n → Bool) (br : Bool) (e : Ix p q ≃ Fin n) (A : Mn n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (Θ : Submodule ℂ (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) (c : ℚ) (m : ℤ) (N : ℝ), 1 ≤ p + q → IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → SignCompat ε e → (m : ℚ) = 2 * c → Side A pt κ (phiFr fr br e) c (fockAct1 p q r s) → L2UnitaryRepresentationData G A pt ip Θ → Fischer pt ip κ N → Coef F A pt ip κ (phiFr fr br e) m N := by
  first | exact @GlobalTheory.ArchRec.FockCoef.coef_of_side | exact GlobalTheory.ArchRec.FockCoef.coef_of_side | (intros; apply GlobalTheory.ArchRec.FockCoef.coef_of_side <;> assumption)
