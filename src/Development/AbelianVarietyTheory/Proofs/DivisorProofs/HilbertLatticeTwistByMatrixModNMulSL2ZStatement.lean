module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMulSL2Z
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul_SL2Z : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) (γ : SL(2, ℤ)), L ≤ stdLat F → twist N L (α * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) = mulMat (twist N L α) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  first | exact @GlobalTheory.HilbFam.TwistSL.twist_mul_sl | exact GlobalTheory.HilbFam.TwistSL.twist_mul_sl | (intros; apply GlobalTheory.HilbFam.TwistSL.twist_mul_sl <;> assumption)
