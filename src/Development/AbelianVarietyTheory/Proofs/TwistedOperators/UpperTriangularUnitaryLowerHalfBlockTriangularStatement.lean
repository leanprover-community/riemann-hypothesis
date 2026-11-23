module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperTriangularUnitaryLowerHalfBlockTriangular
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.upperTriangularUnitary_lowerHalfBlock_triangular : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (hn : n ≤ n'), (∀ g : GU σ n, IsBorelU g → ∃ U : GL (Fin (n / 2)) L, U.1 = lowBlock g.1.1 ∧ U.1.BlockTriangular id ∧ ∀ r, ordL (U.1 r r) = -ordL (g.1.1 (lo n r.rev) (lo n r.rev))) ∧ ∀ h : GU σ n', IsBorelU h → ∃ V : GL (Fin (n / 2)) L, V.1.BlockTriangular id ∧ (∀ r : Fin (n / 2), ordL (V.1 r.rev r.rev) = ordL (h.1.1 (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩) (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩))) ∧ ∀ t : Matrix (Fin (n / 2)) (Fin (n / 2)) L, lowBlock (h⁻¹).1.1 * (Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0) = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then (V.1 * t) ⟨r.1, e⟩ c else 0 := by
  exact @GlobalTheory.SphTheta.lowBlocks_borel
