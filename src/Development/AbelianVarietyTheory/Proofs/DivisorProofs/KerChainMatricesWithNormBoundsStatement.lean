module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerChainMatricesWithNormBounds
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem _root_.GlobalTheory.T.kerChain_matrices_with_norm_bounds : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms) (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) (Pl : Type) [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (hn : HtNums R (InfinitePlace K)) (no : Bs.J → ℕ) (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ), (∀ v, IsUnit (Dc.Xc u v).det) → (∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) v x ^ 2 : ℝ) : ℂ) = famIpAt (Q.F 0) (Q.hF 0) v (f0 x) (f0 x)) → (∀ i, FamFramed (Q.F i) (Q.hF i)) → DatFramed Q.S₁ Q.hS₁ → (∀ φ F, Dc.Pt u Bs.μ0 φ F = g (Q.col (f0 φ)) F) → IsFrames Df X0 → FactorBounds Q no hn.sz → (∀ (v : InfinitePlace K) (ψ : Q.S₁.EqFun) F, v (g ψ F) ^ 2 ≤ Real.exp hn.hPn * (Q.S₁.ipAt Q.hS₁ v ψ ψ).re * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody Dc u Q f0 R := by
  first | exact @GlobalTheory.DefRowsChain.rowsBody_of_framed | exact GlobalTheory.DefRowsChain.rowsBody_of_framed | (intros; apply GlobalTheory.DefRowsChain.rowsBody_of_framed <;> assumption)
