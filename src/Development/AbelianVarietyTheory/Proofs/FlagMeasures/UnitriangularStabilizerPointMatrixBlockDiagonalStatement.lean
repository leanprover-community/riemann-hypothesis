module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularStabilizerPointMatrixBlockDiagonal
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


theorem _root_.GlobalTheory.T.unitriangularStabilizer_pointMatrix_blockDiagonal : ∀ {K : Type} [Field K] (sig : K →+* K), (∀ x, sig (sig x) = x) → ∀ (r : ℕ) (w : Formalism.MainNotions.S.Point K (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K), Formalism.MainNotions.S.ZhatOM Z = Formalism.MainNotions.S.ptMat w → (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s → Formalism.MainNotions.S.IsUpUni s' → (s.map sig).transpose * Z * s' = Z → ∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) ∧ ∀ s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s' → (∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s ∧ (s.map sig).transpose * Z * s' = Z := by
  first | exact @GlobalTheory.PointStab.stab_blockDiag | exact GlobalTheory.PointStab.stab_blockDiag | (intros; apply GlobalTheory.PointStab.stab_blockDiag <;> assumption)
