module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralLogHomDiagonalOfLimit
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV

@[expose] public section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.isIntegralLogHom_diagonal_of_limit : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (G : LogFGL v d) (κ : Type) [Fintype κ] [DecidableEq κ] (U : Matrix (Fin d) κ C) (L : Matrix κ (Fin d) C), (∀ a b, IsIntV v (U a b)) → (∀ a b, IsIntV v (L a b)) → U * L = 1 → ∀ t : κ → C, (∀ r : ℝ, ∃ (t' : κ → C) (A : Matrix (Fin d) (Fin d) C) (φ : Fin d → MvPowerSeries (Fin d) C), IsIntHom G G φ A ∧ (∀ ℓ, A.mulVec (fun e => U e ℓ) = t' ℓ • fun e => U e ℓ) ∧ ∀ ℓ, (r : WithTop ℝ) ≤ v (t' ℓ - t ℓ)) → ∃ φ, IsIntHom G G φ (U * Matrix.diagonal t * L) := by
  first | exact @GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit | exact GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit | (intros; apply GlobalTheory.DiagLimit.isIntHom_diagonal_of_limit <;> assumption)
