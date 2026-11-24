module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetOperatorBideterminantBasisReprIsAlgebraic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.L2.Ker MvPolynomial

theorem _root_.GlobalTheory.T.jetOperator_bideterminantBasis_repr_isAlgebraic : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight a) (lam' : ι → Formalism.BasicNotions.DomWeight b) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ), (∀ m, IsAlgebraic ℚ (J m)) → JetInVV ℂ lam lam' nn → ∀ (i : Formalism.L2.DIV.VVIdx lam') (j : Formalism.L2.DIV.VVIdx lam), IsAlgebraic ℚ ((Formalism.L2.DIV.bVV ℂ lam').repr (jetOp lam lam' J nn (Formalism.L2.DIV.bVV ℂ lam j)) i) := by
  first | exact @GlobalTheory.JetAlg.repr_jetOp_isAlgebraic | exact GlobalTheory.JetAlg.repr_jetOp_isAlgebraic | (intros; apply GlobalTheory.JetAlg.repr_jetOp_isAlgebraic <;> assumption)
