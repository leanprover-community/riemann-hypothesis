module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionExtendBasicOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

theorem _root_.GlobalTheory.T.exists_lineBundleSection_extend_basicOpen : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (M : LB X), M.IsLB → ∀ (f : Γ(X, ⊤)) (t : ∀ c, Γ(X, M.U c ⊓ X.basicOpen f)), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ X.basicOpen f) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ X.basicOpen f) * rsT (t c') (M.U c ⊓ M.U c' ⊓ X.basicOpen f)) → ∃ (N : ℕ) (s : LB.Sec M), ∀ c, rsT (s.f c) (M.U c ⊓ X.basicOpen f) = rsT f (M.U c ⊓ X.basicOpen f) ^ N * t c := by
  first | exact @GlobalTheory.SecAff.sec_extend_basicOpen | exact GlobalTheory.SecAff.sec_extend_basicOpen | (intros; apply GlobalTheory.SecAff.sec_extend_basicOpen <;> assumption)
