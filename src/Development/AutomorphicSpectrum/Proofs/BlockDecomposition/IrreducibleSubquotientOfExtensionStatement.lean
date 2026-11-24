module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtension
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

theorem _root_.GlobalTheory.T.irreducible_subquotient_of_extension : ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A B : Subrepresentation ρ), A ≤ B → σ.IsIrreducible → IsSubquotient σ B.toRepresentation →
    IsSubquotient σ A.toRepresentation ∨ IsSubquotient σ (subQuot B A) := by
  first | exact @GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot | exact GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot | (intros; apply GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot <;> assumption)
