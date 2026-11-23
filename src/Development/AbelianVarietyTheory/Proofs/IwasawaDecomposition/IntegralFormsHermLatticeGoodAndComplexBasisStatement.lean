module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι), (MtHL I hX a).Good ∧ (∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, ∀ x, j x = toCx I hX a x) ∧ LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) ∧ Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  first | exact @GlobalTheory.Mem.Df.mtHL_good_basis | exact GlobalTheory.Mem.Df.mtHL_good_basis | (intros; apply GlobalTheory.Mem.Df.mtHL_good_basis <;> assumption)
