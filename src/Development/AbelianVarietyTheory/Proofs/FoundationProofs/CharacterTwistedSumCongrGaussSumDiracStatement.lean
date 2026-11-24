module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTwistedSumCongrGaussSumDirac
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.characterTwistedSum_congr_gaussSum_dirac : ∀ (l : ℕ) [Fact l.Prime] (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), 1 ≤ m → l ^ (3 * m) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → Cg (2 * m) (chSum F m z ψ) (gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m))) := by
  first | exact @GlobalTheory.KZ.Cmp.ChD.chSum_gauss | exact GlobalTheory.KZ.Cmp.ChD.chSum_gauss | (intros; apply GlobalTheory.KZ.Cmp.ChD.chSum_gauss; all_goals assumption)
