module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.BcB.G3.count1_pf (h1 : Param) : Count1 := by
  intro E _ _ _ hU n S hS P hP y hy hint
  obtain ⟨ι, _, K, L, _, _, _, _, _, _, x, hcard, hR, hC, hA, hsum, ⟨e⟩⟩ :=
    h1 E hU n S hS P hP y hy hint
  rw [Nat.card_congr e, Nat.card_pi, ← hcard, ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two (K i) (L i) (hR i) (hC i) (x i) (hA i)

end
