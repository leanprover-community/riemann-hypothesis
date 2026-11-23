module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spcᵒᵖ) (n : ℤ), n < 0 → IsZero (((HC R F).obj E).X n)) ∧ ∃ cl : ∀ (E : Spc) (n : ℤ) (z : ((HC R F).obj (op E)).X n), ((HC R F).obj (op E)).d n (n + 1) z = 0 → H R E F n, (∀ E n x, ∃ z hz, cl E n z hz = x) ∧ (∀ E n z hz z' hz', cl E n z hz = cl E n z' hz' ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = z' + ((HC R F).obj (op E)).d (n - 1) n y) ∧ (∀ E n z hz, cl E n z hz = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = ((HC R F).obj (op E)).d (n - 1) n y) ∧ ∀ (E E' : Spc) (f : E ⟶ E') n z hz, ∃ h, pull R f F n (cl E' n z hz) = cl E n (((HC R F).map f.op).f n z) h := by
  first | exact @GlobalTheory.EtC.HCElements.main | exact GlobalTheory.EtC.HCElements.main | (intros; apply GlobalTheory.EtC.HCElements.main <;> assumption)
