module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivative
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

@[expose] public section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.algebraMap_not_mem_sq_of_derivative_not_mem : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (p : HeightOneSpectrum (𝓞 E)) (P : HeightOneSpectrum (𝓞 E')) (β : 𝓞 E') (f : Polynomial ℤ),
    f.Monic → Polynomial.aeval β f = 0 → Algebra.adjoin E {(β : E')} = ⊤ →
    (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 E') x ∈ P.asIdeal ↔ x ∈ p.asIdeal) →
    Polynomial.aeval β (Polynomial.derivative f) ∉ P.asIdeal →
    ∀ c : 𝓞 E, c ∉ p.asIdeal ^ 2 → algebraMap (𝓞 E) (𝓞 E') c ∉ P.asIdeal ^ 2 := by
  first | exact @GlobalTheory.UnramSimpleGen.not_mem_sq_of_derivative | exact GlobalTheory.UnramSimpleGen.not_mem_sq_of_derivative | (intros; apply GlobalTheory.UnramSimpleGen.not_mem_sq_of_derivative <;> assumption)
