module

public import Mathlib.Data.Nat.Notation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
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
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Parts

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}

private abbrev SS (n a : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ((p.1 : ℕ) < a ↔ (p.2 : ℕ) < a)}

private abbrev TT (n a : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ¬ ((p.1 : ℕ) < a ↔ (p.2 : ℕ) < a)}

private def upM (f : (SS n a → X) × (TT n a → Fin g → X)) : Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun i j => ⟨if h : i < j ∧ ((i : ℕ) < a ↔ (j : ℕ) < a) then f.1 ⟨(i, j), h⟩ else 0,
    if h : i < j ∧ ¬ ((i : ℕ) < a ↔ (j : ℕ) < a) then f.2 ⟨(i, j), h⟩ else 0, 0, 0⟩

end Parts
