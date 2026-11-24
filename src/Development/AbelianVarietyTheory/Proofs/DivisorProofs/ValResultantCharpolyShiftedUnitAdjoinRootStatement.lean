module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValResultantCharpolyShiftedUnitAdjoinRoot
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

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.val_resultant_charpoly_shifted_unit_adjoinRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (k : ℕ) (t : K.O), t ≠ 0 → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (B₁.P * B₂.P).Separable ∧ GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) - ((k * a * b : ℕ) : ℤ) := by
  first | exact @GlobalTheory.UnitLemma.ShiftRes.val_resultant_shift | exact GlobalTheory.UnitLemma.ShiftRes.val_resultant_shift | (intros; apply GlobalTheory.UnitLemma.ShiftRes.val_resultant_shift <;> assumption)
