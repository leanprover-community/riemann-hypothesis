module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LandherrStandardDefiniteHermitianCmField
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.landherr_standard_definite_hermitian_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E), H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) → ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := by
  first | exact @GlobalTheory.LandherrStd.main | exact GlobalTheory.LandherrStd.main | (intros; apply GlobalTheory.LandherrStd.main <;> assumption)
