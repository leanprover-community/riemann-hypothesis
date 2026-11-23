module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerRelationPassesToSemiLocalSpan
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.whittaker_relation_passes_to_semi_local_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ (t : GA E a) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | exact @GlobalTheory.JSW.MirSemi.whit_rel_locSpan | exact GlobalTheory.JSW.MirSemi.whit_rel_locSpan | (intros; apply GlobalTheory.JSW.MirSemi.whit_rel_locSpan <;> assumption)
