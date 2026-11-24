module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboli
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_disjoint_unipotentCells_cover_compact_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (C : Set (GA E (m + 1))), IsCompact C → ∀ V : GA E (m + 1) → Subgroup (GL (Fin (m + 1)) (Af E)), (∀ q, IsOpen (V q : Set (GL (Fin (m + 1)) (Af E)))) → ∃ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (R : Finset (GA E (m + 1))) (j : GA E (m + 1) → GA E (m + 1)), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) ∧ IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) ∧ (∀ x ∈ R, j x ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) (j x) = 1 ∧ K ≤ V (j x) ∧ GlobalTheory.JSW.MirPatch.cell K x ⊆ GlobalTheory.JSW.MirPatch.cell (V (j x)) (j x)) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → ∃ x ∈ R, p ∈ GlobalTheory.JSW.MirPatch.cell K x) ∧ (∀ x ∈ R, ∀ x' ∈ R, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell K x → p ∈ GlobalTheory.JSW.MirPatch.cell K x' → x = x') := by
  first | exact @GlobalTheory.JSW.MirPatch.Cover.exists_cover | exact GlobalTheory.JSW.MirPatch.Cover.exists_cover | (intros; apply GlobalTheory.JSW.MirPatch.Cover.exists_cover <;> assumption)
