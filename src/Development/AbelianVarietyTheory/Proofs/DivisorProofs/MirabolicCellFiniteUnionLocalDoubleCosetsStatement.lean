module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosets
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

theorem _root_.GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  first | (exact @GlobalTheory.JSW.MirPatch.cell_decomp) | (exact GlobalTheory.JSW.MirPatch.cell_decomp) | (intros; apply GlobalTheory.JSW.MirPatch.cell_decomp  <;> assumption)
