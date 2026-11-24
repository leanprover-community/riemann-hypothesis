module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FischerInnerFormFockSubstitutionUnitaryInvariant
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Links

theorem _root_.GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := by
  first | exact @GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | exact GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | (intros; apply GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary <;> assumption)
