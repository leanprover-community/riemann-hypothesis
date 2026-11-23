module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionFrameOfMatrixForm
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.decompletion_frame_of_matrix_form : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsActC act → IsGen χ K m g → (∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m)) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ) → (∀ i j, ‖D i j‖ ≤ 1) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ ≤ 1) ∧ D * X = (l : PadicComplex l) • (1 : Matrix (Fin d) (Fin d) (PadicComplex l))) → (∀ σ ∈ Gj K m, ∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, X i j ∈ intC (Ks K m)) ∧ M σ * D.map (act σ) = D * X) → (∀ σ ∈ Hinf K, M σ * D.map (act σ) = D) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ < rho1 l) ∧ M g * D.map (act g) - D = D * X) → ∃ U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l), IsDec act χ K m M D U g := by
  first | exact @GlobalTheory.Cyc.Decomp.isDec_of_matrix | exact GlobalTheory.Cyc.Decomp.isDec_of_matrix | (intros; apply GlobalTheory.Cyc.Decomp.isDec_of_matrix <;> assumption)
