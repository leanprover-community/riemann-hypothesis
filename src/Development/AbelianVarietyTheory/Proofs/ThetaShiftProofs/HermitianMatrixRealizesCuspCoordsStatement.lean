module

public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

theorem _root_.GlobalTheory.T.hermitian_matrix_realizes_cusp_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ m : Fin (nZ X ρ) → ℤ, ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k := by
  first | exact @GlobalTheory.exists_isHermE_phZ_eq | exact GlobalTheory.exists_isHermE_phZ_eq | (intros; apply GlobalTheory.exists_isHermE_phZ_eq <;> assumption)
