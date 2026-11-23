module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundarySemistableTensorColumns
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.coboundary_semistableTensor_columns : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  first | exact @GlobalTheory.PMonCob.coboundary_cols | exact GlobalTheory.PMonCob.coboundary_cols | (intros; apply GlobalTheory.PMonCob.coboundary_cols <;> assumption)
