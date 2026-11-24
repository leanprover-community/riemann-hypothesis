module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedUnramifiedTowerBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobFixedLatticeConditionSmulOfFrobeniusFixedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeDegreeOneStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBdRPlusUnitMatrixRestrictionLatticeMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRestrictionLatticeColumnStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndependStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegreeStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem flAt_all : ∀ r : ℕ, FLAt r := by
  intro r l _ P AI T n _ _ U x y hxy hU hc
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact x.1.elim0
  obtain ⟨E, ω, -, -, -, hω, hlin, hspan, hdet⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l r hr
  have hdet' : (frobMat ω).det ≠ 0 := hdet
  have hxy' : ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) ≠ (0, (y.2, y.1)) := by
    intro h
    apply hxy
    simp only [Prod.mk.injEq, true_and] at h
    exact Prod.ext h.2 h.1
  obtain ⟨A₀, hA₀, hW⟩ := GlobalTheory.T.fundamentalLemmaLattice_degreeOne l P AI T (n × Fin r) (fun _ => U0 P ω hdet' U) _ _ hxy'
    (fun _ => GlobalTheory.T.isBdRPlusUnitMatrix_restrictionLatticeMatrix l P r ω hdet' n U hU) (GlobalTheory.T.linearIndependent_restrictionLattice_column l P r ω hω hdet' n U x hc)
  obtain ⟨W₀, hW₀, heq⟩ := hW 0
  have he : ∀ j : n × Fin r, eps ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) (0, (y.2, y.1)) (0, j) = eps x y (j.2, j.1) := by
    intro j
    simp only [eps, Prod.mk.injEq, true_and, Prod.ext_iff]
    grind
  have heq' : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet' U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    simpa [he] using heq
  have hA₀' : ∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun i j => by simpa using hA₀ i j
  have h3 := GlobalTheory.T.restrictionLattice_columns_condition_linearIndependent l P r ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq'
  obtain ⟨a, -, -, hsp⟩ := GlobalTheory.T.exists_frobeniusFixed_unramified_tower_basis l r ω hω hlin hspan (n → P.R.B) n (colv P ω A₀) h3.2
    (fun e he c => GlobalTheory.T.mem_span_restrictionLattice_columns l P r hr ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq' _ (GlobalTheory.T.frobFixedLatticeCondition_smul_of_frobenius_fixed l P r n U x y _ e he (h3.1 c)))
  exact GlobalTheory.T.exists_frobeniusFixed_matrix_units_of_lattice_basis l P r ω hω hdet' n U x y hU A₀ hA₀' W₀ hW₀ heq' a hsp

end GlobalTheory.PMon

end
