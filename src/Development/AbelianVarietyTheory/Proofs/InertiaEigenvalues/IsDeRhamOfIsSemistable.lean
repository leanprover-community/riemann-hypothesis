module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRhamStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistablePeriodMatrixOfIsSemistableStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfInvertiblePeriodMatrixStatement
import Mathlib.Algebra.Module.StablyFree.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem sst_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → IsDR (P.PD K) ρ := by
  intro l _ P AI T K V _ _ _ ρ hρ
  obtain ⟨ι, -, hι⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  let b := Module.finBasis ℚ_[l] V
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_semistable_period_matrix_of_isSemistable l P AI T _ K V b ρ hρ
  refine GlobalTheory.T.isDeRham_of_invertible_periodMatrix l P _ K V b ρ (Matrix.GeneralLinearGroup.map ι.toRingHom Q) ?_
  intro g
  have hmap : ((Matrix.GeneralLinearGroup.map ι.toRingHom Q : GL (Fin (finrank ℚ_[l] V)) P.R.BdR) :
      Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) P.R.BdR)
      = (Q : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P)).map ι := rfl
  have h := congrArg (fun M => M.map ι) (hQ g)
  simp only [Matrix.map_mul, Matrix.map_map] at h
  rw [hmap]
  conv_rhs => rw [← h]
  congr 1
  · ext i j
    exact (ι.commutes _).symm
  · rw [Matrix.map_map]
    congr 1
    funext x
    exact (hι _ x).symm

end GlobalTheory
