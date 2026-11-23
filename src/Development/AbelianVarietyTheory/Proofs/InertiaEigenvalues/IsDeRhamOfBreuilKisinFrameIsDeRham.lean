module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisDeRhamBreuilKisinStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfInvertiblePeriodMatrix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem isDR_of_frame_isDR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsDR → Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hF
  obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  obtain ⟨B, Q, -, hQ, -, -, hinv⟩ := GlobalTheory.T.exists_invariant_basis_deRham_breuilKisin l K bk τ hτ C N d (fun g => (ρ g).val) F Y hF hY
  have hQ' : IsUnit (T.eD.symm.mapMatrix Q) := hQ.map T.eD.symm.mapMatrix
  refine GlobalTheory.PMon.isDR_of_periodMatrix l P (Fin d) K (Fin d → ℚ_[l]) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hQ'.unit ?_
  intro g
  have hg := hinv g
  simp only [IsUnit.unit_spec]
  ext i j
  apply T.eD.injective
  have hij := congrFun (congrFun hg i) j
  rw [LinearMap.toMatrix_eq_toMatrix']

  simp only [qRep, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, RingEquiv.mapMatrix_apply] at hij ⊢
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, Units.coeHom_apply, RingHom.mapMatrix_apply, AlgEquiv.coe_toAlgHom, Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix'_toLin',
    Matrix.map_apply, T.actD, RingEquiv.apply_symm_apply] at ⊢
  rw [← hij]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have e : LinearMap.toMatrix' (Matrix.toLinAlgEquiv' ((algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]))) =
      (algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) :=
    LinearMap.toMatrix'_toLin' _
  erw [e]
  exact T.zD ((ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) i x)

end GlobalTheory.BKLim
