module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMtMulLeftAdelicMatrixHaarEqStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulRightUnitaryAdelicMatrixAddHaarStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem actO_map_haar : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (μ : Measure (WO S T)),
    μ.IsAddHaarMeasure → μ.map (actO S T g h) = μ := by
  intro D S T g h μ hμ
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hL : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) :=
    continuous_const.matrix_mul continuous_id
  have hR : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) :=
    continuous_id.matrix_mul continuous_const
  have e : actO S T g h =
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) ∘
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) := rfl
  rw [e, ← Measure.map_map hR.measurable hL.measurable, GlobalTheory.T.map_mt_mul_left_adelicMatrix_haar_eq D T S.rank h μ hμ]
  exact GlobalTheory.T.map_mul_right_unitaryAdelicMatrix_addHaar D S T.rank g⁻¹ μ hμ

end GlobalTheory
