module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubOrthogonal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

theorem exists_orthProj_polyV {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (p : KG ε → ℂ) (hp : Continuous p) :
    ∃ p' ∈ GlobalTheory.KFourier.polyV ε d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d,
      ∫ k, star (q k) * (p k - p' k) ∂(muK ε) = 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV
  | exact _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV
  | (apply _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV ..)

end GlobalTheory.KFourier

end
