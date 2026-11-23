module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakTop

theorem coords_algebraMap_smul {R O W T ι : Type} [CommRing R] [CommRing O] [Algebra R O]
    [CommRing W] [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R T) (c : R) (x : (O ⊗[R] W) ⊗[O] T) (i : ι) :
    coords W O b (algebraMap R O c • x) i = algebraMap R W c * coords W O b x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
    | tmul a w =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', coords_tmul, coords_tmul, smul_eq_mul,
        mul_smul, algebraMap_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul,
        Algebra.smul_def]

end GlobalTheory.WeakTop

theorem GlobalTheory.WeakClosed.continuous_zl_smul : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (m : TW (RW LL) T), letI := twTop T b; Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] ↥(OL LL) c • m := by
  intro l _ K LL T d b m
  letI := twTop T b
  letI := zlMod T
  haveI := zlTower T
  letI := cbTop l
  letI := cbValued l
  letI := wTop l
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) := GlobalTheory.WeakTop.continuous_padicInt_witt _
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  simp only [Function.comp_apply, GlobalTheory.WeakTop.coords_algebraMap_smul]
  exact hW.mul continuous_const
