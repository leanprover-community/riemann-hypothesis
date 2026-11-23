module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal



theorem _root_.UpperTheory.KN.latticeTensorIncl_deRham_injective :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O), Function.Injective (TWincl (dRO l O) T) := by
  intro l _ O K _ _ _ _ _ _ _ T
  classical
  have h0 : Function.Injective (bdRpToBdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1
  have h1 : Function.Injective (dRO l O) := by
    intro r s h
    let b := Module.Free.chooseBasis ℤ_[l] O
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext k
    apply h0
    rw [← equivFinsuppOfBasisLeft_map_id, ← equivFinsuppOfBasisLeft_map_id]
    exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisLeft b y k) h
  intro w z h
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  apply (TensorProduct.equivFinsuppOfBasisRight bT).injective
  refine Finsupp.ext (fun j => ?_)
  apply h1
  rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
  exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) h
