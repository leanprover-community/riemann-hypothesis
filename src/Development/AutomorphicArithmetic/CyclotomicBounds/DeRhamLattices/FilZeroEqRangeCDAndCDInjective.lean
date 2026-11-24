module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per



private theorem mem_FilD_zero (l : ℕ) [Fact l.Prime] (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x :=
  ⟨fun h => let ⟨z, _, e⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l (n := 0) h; ⟨z, e⟩,
    fun ⟨y, e⟩ => e ▸ GlobalTheory.RingIface.alg_mem_FilD_zero l y⟩

theorem _root_.UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (K : FinExt l), (∀ x : Pl.R.BdR, x ∈ (Pl.PD K).Fil 0 ↔ ∃ y : Per.BdRp l, x = GlobalTheory.BKGal.JumpDR.cD Td y) ∧ Function.Injective (GlobalTheory.BKGal.JumpDR.cD Td) := by
  intro l _ Pl AI Td K
  refine ⟨fun x => ?_, fun y z h => ?_⟩
  · rw [Td.fil, mem_FilD_zero]
    refine exists_congr fun y => ?_
    change _ ↔ x = Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y)
    rw [RingEquiv.eq_symm_apply, eq_comm]
  · exact (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 (Td.eD.symm.injective h)
