module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
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

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwFockk

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain



theorem heightWN_of (hF : HWFin) (hI : HWInf) (hL : LstdStd) : PositivityTheory.PfSWUS.SwMatch.HeightWN := by
  intro D n H hH θ hθ nb hnb w hw
  refine ⟨lstd D.host.F D.host.E n, (hL D.host.F D.host.E n).1, fun d bs => (hL D.host.F D.host.E n).2 d bs, ?_⟩
  intro lam hlam b
  obtain ⟨p, hp, k, hk, hpk⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n (w * nb b)
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  have hH' : H (w * nb b) = absA D (Matrix.GeneralLinearGroup.det a) := by
    rw [hpk]; exact hH p hp a ha k hk
  have hX : ((H (w * nb b) : ℝ≥0) : ℝ) =
      ((∏ w' : NumberField.InfinitePlace D.host.F, GlobalTheory.Doubling.absEw D.host.F D.host.E w'
        (GlobalTheory.Doubling.unitInf D.host.F D.host.E w' (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ) *
      ∏ᶠ v, ((GlobalTheory.Doubling.absEv D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v
        (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ) := by
    rw [hH']
    change ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ≥0) : ℝ) = _
    rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul]
    congr 1
    exact MonoidHom.map_finprod_of_injective NNReal.toRealHom.toMonoidHom NNReal.coe_injective _
  have h1 := hI D n θ hθ w hw nb hnb b p k hp hk hpk a ha
  have h2 := fun v => hF D n w hw nb hnb b p k hp hk hpk a ha v (lam v) (hlam v)
  rw [hX, PositivityTheory.SiegelWeilFormula.Gen.nuA, finprod_congr h2, finprod_inv_distrib, mul_inv]
  congr 1
  exact (eq_inv_of_mul_eq_one_right h1).symm

end PositivityTheory.PfSWUS.SwFockk

end
