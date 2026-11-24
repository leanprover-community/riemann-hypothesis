module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLEpsPairMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelParabolicConjInvTranspose
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_siegelParabolic_conj_invTranspose : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
    p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
    ∀ g : GA D (GlobalTheory.Doubling.dblSp S), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp S) g =
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1ᵀ →
    ∃ h : GlobalTheory.Doubling.siegel S, GlobalTheory.DiagThetaRule.epsD S * g = (h : GA D (GlobalTheory.Doubling.dblSp S)) * GlobalTheory.DiagThetaRule.epsD S ∧
      GlobalTheory.Doubling.aP S h = GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t) := by
  first | exact @GlobalTheory.SiegelTransposeInverse.exists_siegel_conj | exact GlobalTheory.SiegelTransposeInverse.exists_siegel_conj | (intros; apply GlobalTheory.SiegelTransposeInverse.exists_siegel_conj <;> assumption)
