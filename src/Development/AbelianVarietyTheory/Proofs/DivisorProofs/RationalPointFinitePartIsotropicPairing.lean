module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RatFinIso

variable {D : D7}

theorem symplOH_ratW_finRat_neg (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 := by
  set u : WO S T := ratW T S v - GlobalTheory.VacUnique.finRat S T v with hu
  have hfin : u.map (finPart D) = 0 := by
    funext i j
    have e1 := congrFun (congrFun (GlobalTheory.VacUnique.finRat_fin S T v) i) j
    show finPart D (ratW T S v i j - GlobalTheory.VacUnique.finRat S T v i j) = 0
    rw [RingHom.map_sub]
    simp only [Matrix.map_apply] at e1
    rw [e1, sub_self]
  have hr : ratW T S v = u + GlobalTheory.VacUnique.finRat S T v := by rw [hu, sub_add_cancel]
  rw [hr, GlobalTheory.FinTranslate.symplOH_add_left, map_neg, GlobalTheory.FinTranslate.symplOH_neg_right,
    GlobalTheory.FinTranslate.symplOH_neg_right, GlobalTheory.FinTranslate.symplOH_self,
    GlobalTheory.FinTranslate.symplOH_real_fin (GlobalTheory.VacUnique.finRat_inf S T v) hfin]
  simp

theorem isotropic : ∀ {D : D7} (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
    symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 :=
  fun S T v => symplOH_ratW_finRat_neg S T v

end GlobalTheory.RatFinIso

end
