module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Formalism.LocalToGlobal.HermitianForms.BothSym
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.MemberCount

theorem rankMu_of_cols (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D) (hDu : StandardLattice.FactDuStar D)
    (u : D.what₂.Word) : GlobalTheory.Core.Rk.RankMu D u := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  have hr := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
    (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
  have hfin : Module.finrank ℂ (D.s.Cu u) = Module.finrank ℂ (D.mem u).A.Mu0 := (D.s_Cu u).finrank_eq
  unfold GlobalTheory.Core.Rk.RankMu GlobalTheory.Core.Rk.d0
  rw [hfin, hDu u]
  exact hr

end GlobalTheory.Fam.MemberCount
