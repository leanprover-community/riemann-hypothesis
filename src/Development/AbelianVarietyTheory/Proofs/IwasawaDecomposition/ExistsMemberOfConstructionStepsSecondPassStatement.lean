module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberOfConstructionStepsSecondPass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl


theorem _root_.GlobalTheory.T.exists_member_of_construction_steps_secondPass : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM →
    ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
      ExportF KPx (IsBuiltE 𝒮) →
      Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) →
      StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' →
      (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  first | exact @GlobalTheory.Mem.Top.Bl.memberE_of_steps2 | exact GlobalTheory.Mem.Top.Bl.memberE_of_steps2 | (intros; apply GlobalTheory.Mem.Top.Bl.memberE_of_steps2 <;> assumption)

end GlobalTheory.Mem.Top.Bl
