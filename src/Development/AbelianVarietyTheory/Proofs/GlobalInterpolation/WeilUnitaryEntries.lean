module

public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchAllMembers
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.HeckeRamifiedZeroAll
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntegralAtT0Lattice
public import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.RL.DefSide


open Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory in
theorem full_rank {eps : ℝ} (Fm : FamP eps) (CH : ℝ) (tie : RealPlaceSecondLayerConditions Fm) (hTu : TuSize Fm) (hCh : ChosenE Fm 3 CH) :
    NuFullF Fm ∧ J.MuRank Fm := by
  have tT := (family_conditions_of_layer_two Fm tie).2.2
  have h := slope_free_branch_family Fm tT freeTT_holds slopeLineT_holds Formalism.L2.GlobalTheoryTheory.LemB.second_branch_all_members
  obtain ⟨hT2, hT5⟩ := Formalism.MainNotions.Wire.family_theorems_two_and_five Fm h.1 h.2.1 (hI_tied Fm tT PI.IntegralAtBasePointLattice.integral_at_t0_lattice)
    (tT.mono fun D u hS ht => Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.hecke_ramified_zero_all D u hS ht) h.2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, cPr, _⟩ := hCh
  exact muRank_items Fm 3 (by norm_num) hT2 hT5 hTu cPr

theorem wts_eq {X X' : Formalism.L2.Col.Fields} (h : X = X') {P : Formalism.L2.Col.Primes X} {P' : Formalism.L2.Col.Primes X'} (hP : HEq P P')
    {R R' : Ranks} (hR : R = R') : Formalism.L2.Col.Wts X P.Word R = Formalism.L2.Col.Wts X' P'.Word R' := by
  subst h; cases hP; subst hR; rfl

end GlobalTheory.Fc.RL.DefSide

end
