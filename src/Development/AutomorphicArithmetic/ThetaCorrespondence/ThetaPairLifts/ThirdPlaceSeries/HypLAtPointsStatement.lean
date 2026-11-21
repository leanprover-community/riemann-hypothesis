import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegreeHypothesisAllMembersStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegreeHypothesisAllMembers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceLowerBoundAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceLowerBoundAllMembers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankMuOfBundle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceUpperBoundAllMembersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceUpperBoundAllMembers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Core.LevLow
theorem levelPrime_lower_at_points_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∀ u : D.what₂.Word, O.L.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr D u) := by
  intro hL p
  have hA : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => LocalBesselAndTopKernel.FamilyMidVolume D) :=
    RowE.of_all fun _ K β _ b _ _ _ =>
      admissibleRanks_of_mass_formula β.D β.O.ex.lev b.R.T.toTiedDataS.cols (Dstar_mass K β.X β.c.isOver β.c.dsig_eq)
  exact (EvP.and (RowE.and hA (_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked hL p)) eventually_le_trace).mono
    fun _ _ _ H β hq c b hl => H.2 β (H.1 β hq c b hl).1 (H.1 β hq c b hl).2
end GlobalTheory.Core.LevLow
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_lower_bound_all_members' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∀ u : D.what₂.Word, O.L.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr D u) := by
  atlas_forward_decl _root_.GlobalTheory.Core.LevLow.levelPrime_lower_at_points_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
theorem levelPrime_le_at_points_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
      (fun κ D O _ _ => ∀ u : D.what₂.Word, Formalism.MainNotions.S.Tr D u ≤ O.L.sc.b ^ (κ.C.CTu * (D.R.m : ℝ))) := by
  intro hL p
  exact eventually_trace_le.mono fun _ _ _ H β _ _ _ _ => H β
end GlobalTheory.LevelPrimeUpper
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_upper_bound_all_members' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ => ∀ u : D.what₂.Word, Formalism.MainNotions.S.Tr D u ≤ O.L.sc.b ^ (κ.C.CTu * (D.R.m : ℝ))) := by
  atlas_forward_decl _root_.GlobalTheory.LevelPrimeUpper.levelPrime_le_at_points_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.HypAt
theorem hypL_at_points_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (A B : Formalism.MainNotions.Inhab.FC → ℝ), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ => GlobalTheory.Core.Deg.HypL D O.L.sc.L (max (A κ.C) (8 * κ.C.CGam)) (max (B κ.C) 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2) κ.C.CTu) := by
  intro hL p A B
  exact (EvP.and (RowE.and (_root_.GlobalTheory.T.trace_lower_bound_all_members' hL p) (_root_.GlobalTheory.T.trace_upper_bound_all_members' hL p)) (evP_hypL A B)).mono fun _ _ _ H β hq c b hl =>
    H.2 β fun u => ⟨(H.1 β hq c b hl).1 u, (H.1 β hq c b hl).2 u⟩
end GlobalTheory.Core.HypAt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degHypL_all_linked_good_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (A B : Formalism.MainNotions.Inhab.FC → ℝ), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ => GlobalTheory.Core.Deg.HypL D O.L.sc.L (max (A κ.C) (8 * κ.C.CGam)) (max (B κ.C) 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2) κ.C.CTu) := by
  atlas_forward_decl _root_.GlobalTheory.Core.HypAt.hypL_at_points_alt
end
end
