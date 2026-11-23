module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem mem_levS_dat0_PsharpSym_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  intro D T Lc β ψ0 κ
  have hH : ∀ g : G0 Lc.Pg D.R.r, g ∈ (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ PP : ↥Lc.Pg, g PP ∈ unipSym (kP PP.1) D.R.r D.R.rS D.R.k := by
    intro g
    show g ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    simp
  refine ⟨?_, fun hκ => ?_⟩
  · rw [GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff, hH]
    simp only [GlobalTheory.SeeConjReord.r0]
    constructor
    · rintro ⟨⟨h0, h1, h2⟩, h3⟩
      exact ⟨h0, h1, h2, fun PP hPP => h3 ⟨PP, hPP⟩⟩
    · rintro ⟨h0, h1, h2, h3⟩
      exact ⟨⟨h0, h1, h2⟩, fun PP => h3 PP.1 PP.2⟩
  · have hm := ((GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff Lc _ β κ).1 hκ).2
    rw [GlobalTheory.SeeConjReord.principalRowLevelCharacter_trivial, extendOne_of_mem _ hm]
    letI : IsOneApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ => rfl⟩
    letI : IsMulApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
    erw [prod_apply, Units.coe_prod]
    rw [← Finset.prod_coe_sort Lc.Pg]
    rfl

end GlobalTheory.SeeConjRead
