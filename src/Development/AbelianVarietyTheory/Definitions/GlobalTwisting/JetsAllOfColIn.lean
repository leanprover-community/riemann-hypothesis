module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StepBoxIffStepSuppDeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPowClassNumber
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

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory.KerT



open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem hyp_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (a : I.ι) (u : B.Word) :
    Hyp I.dat (seamOf B C W V S N G) ⊤ I.J.δ I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u := by
  have hJ := (I.J.ok_iff B C W V S N G).1 h.amb_ok
  refine ⟨GlobalTheory.T.definiteBaseData_admissible B X I.Ch h.ch_ok h.fromHecke, ⟨seamOf_ok B C W V S N G, rfl, ⟨top_ne_bot, by simp⟩, hJ.1,
    ChiIdeal.isChi_chiId _ _ I.C.isChi, hJ.2⟩, fun 𝔞 _ => (ChiVal.chi_values B X I h).2 𝔞, h.sel_ok, ?_, fun _ hl => h.small_mem hl, fun _ _ => by simp,
    (h.idx_ok a).cst_ok, I.C.mu0, I.C.eta, h.ch_tied, (h.idx_ok a).muqG⟩
  rintro p ((rfl | rfl | rfl | rfl | rfl) | ⟨u, rfl⟩)
  exacts [h.two_q_d_mem.1, h.two_q_d_mem.2.1, h.two_q_d_mem.2.2, h.g_mem 0, h.g_mem 1, h.T_mem u]


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem jetsAll_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn) (a : I.ι) (u : B.Word) {i : ℕ} (hi : i < B.R.m) :
    JetsAll (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B C W V S N G) (I.J.toRec B C W V S N G) I.chi I.J.cD) u i (i + 1) := by
  have hP := (hyp_of_colIn B C W V S N G I h a u).ok.primes
  rw [← AmbIn.amb_eq_ambOf]
  intro L L' hL hL'
  exact (GlobalTheory.MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) L L').2
    (GlobalTheory.MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (GlobalTheory.MoveCompare.cBof_pos hP _ _ _ u) hL hL')

end GlobalTheory.KerT
