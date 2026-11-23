module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexFiniteNonzero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volume_index_finite_of_hyps (D : D7) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hyps : Hyps D u u' F0 what₂)
    (hC : Commens) (hSt : StClosed) (hDel : DeltaAE D δ M)
    (hAin : AinSt D u u' F0 what₂ δ M) (hAbdd : ABddOf D u u' F0 what₂ δ M) (hAcong : ACong D u u' F0 what₂ δ M)
    (hBin : BinSt D u u' F0 what₂ δ M) (hBbdd : BBdd D u u' F0 what₂ δ M) (hBcong : BCong D u u' F0 what₂ δ M) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.VolumeIndexFiniteNonzero D u u' F0 what₂ δ M := by
  intro hAg t w F' L U hr hg hN hG
  exact ⟨hC _ _ _ _ _ (hAin hSt hyps hAg t w F' L U hr hg hN hG) (hAbdd hDel hyps hAg t w F' L U hr hg hN hG)
      (hBcong hyps hAg t w F' L U hr hg hN hG),
    hC _ _ _ _ _ (hBin hSt hyps hAg t w F' L U hr hg hN hG) (hBbdd hyps hAg t w F' L U hr hg hN hG)
      (hAcong hyps hAg t w F' L U hr hg hN hG)⟩

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
