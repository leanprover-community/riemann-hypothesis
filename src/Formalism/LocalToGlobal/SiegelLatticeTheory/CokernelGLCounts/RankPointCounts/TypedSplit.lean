module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
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
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneDir

variable {D : D7} (Zd : LocDat D)

theorem typed_split (p : PlF D) {g : Formalism.MainNotions.S.Loc.SplitG (Zd.M p).L} (hs : (Zd.M p).split = some g) :
    ∃ sg, (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
  have h := (Zd.agree p).2.2.2.2.2
  rw [hs] at h
  cases hsg : (D.s.atP p).split with
  | none => rw [hsg] at h; exact h.elim
  | some sg => rw [hsg] at h; exact ⟨sg, rfl, h.1, h.2⟩

theorem gS_mem_of_split (p : PlF D) {sg} (hsg : (D.s.atP p).split = some sg) :
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := fun P hP =>
  (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P hP).2 (by rw [← D.s_split p, hsg]; rfl)

end OneDir

end Formalism.L2.SG.Pf.FibQ
