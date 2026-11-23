module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSnapper
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeFiniteESt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistTildeSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeShiftSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanish
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem SnapperFinite.proof (hE : Extension.Statement.{u, v, w}) (hEL : Extension.Statement.{u, w, w})
    (hT : TwistTilde.Statement.{u, v, w}) (hTL : TwistTilde.Statement.{u, w, w})
    (hS : TildeShift.Statement.{u, v, w}) (hF : TildeFiniteE.Statement.{u, v, w}) :
    SnapperFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF0 t L n c i

  have hpow : ∀ (Lb : LineBundle k x) (m : ℕ), ∃ Q : FinGradedSub (S := k) (x := x) Ω,
      Lb.toSubSystem.pow m = Q.tildeSys 0 := by
    intro Lb m
    induction m with
    | zero =>
      refine ⟨coordGraded k x, ?_⟩
      change twistSys k x 0 = _
      rw [← coordGraded_tildeSys_twist (twistSys k x 0), SubSystem.twist_twistSys_zero]
    | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨QL, -, hQL⟩ := hEL k Ω N x Ω Lb.toSubFamily Lb.fg
      obtain ⟨P, -, hP⟩ := hTL k Ω N x Ω Q QL
      refine ⟨P, ?_⟩
      have hL : Lb.toSubSystem = QL.tildeSys 0 := SubSystem.ext_sub fun I => (hQL I).symm
      change (Lb.toSubSystem.pow m).twist Lb.toSubSystem = _
      rw [hQ, hL]
      exact SubSystem.ext_sub hP

  have hpows : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∃ P : FinGradedSub (S := k) (x := x) E,
        F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n = P.tildeSys 0 := by
    intro t
    induction t with
    | zero =>
      intro L n
      obtain ⟨M, -, hM⟩ := hE k Ω N x E F hF0
      exact ⟨M, SubSystem.ext_sub fun I => (hM I).symm⟩
    | succ t ih =>
      intro L n
      obtain ⟨P, hP⟩ := ih (fun j => L j.castSucc) (fun j => n j.castSucc)
      obtain ⟨Q, hQ⟩ := hpow (L (Fin.last t)) (n (Fin.last t))
      obtain ⟨P', -, hP'⟩ := hT k Ω N x E P Q
      refine ⟨P', ?_⟩
      change (F.toSubSystem.twistPows t (fun j => (L j.castSucc).toSubSystem)
        (fun j => n j.castSucc)).twist ((L (Fin.last t)).toSubSystem.pow (n (Fin.last t))) = _
      rw [hP, hQ]
      exact SubSystem.ext_sub hP'
  obtain ⟨P, hP⟩ := hpows t L n
  rw [hP, ← hS k Ω N x E P c]
  exact hF k Ω N x E P i c

end

end GroundTheory.Heights₂.Heights.Kleiman
