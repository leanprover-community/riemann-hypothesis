module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsTer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombination
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowCombGood

theorem comb_good : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ C, IsRealFam ch.W C → ∀ c : Combs ch.G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) →
    Good ch.W (combC ch.W c C) (combR ch.rm c) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro C hC c _
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  have hL := s.core.lev
  refine ⟨fun j hje hj => ?_, fun i => ?_⟩
  · obtain ⟨k, hk⟩ := D.R.m_even
    obtain ⟨l, hl⟩ := hje
    obtain ⟨hv, hs⟩ := hC j ⟨l, hl⟩ hj
    have h1 : IsBiTheta ch.W.ψ _ _ _ (C j) :=
      GlobalTheory.FrComb.biTheta_of_vac (node_isV ch.G hL (X := .top j) (show j ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega)).sd hv hs
    exact GlobalTheory.FrCombAny.biTheta_biComb D _ hψ _ _ _ _ h1 _ _
  · exact GlobalTheory.CombThetaAny.main D _ hψ _ _ _ _ (ch.rm.vX_is i D.R.m i.2 le_rfl).2.theta

end GlobalTheory.RowCombGood
