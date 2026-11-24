module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsThetaModStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSideStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainOfStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.JoinExists
theorem main_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Nonempty (_root_.GlobalTheory.NPin.CharacterChoiceJoin P) := by
  intro h1 h2 hL D P X hA
  have key : ∀ i : D.nd.Loc, ∃ Y : RowMod D P.rep (D.nd.j i),
      ∀ (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), GlobalTheory.NJoin.IsCanon X j hj Y := by
    intro i
    have hr := D.nd.j_range i
    have hlt : D.nd.j i - 1 < D.R.m := by omega
    obtain ⟨Y, hY⟩ := _root_.GlobalTheory.T.exists_canonical_module_at_successor h1 h2 hL D P X hA ⟨D.nd.j i - 1, hlt⟩ (D.nd.j i) (by simp only; omega)
    refine ⟨Y, fun j hj => ?_⟩
    have hj' : j = ⟨D.nd.j i - 1, hlt⟩ := Fin.ext (by simp only; omega)
    subst hj'
    exact hY
  choose Y hY using key
  exact ⟨{ form := _root_.GlobalTheory.T.mtForm_of_realAt_agree hL D P X hA
           rowM := Y
           th := fun i j hj => (_root_.GlobalTheory.T.nonempty_theta_mod_of_is_canon h1 h2 hL D P X hA i j hj (Y i) (hY i j hj)).some }⟩
end GlobalTheory.JoinExists
end
