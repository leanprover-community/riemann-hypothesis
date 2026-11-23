module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiInvariantConjugacyClassesFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairTermEqCentraliserOrbitSumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DformRelEquivalence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatZeroFromResolutionAndGaga
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

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem GlobalTheory.LKDef.Regroup.regroup :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 :=
  GlobalTheory.LKDef.Regroup.regroup_main GlobalTheory.LKDef.DFormPos.sim_pos GlobalTheory.T.bi_invariant_conjugacy_classes_finite GlobalTheory.T.definitePair_term_eq_centraliser_orbit_sum
