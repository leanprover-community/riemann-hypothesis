module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodEigSumSupComplEigSumEqTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.Divisibility.ClassSum
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.goodEigSum_sup_compl_eigSum_eq_top : ∀ (D : D7) (i : D.nd.Loc), ZRat D (D.nd.mu i) (D.nd.j i) → SpecPr D i → D.nd.eigSum i ↑(D.nd.Zgood i) ⊔ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ = ⊤ := by
  first | exact @GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top | exact GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top | (intros; apply GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top <;> assumption)
