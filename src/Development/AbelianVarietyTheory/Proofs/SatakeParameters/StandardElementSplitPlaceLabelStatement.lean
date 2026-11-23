module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardElementSplitPlaceLabel
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.standardElement_splitPlace_label : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ} (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E) (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ → ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E), Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧ Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧ Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := by
  first | exact @GlobalTheory.StdEltLabel.std_elt_label | exact GlobalTheory.StdEltLabel.std_elt_label | (intros; apply GlobalTheory.StdEltLabel.std_elt_label <;> assumption)
