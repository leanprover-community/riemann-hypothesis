module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem adm5_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  classical
  intro D L P X C tf h i hi hl
  obtain ⟨h2, hq, hd, hg⟩ := hl
  have hqd : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by tauto
  have hR0 : 0 ≤ C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 := by
    have := h.pos
    positivity
  show (if D.nd.l i ∈ D.host.small then TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i
    else if D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d then TwistedPlaces.midG L C (D.nd.l i)
    else if KillingConditions.RangeAD L X.exc (D.nd.l i) then KillingConditions.supZ i (X.errorBoundHub i) else 0) ≤ _
  rw [if_neg h2, if_neg hqd]
  split_ifs with hR
  · unfold KillingConditions.supZ
    split_ifs with hne
    · exact Finset.sup'_le hne _ (fun π hπ => h.bb i hi hg hR π hπ)
    · exact hR0
  · exact hR0

end GlobalTheory.NLink
