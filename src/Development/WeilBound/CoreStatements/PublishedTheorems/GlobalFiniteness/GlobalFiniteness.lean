module

public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1UnramifiedOutside
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.FiniteH2TorsionModule
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Transport
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

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GF

theorem globalFiniteness : ReciprocityTheory.Gal.GlobalFiniteness := by
  intro F Ω _ _ _ _ _ l hl r M _ _ _ _ _ S rhoS hr hS hc
  obtain ⟨A, _, hAf, hn, ⟨e1⟩, ⟨e2⟩, en⟩ := PositivityTheory.Lit1.GFTransport.cohDict S rhoS hc
  refine ⟨?_, ?_, ?_, fun hl2 n hn3 => ?_⟩
  · exact Finite.of_injective (fun x : H0 rhoS => (x : M)) Subtype.val_injective
  · have := GlobalTheory.CompanionTheory.GSFin.finite_cohomology_one F Ω l r S hS A hAf hn
    exact Finite.of_equiv _ e1.toEquiv.symm
  · have := PositivityTheory.Lit1.GFParts.finite_H2_torsion_module F Ω l r S hS A hAf hn
    exact Finite.of_equiv _ e2.toEquiv.symm
  · have := PositivityTheory.Lit1.GFParts.subsingleton_hn F Ω l r S hS hl2 A hAf hn n hn3
    obtain ⟨e⟩ := en n
    exact e.toEquiv.subsingleton

end PositivityTheory.Lit1.GF
