module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

theorem conjLoc_exists_split (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host) (h : IsConjPl D.host w s.w) :
    ∃ s' : SplitPlace D.host.E, s'.w = w := by
  have hc : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => by
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact Formalism.HC.HostAx.conjE_apply _ _ _
  refine ⟨⟨s.v, s.i.comp (IsCMField.complexConj D.host.E).toAlgHom⟩, ?_⟩
  apply HeightOneSpectrum.ext
  ext x
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [hc]; rfl
  rw [h x _ hy]
  exact Iff.rfl

theorem conjLoc (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host)
    (h : IsConjPl D.host w s.w) : ∃ x, GlobalTheory.AutQuot.LocAt π w x := by
  obtain ⟨s', rfl⟩ := conjLoc_exists_split D s w h
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV π s'
  exact ⟨_, s', σ, rfl, hσ, HEq.rfl⟩

end GlobalTheory.AutQuot
