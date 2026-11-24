module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddingOfExponent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSocleProdIrrCongr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LOneSatakeBoundStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem expSat : PositivityTheory.SphericalProduct.ExpSat := by
  intro k _ _ _ _ _ n hd V _ _ π hs ha hirr ξ hξ hanti hv
  have hsm : ∀ a, IsSmoothChar (ξ a) := fun a => isSmoothChar_of_isUnram (hξ a)
  have hdeg : ∑ a, (IrrGL.ofChar (ξ a) (hsm a)).1 = n :=
    (Finset.sum_congr rfl fun _ _ => rfl).trans hd
  obtain ⟨f, hf⟩ := GlobalTheory.CompanionTheory.GlFrob.embedding_of_exponent k n hd V π hs ha hirr ξ hsm hdeg hv
  obtain ⟨⟨x, hx1, hxL⟩, hsoc⟩ := GlobalTheory.CompanionTheory.LocGL.socleOne k n ξ hξ hanti hdeg
  subst hx1
  have hS := hsoc _ x.rep hxL
  obtain ⟨e⟩ := hS.equiv_of_embeds hirr ⟨f, hf⟩
  have hL : IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) π := IsL.of_equiv hxL e.symm
  exact (GlobalTheory.T.l_one_satake_bound k _ ξ hξ V π hs).1 hL

end GlobalTheory.CompanionTheory.LocGL
