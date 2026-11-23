module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEquivariantFormStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFrobeniusReciprocityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReductionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetEigenvectorExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReductionStatement
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

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun

namespace PositivityTheory.SphericalProduct

theorem extremeU : ExtremeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU hA hI hS
  obtain ⟨y, hy, hy1⟩ := GlobalTheory.T.unitary_jacquet_nonzero L ϖ σ q n V ρ α hU hA hI hS
  obtain ⟨y', ξ, hy', heig, h1⟩ := GlobalTheory.T.unitary_jacquet_eigenvector_exists L ϖ σ q n V ρ hU hA y hy hy1
  obtain ⟨lam, hlam0, hne, hlam⟩ := GlobalTheory.T.unitary_equivariant_form L ϖ σ q n V ρ hU hA ξ y' hy' heig h1
  obtain ⟨β, hβ⟩ := GlobalTheory.T.unitary_character_facts L ϖ σ q n V ρ hU ξ y' hy' heig h1
  obtain ⟨hW, f, hf, hfe⟩ := GlobalTheory.T.unitary_frobenius_reciprocity L ϖ σ q n V ρ α hU hA hI hS β lam hlam0 hne
    (fun t ht v => by rw [← hβ t ht]; exact hlam t ht v)
  exact GlobalTheory.T.unitary_chamber_decomposition GlobalTheory.T.unitary_swap_reduction GlobalTheory.T.unitary_inverse_reduction L ϖ σ q n hU V ρ hA hI hS.1 α β hW f hf hfe

end PositivityTheory.SphericalProduct

end
