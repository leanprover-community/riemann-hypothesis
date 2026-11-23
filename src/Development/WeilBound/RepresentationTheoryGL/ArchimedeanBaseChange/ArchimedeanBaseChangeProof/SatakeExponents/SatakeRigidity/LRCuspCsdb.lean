module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig.B

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infChar_conj {a : ℕ} (P : CuspSub E a) (hn : IsNormalised P) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : P.HasInfChar τ m) (hm' : P.HasInfChar (ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have := h1
  have := h2
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a μ P hn
  exact GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq E a P B hB τ m m' hm hm'

end PositivityTheory.Rg.BcB.F.Rig.B

end
