module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousToK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.IsoEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopPtAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.ValComapLtOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

theorem UpperTheory.V.Z.Kato.Sym.ptTop :
    UpperTheory.V.Z.Kato.Sym.PtTop := by
  intro Ω _ _ _ ε X l n M hl hM hd u v hu hv huF hvF
  obtain ⟨e, he⟩ := isoEx Ω ε X M
  obtain ⟨h1, h2⟩ := TopEta.spec_of_units X hM.ne' hl.ne_zero hd (isTopUnit X M hu huF) (isTopUnit X M hv hvF)
  have hη := isTopEta_topEta X M h1
  refine ⟨_, ptIs Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη, ptGam Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη,
    fun s hs => ?_⟩
  have hw := h2 (topLift X M s)⁻¹
  have h0 : wGen X M l n u v s ≠ 0 := fun h => hw.1 (Subtype.ext h)
  exact ⟨Units.mk0 _ h0, rfl, ptGal Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη s hs _ hw _ rfl⟩
