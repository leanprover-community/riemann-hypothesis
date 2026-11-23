module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Approx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.IsOpenMapVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestBump
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.gardSep :
    UpperTheory.V.Cj.H.GardSep := by
  open scoped Pointwise in
  intro E _ _ _ a μ _ _ W hW h
  rw [Submodule.eq_bot_iff]
  intro F hF
  refine approx (GA E a) (latticeGL E a) μ F fun U hU => ?_
  have hU' : (interior U)⁻¹ ∈ 𝓝 (1 : GA E a) := inv_mem_nhds_one _ (interior_mem_nhds.2 hU)
  obtain ⟨ψ, hψ, hpos, hne, hout⟩ := testBump E a {1} (interior U)⁻¹ isCompact_singleton isOpen_interior.inv
    (Set.singleton_subset_iff.2 (mem_of_mem_nhds hU'))
  have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
  have hc' : Continuous fun y => ψ.1 y⁻¹ := hc.comp continuous_inv
  have hs : HasCompactSupport fun y => ψ.1 y⁻¹ := hψ.1.comp_homeomorph (Homeomorph.inv (GA E a))
  refine ⟨fun y => ψ.1 y⁻¹, hc', hs, fun y => hpos _, by simpa using hne 1 rfl, fun y hy => hout _ ?_, ?_⟩
  · intro hh
    exact hy (interior_subset (by simpa using hh))
  · have e := (clFacts E a μ).2.2.2 ψ ⟨cv ψ.1 F, cvSm E a μ ψ hψ F⟩ F hψ rfl
    rw [← e]
    refine h _ (Submodule.subset_span ⟨ψ, F, hψ, rfl⟩) ?_
    rw [e]
    exact hW.Rop_mem (hc'.integrable_of_hasCompactSupport hs) hF
