module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

theorem UpperTheory.V.Z.Kato.Sym.PT.isoEx :
    UpperTheory.V.Z.Kato.Sym.PT.IsoEx := by
  intro Ω _ _ _ ε X M
  let L := topL X M
  let L' : IntermediateField Ω X.K :=
    { L with algebraMap_mem' := fun c => algebraMap_mem_lev X _ c }
  let F : IntermediateField Ω X.K := IntermediateField.adjoin Ω {X.jK}
  have hFL : F ≤ L' :=
    IntermediateField.adjoin_simple_le_iff.mpr (jK_mem_lev X _)
  have hle : F.toSubfield ≤ L := fun x hx => hFL hx
  letI : Algebra F L := (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower F L X.K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic L X.K :=
    ⟨fun f => (X.alg_j f).tower_top L⟩
  haveI : IsAlgClosure L (Kb X) := IsAlgClosure.ofAlgebraic L X.K (Kb X)
  let e : topBar X M ≃ₐ[L] Kb X := IsAlgClosure.equiv L (topBar X M) (Kb X)
  refine ⟨e.toRingEquiv, fun f => ?_⟩
  change e (algebraMap L (topBar X M) f) = algebraMap X.K (Kb X) (f : X.K)
  rw [AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply L X.K (Kb X) f
