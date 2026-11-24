module

public import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimitiveCentralIdempotentEqSimpleRepIdempotentStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.AdmDepthZero

theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → PairedCharacterCondition.admDZ P := by
  intro D P h i k v PI τ hτ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro hsq hu
  obtain ⟨ρ, hρ, he⟩ := GlobalTheory.T.primitiveCentralIdempotent_eq_simpleRepIdempotent (D.host.g k) D.R.r (P.lz k) τ
  have hO := PairedCharacterCondition.RT.ktyTie_of_spec P i PI k v τ hτ
  rw [he] at hO
  have hs : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k ((P.lz k).lab τ) =
      Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
    rw [← he]
    exact PairedCharacterCondition.RT.idem_mul_eSer P k τ
  exact h i k v PI ρ _ hρ hs hO hsq hu

end GlobalTheory.AdmDepthZero
