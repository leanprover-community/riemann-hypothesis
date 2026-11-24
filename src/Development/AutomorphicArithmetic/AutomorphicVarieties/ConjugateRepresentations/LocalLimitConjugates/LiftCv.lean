module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.IsOpenMapVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.RopComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.liftCv :
    UpperTheory.V.Cj.H.LiftCv := by
  intro E _ _ _ a ha μ _ _ T hT T' hL ψ φ F hψ hφ
  obtain ⟨c1, c2, -, c4⟩ := clFacts E a μ
  have hφg : φ ∈ gard μ := Submodule.subset_span ⟨ψ, F, hψ, hφ⟩
  obtain ⟨g1, g2⟩ := hL φ hφg
  let φ' : Sm E a := ⟨cv ψ.1 (T F), cvSm E a μ ψ hψ (T F)⟩
  have hφ'g : φ' ∈ gard μ := Submodule.subset_span ⟨ψ, T F, hψ, rfl⟩
  have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
  have hint : Integrable (fun y => ψ.1 y⁻¹) μ :=
    (hc.comp continuous_inv).integrable_of_hasCompactSupport
      (hψ.1.comp_homeomorph (Homeomorph.inv (GA E a)))
  have e : cl μ (T' φ) = cl μ φ' := by
    rw [g2, c4 ψ φ F hψ hφ, c4 ψ φ' (T F) hψ rfl]
    exact ropComm _ _ μ T hT _ hint F
  have hd : (1 : ℂ) • T' φ + (-1 : ℂ) • φ' ∈ gard μ :=
    add_mem (Submodule.smul_mem _ _ g1) (Submodule.smul_mem _ _ hφ'g)
  obtain ⟨d1, d2, -⟩ := gardFacts E a ha μ _ hd
  have h0 := c2 _ d1 d2 (by
    rw [(c1 _ _ 1 (-1) (gardFacts E a ha μ _ g1).2.1 (gardFacts E a ha μ _ hφ'g).2.1).2, e]
    simp)
  have h1 : T' φ = φ' := by
    rw [one_smul, neg_one_smul, add_neg_eq_zero] at h0
    exact h0
  rw [h1]
