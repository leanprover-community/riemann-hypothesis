module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalHeckeOperatorEqSmulOfLocalParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransport
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.SatInd

theorem guMap_comp_mem_hecke : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (n : ℕ) (h : Formalism.UG.GU σ' n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ' n) → (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) := by
  intro K _ _ g σ σ' hg hint n h hh
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [hg]
    simp
  let e : Formalism.UG.GU σ n ≃* Formalism.UG.GU σ' n :=
    { toFun := guMap g hg n
      invFun := guMap g.symm hg' n
      left_inv := fun y => guMap_symm_comp g hg hg' y
      right_inv := fun y => by
        have := guMap_symm_comp g.symm hg' (by simpa using hg) y
        simpa using this
      map_mul' := map_mul _ }
  have hK : ∀ y, y ∈ Formalism.UG.KU σ' n ↔ e.symm y ∈ Formalism.UG.KU σ n := by
    intro y
    rw [mem_KU_iff_guMap g hg hint (e.symm y)]
    change y ∈ Formalism.UG.KU σ' n ↔ e (e.symm y) ∈ Formalism.UG.KU σ' n
    rw [MulEquiv.apply_symm_apply]
  have := GlobalTheory.LFun.EigLoc.comp_symm_mem_hecke e.symm hK hh
  exact this

end GlobalTheory.SatInd
