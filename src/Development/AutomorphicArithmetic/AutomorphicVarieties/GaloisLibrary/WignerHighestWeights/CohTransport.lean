module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasCohomologyTransport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.cohTransport :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ Ξ' : AlgRep E a) (T : (Fin Ξ.d → ℂ) ≃ₗ[ℂ] (Fin Ξ'.d → ℂ)),
      IsAlgIso Ξ Ξ' T → IsCohFor π Ξ → IsCohFor π Ξ' := by
  rintro E _ _ _ a π Ξ Ξ' T ⟨h1, h2⟩ H
  refine GlobalTheory.ConjCoh.hasCohomology_transport (σ := LinearMap.id) (s := id)
    (LinearEquiv.lTensor π.V T) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun k m => ?_) (fun X m => ?_) H
  · induction m using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v =>
      change π.op (.cpt k) φ ⊗ₜ[ℂ] T (Ξ.mat (Unitary.toUnits k) *ᵥ v) =
        π.op (.cpt k) φ ⊗ₜ[ℂ] (Ξ'.mat (Unitary.toUnits k) *ᵥ T v)
      rw [h1]
  · induction m using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v =>
      rw [GlobalTheory.GKCoh.tensorLie_tmul, map_add (f := _)]
      change π.op (.lie (toL X.1)) φ ⊗ₜ[ℂ] T v + φ ⊗ₜ[ℂ] T (Ξ.dmat (toL X.1) *ᵥ v) =
        π.op (.lie (toL X.1)) φ ⊗ₜ[ℂ] T v + φ ⊗ₜ[ℂ] (Ξ'.dmat (toL X.1) *ᵥ T v)
      rw [h2]
