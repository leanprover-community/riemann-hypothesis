module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleProjectionExists
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

theorem UpperTheory.Reformulated.B.IsoSeparation.isoSep :
    ∀ {H M : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : IsTopologicalGroup H] [inst_3 : AddCommGroup M]
      [inst_4 : _root_.Module ℂ M] {ρ : Representation ℂ H M} {Y : Submodule ℂ M} {σ : GlobalTheory.CuspRep.SmIrr H},
      UpperTheory.V.Hi.IsoSum ρ Y σ →
        ∀ {F : M},
          F ∈ Y →
            F ≠ (0 : M) →
              ∃ (p : M →ₗ[ℂ] σ.V),
                (∀ (g : H),
                    ∀ y ∈ Y,
                      (p : M → σ.V) (((ρ : H → M →ₗ[ℂ] M) g : M → M) y) =
                        ((σ.ρ : H → σ.V →ₗ[ℂ] σ.V) g : σ.V → σ.V) ((p : M → σ.V) y)) ∧
                  (p : M → σ.V) F ≠ (0 : σ.V) := by
  intro H M _ _ _ _ _ ρ Y σ h F hF h0
  cases σ with
  | mk V ρ' hs hi => exact UpperTheory.irreducible_projection_exists ρ' ρ hi Y h hF h0
