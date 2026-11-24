module

public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem csEquiv_bc_mulVec (γ : GL n E) (x : n → E) :
    (((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i))) =
      fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((γ : Matrix n n E) *ᵥ x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem csEquiv_mem (Λ : Submodule (𝓞 E) (n → E)) (γ : GL n E)
    (g k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)) (x : n → E) :
    x ∈ globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k) Λ ↔
      ((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x ∈ globLat g Λ := by
  have hki := (stabGL _).inv_mem hk
  show (((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k)⁻¹ :
      GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
    ((g⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x) i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← map_inv, csEquiv_bc_mulVec]
  exact (hki _).symm

theorem csEquiv_main (Λ : Submodule (𝓞 E) (n → E)) (γ : GL n E)
    (g k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)) :
    globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k) Λ =
      Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat g Λ) := by
  ext x
  rw [csEquiv_mem Λ γ g k hk x]
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact hy

end

theorem global_lattice_equiv_holds : Formalism.UG.CS.GlobLatEquiv := by
  intro F E _ _ _ _ _ n _ _ Λ γ g k hk
  exact csEquiv_main Λ γ g k hk

end Formalism.UG.P
