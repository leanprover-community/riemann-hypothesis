module

public import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section Iso

variable {k G : Type*} [CommRing k] [Monoid G]

def Rep.isoOfBijective {A B : Rep.{u} k G} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    A ≅ B :=
  Rep.mkIso (Representation.IntertwiningMap.ofBijective f.hom hf)

end Iso

section ZMod

variable (G : Type*) [Monoid G]

abbrev zmodRep (n : ℕ) : Rep.{u} (ULift.{u} ℤ) G :=
  Rep.trivial (ULift.{u} ℤ) G (ULift.{u} (ZMod n))

end ZMod

attribute [local instance 2000] Rep.hV2

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

abbrev cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) : Rep.{u} (ULift.{u} ℤ) Gal(L/K) :=
  Rep.of (Representation.linHom M.ρ (galUnits.{u} K L).ρ)

variable {K L}

theorem cartierDual_ρ_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (σ : Gal(L/K))
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (m : M) :
    ((cartierDual K L M).ρ σ f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) m =
      (galUnits.{u} K L).ρ σ (f (M.ρ σ⁻¹ m)) :=
  rfl

variable (K L)

def evalBilin (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    M →ₗ[ULift.{u} ℤ] (M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) →ₗ[ULift.{u} ℤ] galUnits.{u} K L where
  toFun m :=
    { toFun := fun f => f m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' a b := LinearMap.ext fun f => f.map_add a b
  map_smul' r a := LinearMap.ext fun f => f.map_smul r a

def cartierPairing (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    M ⊗ cartierDual K L M ⟶ galUnits.{u} K L :=
  pairingHom (evalBilin K L M) fun σ m f => by
    change (galUnits.{u} K L).ρ σ (f (M.ρ σ⁻¹ (M.ρ σ m))) = (galUnits.{u} K L).ρ σ (f m)
    rw [Representation.inv_self_apply]

variable {K L}

@[simp]
theorem cartierPairing_tmul (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (m : M)
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) :
    (cartierPairing K L M).hom (m ⊗ₜ[ULift.{u} ℤ] (f : cartierDual K L M) :
      (M ⊗ cartierDual K L M : Rep _ _)) = f m :=
  pairingHom_tmul (A := M) (B := cartierDual K L M) (evalBilin K L M) _ m f

variable (K L)

variable {K L}

end GroundTheory.ProfCoh
