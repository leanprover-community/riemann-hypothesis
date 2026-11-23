module

public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.HermitianLattices.HermitianLatticesProofs.MajDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

structure Coord (hc : CMData F E) (S : HSpace E) (n : Type) [Fintype n] where
  κ : S.V ≃ₗ[E] (n → E)
  J : Matrix n n E
  form : ∀ x y, S.hT x y = hform (hc.sig : E →+* E) J (κ x) (κ y)

variable {hc : CMData F E} {S : HSpace E}

def Coord.lat (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (n → E) :=
  L.map ((K.κ : S.V →ₗ[E] (n → E)).restrictScalars (𝓞 E))

theorem Coord.mem_lat (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) (y : n → E) : y ∈ K.lat L ↔ K.κ.symm y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show K.κ.symm (K.κ x) ∈ L
    rwa [LinearEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, K.κ.apply_symm_apply y⟩

theorem Coord.lat_dual (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) :
    K.lat (Formalism.HermitianLatticesTheory.dual S.hT L) = dl hc.sig K.J (K.lat L) := by
  ext y
  rw [K.mem_lat, Formalism.HermitianLatticesTheory.dualBasic_mem_dual, mem_dl]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    have h1 := h x hx
    rw [K.form, LinearEquiv.apply_symm_apply] at h1
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
    exact ⟨r, hr⟩
  · intro h x hx
    have h1 := h (K.κ x) ⟨x, hx, rfl⟩
    rw [K.form, LinearEquiv.apply_symm_apply]
    obtain ⟨r, hr⟩ := h1
    exact Submodule.mem_one.2 ⟨r, hr⟩

theorem Coord.isLat_lat (K : Coord hc S n) {L : Submodule (𝓞 E) S.V} (hL : Submodule.IsFullLattice E L) :
    IsLat (K.lat L) := by
  refine ⟨Module.Finite.iff_fg.2 (hL.fg.map _), ?_⟩
  rw [eq_top_iff]
  intro y _
  have h1 : K.κ.symm y ∈ Submodule.span E (L : Set S.V) := by rw [hL.span_eq_top]; trivial
  have h2 : K.κ (K.κ.symm y) ∈ (Submodule.span E (L : Set S.V)).map (K.κ : S.V →ₗ[E] (n → E)) := ⟨_, h1, rfl⟩
  rw [LinearEquiv.apply_symm_apply, Submodule.map_span] at h2
  exact h2

theorem star_int (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨⟨_, Formalism.HermitianLatticesTheory.majDual_star_int r⟩, rfl⟩

end Formalism.L2.GlobalTheoryTheory.Comp

end
