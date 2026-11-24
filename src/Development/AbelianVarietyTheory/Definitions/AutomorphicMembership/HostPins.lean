module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.HD

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld NumberField IsDedekindDomain

def LevEx (D : D7) : Prop :=
  ∀ p, p ∈ D.host.levelPrimes ↔
    (∃ i, p = D.host.g i) ∨ p = D.host.pde ∨ p = D.host.pde' ∨ (∃ u, p = (D.mem u).A.T) ∨ p = q0Av D

def ExFld (B : Pre) (f : Fr B) (δ : FieldDat B) (F : IntermediateField ℚ ℂ) : Prop := F = listField δ f

def qb (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) : Fld := M.comap ι.toRatAlgHom

theorem mem_qb {ι : Qb →+* ℂ} {M : IntermediateField ℚ ℂ} {x : Qb} : x ∈ qb ι M ↔ ι x ∈ M := Iff.rfl

abbrev KC (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {GlobalTheory.Published.sqrtNegNat d}

structure HostPins (D : D7) (nch : NChoice D) : Prop where
  Tu_g : ∀ u i, (D.mem u).A.T ≠ D.host.g i
  fin : {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite
  Qw_Tu : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ nch.Q w, ∀ u, ¬ OverP D.host (D.mem u).A.T v
  gal : IsGalois ℚ D.what₂.LL
  hilb : ∃ M : IntermediateField ℚ ℂ, IsRayFieldIn D.host.φ₀ ⊤ M ∧
    ∀ z ∈ M, IsIntegral ℤ z → ∃ y : D.what₂.O, D.what₂.embLL (D.what₂.OtoLL y) = z

structure TupPins {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) : Prop where
  ram : ∀ μ v, ¬ (Tp.xi μ).UnrAt v → IsSplitPl D.host v ∧ (Ideal.absNorm v.asIdeal).Prime ∧
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ^ 2 ∧ ∀ k, ¬ OverP D.host (D.host.g k) v
  atl : ∀ w v, OverP D.host (D.what₂.places.resChar w) v → (Tp.xi (D.what₂.muAt w)).UnrAt v

end GlobalTheory.Mem.HD

end
