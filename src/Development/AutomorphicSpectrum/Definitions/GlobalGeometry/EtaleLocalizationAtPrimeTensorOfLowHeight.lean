module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
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

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

def Lat (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] : Type :=
  (p : Cpt ξ) → Submodule (regAt ξ p) E

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def IsFrameAt (L : Lat ξ E) {r : ℕ} (b : Fin r → E) (p : Cpt ξ) : Prop :=
  LinearIndependent Ω b ∧ L p = Submodule.span (regAt ξ p) (Set.range b)

def IsVBOn (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) : Prop :=
  ∀ p ∈ T, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧
    ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q

def IsVB (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) : Prop := L.IsVBOn Set.univ r V

def inter (L : Lat ξ E) (V : Submodule Ω E) : Lat ξ E := fun p => L p ⊓ V.restrictScalars (regAt ξ p)

def map (L : Lat ξ E) (f : E →ₗ[Ω] E') : Lat ξ E' := fun p => (L p).map (f.restrictScalars (regAt ξ p))

def comap (L : Lat ξ E') (f : E →ₗ[Ω] E') : Lat ξ E := fun p => (L p).comap (f.restrictScalars (regAt ξ p))

def scale (L : Lat ξ E) (a : Ω) : Lat ξ E := L.map (a • LinearMap.id)

def dual (L : Lat ξ E) : Lat ξ (Module.Dual Ω E) := fun p =>
  { carrier := {w | ∀ e ∈ L p, w e ∈ regAt ξ p}
    add_mem' := fun ha hb e he => by simpa using add_mem (ha e he) (hb e he)
    zero_mem' := fun e _ => by simp
    smul_mem' := fun c w hw e he => by
      show (c : Ω) * w e ∈ regAt ξ p
      exact mul_mem c.2 (hw e he) }

def wedge (L : Lat ξ E) (r : ℕ) : Lat ξ (⋀[Ω]^r E) := fun p =>
  Submodule.span (regAt ξ p) {w | ∃ b : Fin r → E, (∀ i, b i ∈ L p) ∧ w = exteriorPower.ιMulti Ω r b}

def IsChartOf (L : Lat ξ E) {κ : Type} (x : κ → Ω) (lat : κ → AddSubgroup E) : Prop :=
  ∀ c, x c ≠ 0 → ∀ e, e ∈ lat c ↔ ∀ p : Cpt ξ, InChart ξ x c p → e ∈ L p

def IsDegOn (L : Lat ξ E) (T : Set (Cpt ξ)) {K : Type} [Fintype K] {ι : K → Type} (y : (Σ k, ι k) → Ω)
    (a : K → ℤ) (e₀ : E) : Prop :=
  e₀ ≠ 0 ∧ ∀ p ∈ T, ∀ c : (k : K) → ι k, InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p →
    L p = Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a k) • e₀}

end Lat

def Dominates {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X' ⟶ X) (i : Ω →+* Ω') : Prop :=
  ξ' ≫ f = Spec.map (CommRingCat.ofHom i) ≫ ξ

def Lat.pull {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {F : Type} [AddCommGroup F] [Module Ω' F]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X)
    (j : E →+ F) : Lat ξ' F := fun p' =>
  Submodule.span (regAt ξ' p') {e' | ∃ (h : genPt ξ ⤳ f p'.1) (e : E), e ∈ L ⟨f p'.1, h⟩ ∧ e' = j e}

end GlobalTheory.CompanionTheory.Ar
