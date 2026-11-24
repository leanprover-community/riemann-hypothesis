module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV Formalism.ConjugateSelfDual

namespace UpperTheory.V.Th.Nm

variable {l : ℕ} [Fact l.Prime] {n : ℕ}

def IntM (Z : Matrix (Fin n) (Fin n) (Qbar l)) : Prop := ∀ i j, ‖Z i j‖ ≤ 1

def InO (c : Coef l) (Z : Matrix (Fin n) (Fin n) (Qbar l)) : Prop := ∀ i j, Z i j ∈ c.O

def cj {G K : Type} [Group G] [CommRing K] (Q : GL (Fin n) K) (ρ : G →* GL (Fin n) K) : G →* GL (Fin n) K :=
  (MulAut.conj Q⁻¹).toMonoidHom.comp ρ

theorem cj_apply {G K : Type} [Group G] [CommRing K] (Q : GL (Fin n) K) (ρ : G →* GL (Fin n) K) (g : G) :
    cj Q ρ g = Q⁻¹ * ρ g * Q := by
  show Q⁻¹ * ρ g * Q⁻¹⁻¹ = Q⁻¹ * ρ g * Q
  rw [inv_inv]

def OrdAt (F : GFrame l) {K : Type} [CommRing K] (ρ : F.G₀ →* GL (Fin n) K) (v : F.Vl) (ψ : Fin n → F.Gv v →* Kˣ)
    (z : F.G₀ → Matrix (Fin n) (Fin n) K) (w : GL (Fin n) K) (Y : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ g : F.Gv v,
    (∀ i j, j < i → (w⁻¹ * ρ (F.φ v g) * w : GL (Fin n) K) i j = 0) ∧
    (∀ i, (w⁻¹ * ρ (F.φ v g) * w : GL (Fin n) K) i i = (ψ i g : K)) ∧
    (∀ i j, j < i → (((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) K)) i j = 0) ∧
    (g ∈ F.Iv v → ∀ i, (((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) K)) i i = 0)

structure OCoc {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (y : Pt F O n)
    (z : F.G₀ → Matrix (Fin n) (Fin n) O) : Prop where
  cont : ∀ i j, AdicCont (maximalIdeal O) fun g => z g i j
  coc : ∀ g g', z (g * g') = z g + mat y.ρ g * z g' * mat y.ρ g⁻¹
  pol : ∀ g, (y.P : Matrix (Fin n) (Fin n) O) * z (F.conj g) = -((z g)ᵀ * y.P)
  ine : ∀ u, ∀ g ∈ F.Iu u, z g = 0
  ord : ∀ v, ∃ Y, OrdAt F y.ρ v (y.ψ v) z (y.w v) Y

def shrink {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {I : F.St → Subgroup F.G₀}
    (y : Pt (reIu F I) O n) (I' : F.St → Subgroup F.G₀) (h : ∀ u, I' u ≤ I u) : Pt (reIu F I') O n :=
  ⟨y.ρ, y.cont, y.P, y.sgn, y.form, y.span, fun u g hg => y.ine u g (h u hg), y.ψ, y.w, y.tri, y.reg, y.N1⟩

def inc {c c' : Coef l} (h : c.O ≤ c'.O) : c.O →+* c'.O := (Subalgebra.inclusion h).toRingHom

def RPush {F : GFrame l} {c c' : Coef l} (h : c.O ≤ c'.O) (r : Resid F c.O n) (r' : Resid F c'.O n) : Prop :=
  ∃ f : ResidueField c.O →+* ResidueField c'.O, (∀ a, f (residue c.O a) = residue c'.O (inc h a)) ∧
    (∀ i, r'.chib i = pushCh f (r.chib i)) ∧ (∀ v i, r'.psib v i = pushCh f (r.psib v i)) ∧
    ∀ v i, r'.th v i = pushCh (inc h) (r.th v i)

def IsModel {F : GFrame l} {c : Coef l} (y : Pt F c.O n) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l))
    (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) : Prop :=
  pushRep (algebraMap c.O (Qbar l)) y.ρ = ρ ∧ GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P = P ∧
    ∀ v i, pushCh (algebraMap c.O (Qbar l)) (y.ψ v i) = ψ v i

end UpperTheory.V.Th.Nm
