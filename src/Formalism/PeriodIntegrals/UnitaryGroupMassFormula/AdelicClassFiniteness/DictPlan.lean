module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StGenusOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

def DInj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Function.Injective (Formalism.UG.inclE (F := F) (E := E) (Af F))

def DInter : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (e : E),
    Formalism.UG.inclE (F := F) (Af F) e ∈ IntAf F E → e ∈ (algebraMap (𝓞 E) E).range

def DDenom : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (r : E ⊗[F] Af F),
    ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Af F) * r ∈ IntAf F E

def DDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ r ∈ IntAf F E, ∃ a : 𝓞 E, ∃ r' ∈ IntAf F E,
      r = Formalism.UG.inclE (F := F) (Af F) (a : E) + (N : E ⊗[F] Af F) * r'

def iv (I : AutInst) (v : Fin I.n → I.E) : Fin I.n → I.E ⊗[I.F] Af I.F :=
  fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (v i)

def hhat (I : AutInst) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) : I.E ⊗[I.F] Af I.F :=
  Formalism.UG.hform (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) y z

def LInter : Prop := ∀ (I : AutInst) (v : Fin I.n → I.E), iv I v ∈ I.Lf → v ∈ I.L

def LDenom : Prop :=
  ∀ (I : AutInst) (y : Fin I.n → I.E ⊗[I.F] Af I.F), ∃ m : ℕ, 0 < m ∧ (m : I.E ⊗[I.F] Af I.F) • y ∈ I.Lf

def LDense : Prop :=
  ∀ (I : AutInst) (N : ℕ), 0 < N → ∀ y ∈ I.Lf, ∃ l ∈ I.L, ∃ y' ∈ I.Lf, y = iv I l + (N : I.E ⊗[I.F] Af I.F) • y'

def LHatInt : Prop := ∀ (I : AutInst), ∀ y ∈ I.Lf, ∀ z ∈ I.Lf, hhat I y z ∈ IntAf I.F I.E

def LHatDual : Prop :=
  ∀ (I : AutInst) (z : Fin I.n → I.E ⊗[I.F] Af I.F), (∀ y ∈ I.Lf, hhat I y z ∈ IntAf I.F I.E) → z ∈ I.Lf

def abelian₂ (I : AutInst) (x : I.Gf) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := {v | I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf}
  add_mem' := fun {v w} hv hw => by
    have e : iv I (v + w) = iv I v + iv I w := by
      funext i; simp [iv]
    show I.fmat x⁻¹ *ᵥ iv I (v + w) ∈ I.Lf
    rw [e, Matrix.mulVec_add]
    exact I.Lf.add_mem hv hw
  zero_mem' := by
    have e : iv I (0 : Fin I.n → I.E) = 0 := by
      funext i; simp [iv]
    show I.fmat x⁻¹ *ᵥ iv I 0 ∈ I.Lf
    rw [e, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  smul_mem' := fun a v hv => by
    have ha : Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) ∈ IntAf I.F I.E :=
      Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)
    have e : iv I (a • v) = Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • iv I v := by
      funext i
      simp [iv, Algebra.smul_def]
    show I.fmat x⁻¹ *ᵥ iv I (a • v) ∈ I.Lf
    rw [e, Matrix.mulVec_smul]
    exact I.Lf.smul_mem ⟨_, ha⟩ hv

def MLat : Prop :=
  ∀ (I : AutInst) (x : I.Gf), (abelian₂ I x).FG ∧ Submodule.span I.E ((abelian₂ I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = ⊤

def MGen : Prop :=
  ∀ (I : AutInst) (x : I.Gf), ∀ y ∈ I.Lf,
    I.fmat x *ᵥ y ∈ Submodule.span (IntAf I.F I.E) (Set.range fun v : abelian₂ I x => iv I (v : Fin I.n → I.E))

def MDual : Prop := ∀ (I : AutInst) (x : I.Gf), SelfDual I.J (abelian₂ I x)

def MInj : Prop := ∀ (I : AutInst) (x y : I.Gf), abelian₂ I x = abelian₂ I y → ∃ k ∈ I.Kset, y = x * k

def MEquiv : Prop :=
  ∀ (I : AutInst) (γ : GL (Fin I.n) I.E), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J →
    ∃ c ∈ GFf I, I.fmat c = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) ∧
      ∀ x, IsImg γ (abelian₂ I x) (abelian₂ I (c * x))

theorem stDict_of (h1 : MLat) (h2 : MDual) (h3 : MInj) (h4 : MEquiv) : StDict :=
  fun I => ⟨abelian₂ I, fun x => ⟨(h1 I x).1, (h1 I x).2, h2 I x⟩, h3 I, h4 I⟩

end PIW.AdelClassFin
