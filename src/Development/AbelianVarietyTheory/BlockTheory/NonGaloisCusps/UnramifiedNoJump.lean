module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

section Conj

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {c : Ω ≃+* Ω}

theorem conj_conj (hc : IsCMConjOm E Ω c) (x : Ω) : c (c x) = x := by
  obtain ⟨⟨j, hj⟩, -⟩ := hc
  apply j.injective
  rw [hj, hj]
  simp

theorem conj_symm (hc : IsCMConjOm E Ω c) (x : Ω) : c.symm x = c x := by
  rw [RingEquiv.symm_apply_eq, conj_conj hc]

def conjElt (hc : IsCMConjOm E Ω c) (g : G E Ω) : G E Ω :=
  AlgEquiv.ofRingEquiv (f := (c.symm.trans g.toRingEquiv).trans c) (fun x => by
    obtain ⟨y, hy⟩ := hc.2 x
    change c (g (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
    rw [conj_symm hc, hy, AlgEquiv.commutes, ← hy, conj_conj hc])

theorem conjElt_apply (hc : IsCMConjOm E Ω c) (g : G E Ω) (x : Ω) :
    conjElt hc g x = c (g (c.symm x)) := rfl

def conjHom (hc : IsCMConjOm E Ω c) : G E Ω →* G E Ω where
  toFun := conjElt hc
  map_one' := by
    ext x
    simp [conjElt_apply]
  map_mul' g h := by
    ext x
    simp [conjElt_apply]

end Conj

section Rep

variable {Γ : Type} [Group Γ] {A : Type} [CommRing A] {n : ℕ}

def scalGL : Aˣ →* GL (Fin n) A :=
  Units.map (Matrix.scalar (Fin n) : A →+* Matrix (Fin n) (Fin n) A).toMonoidHom

theorem scalGL_comm (a : Aˣ) (M : GL (Fin n) A) : Commute (scalGL a) M := by
  apply Units.ext
  exact (Matrix.scalar_commute (a : A) (fun b => mul_comm _ b) (M : Matrix (Fin n) (Fin n) A)).eq

def twist (ρ : Γ →* GL (Fin n) A) (χ : Γ →* Aˣ) : Γ →* GL (Fin n) A where
  toFun g := scalGL (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (scalGL (χ h)),
      (scalGL_comm (χ h) (ρ g)).eq, mul_assoc]

def transGL (M : GL (Fin n) A) : GL (Fin n) A where
  val := (M : Matrix (Fin n) (Fin n) A).transpose
  inv := ((M⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

def dual (ρ : Γ →* GL (Fin n) A) : Γ →* GL (Fin n) A where
  toFun g := transGL (ρ g⁻¹)
  map_one' := by
    apply Units.ext
    simp [transGL]
  map_mul' g h := by
    apply Units.ext
    simp only [transGL, mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul]

def IsoLat (ρ ρ' : Γ →* GL (Fin n) A) : Prop :=
  ∃ P : GL (Fin n) A, ∀ g, P * ρ g = ρ' g * P

end Rep

variable (D : _root_.Formalism.BasicNotions.D7)

def cycField (l : ℕ) : IntermediateField D.host.E D.nd.Om :=
  IntermediateField.adjoin D.host.E {x : D.nd.Om | x ^ l = 1}

def UnramifiedIn (l : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ^ 2

def NC (l : ℕ) : Prop :=
  l = 2 ∨ UnramifiedIn D l ∨ D.R.t * D.R.r < Module.finrank D.host.E ↥(cycField D l)

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

end
