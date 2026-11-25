module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct

namespace GlobalTheory.StepLaw

variable {D : D7}

def ResAt (c : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP → ∀ x : (AE D)ˣ, e * ((x : AE D) - 1) = (x : AE D) - 1 →
    ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (u : (kP PP)ˣ),
      (u : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ → ((c x : Circle) : ℂ) = ((a u : ℂˣ) : ℂ)

def UnrOff (c : (AE D)ˣ →* Circle) (P : Finset (Pl D.host.E)) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ PP ∈ P, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → UnramAt ε c

theorem ResAt.mul {c c' : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a a' : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a)
    (h' : ResAt c' PP a') : ResAt (c * c') PP (a * a') := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  have k' := h' e he x hex hx u hu
  simp only [MonoidHom.mul_apply, Circle.coe_mul, Units.val_mul, k, k']

theorem ResAt.inv {c : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a) :
    ResAt c⁻¹ PP a⁻¹ := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  simp only [MonoidHom.inv_apply, Circle.coe_inv, Units.val_inv_eq_inv_val, k]

theorem UnrOff.mul {c c' : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) (h' : UnrOff c' P) :
    UnrOff (c * c') P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.mul_apply, h v ε hε hv x h₁ h₂ h₃, h' v ε hε hv x h₁ h₂ h₃, one_mul]

theorem UnrOff.inv {c : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) :
    UnrOff c⁻¹ P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.inv_apply, h v ε hε hv x h₁ h₂ h₃, inv_one]

end GlobalTheory.StepLaw

end
