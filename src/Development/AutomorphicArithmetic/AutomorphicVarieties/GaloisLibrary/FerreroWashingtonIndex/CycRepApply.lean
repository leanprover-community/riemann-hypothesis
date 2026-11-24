module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
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

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick

namespace UpperTheory.V.FW

abbrev Cl (K : Type) [Field K] [NumberField K] : Type := ClassGroup (𝓞 K)

section Cyc

variable (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L]

def clA (t : (ZMod M)ˣ) : Cl L →* Cl L := clMap (sg M L t)⁻¹.toRingEquiv

def cycRep : Representation ℤ (ZMod M)ˣ (Additive (Cl L)) :=
  (clRep L).comp (((sg M L).toMonoidHom).comp invMonoidHom)

theorem cycRep_apply (t : (ZMod M)ˣ) (x : Cl L) :
    cycRep M L t (Additive.ofMul x) = Additive.ofMul (clA M L t x) := by
  rw [cycRep, MonoidHom.comp_apply, MonoidHom.comp_apply, invMonoidHom_apply, MulEquiv.coe_toMonoidHom, map_inv, clRep_apply]
  rfl

def embT (φ : L →+* ℂ) (t : (ZMod M)ˣ) : L →+* ℂ := φ.comp (sg M L t).toRingEquiv.toRingHom

end Cyc

section Sign

variable {K ι : Type} [Field K] [NumberField K]

def sgn (e : ι → K →+* ℂ) (a : K) : ι → ZMod 2 := fun i => if (e i a).re < 0 then 1 else 0

def sgnE [IsCMField K] (e : ι → K →+* ℂ) : AddSubgroup (ι → ZMod 2) :=
  AddSubgroup.closure {f | ∃ u : (𝓞 K)ˣ, cE K ((u : 𝓞 K) : K) = ((u : 𝓞 K) : K) ∧ f = sgn e ((u : 𝓞 K) : K)}


variable (K) in
def UnrFin : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield K)) = 1

end Sign

end UpperTheory.V.FW

end
