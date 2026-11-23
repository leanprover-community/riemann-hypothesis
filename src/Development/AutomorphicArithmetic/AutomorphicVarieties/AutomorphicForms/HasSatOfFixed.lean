module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HasFixedVector
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG

namespace UpperTheory.V.Af

variable {F : Type} [Field F] [NumberField F]

private theorem sLoc_mem (w : HeightOneSpectrum (𝓞 F)) (x : Ov F w) : sLoc F w x ∈ Ohat F := by
  classical
  refine Subring.mem_iInf.2 fun v => ?_
  change (Pi.single w (x : w.adicCompletion F) : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) v ∈
    v.adicCompletionIntegers F
  by_cases h : v = w
  · subst h
    rw [Pi.single_eq_same]
    exact x.2
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

private def sInt (w : HeightOneSpectrum (𝓞 F)) : Ov F w →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w x, sLoc_mem w x⟩
  map_mul' x y := Subtype.ext (map_mul (sLoc F w) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (sLoc F w))
  map_add' x y := Subtype.ext (map_add (sLoc F w) x.1 y.1)

theorem LocIsotypic.hasFixed {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (Af F)) V} {w : HeightOneSpectrum (𝓞 F)}
    {σ : SmIrr (GL (Fin n) (w.adicCompletion F))} (h : LocIsotypic ρ w σ)
    {U : Subgroup (GL (Fin n) (w.adicCompletion F))} (hU : IsCompact (U : Set (GL (Fin n) (w.adicCompletion F))))
    (hf : HasFixed (ρ.comp (locGL F n w)) U) : HasFixed σ.ρ U :=
  _root_.UpperTheory.Reformulated.B.HasFixedVector.hasFixed h hU hf

end UpperTheory.V.Af
