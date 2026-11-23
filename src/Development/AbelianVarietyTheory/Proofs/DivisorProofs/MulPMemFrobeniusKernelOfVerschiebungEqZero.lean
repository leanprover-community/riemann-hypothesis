module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
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

@[expose] public section

set_option autoImplicit false

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_of_verschiebung_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (a : G.A 1) (ha : (verschiebung h G).app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) := by
  let f := (G.mulP 1).comp ((relFrob h G).app 1)
  let K := kerIdeal f
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff f x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp ((relFrob h G).app 2 : (frobTwist h G).A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal (R := R) (A := (frobTwist h G).A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff (mulBy R ((frobTwist h G).A 2) p) y).2 fun z => by
      change x ((relFrob h G).app 2 (mulBy R ((frobTwist h G).A 2) p z)) = _
      rw [← (frobTwist h G).mulP_res 1 z, PDivGroup.app_mulP (relFrob h G)]
      simpa only [f, BialgHom.coe_comp, Function.comp_apply, CoalgHomClass.counit_comp_apply]
        using hx ((frobTwist h G).res 1 z)
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app (verschiebung h G)] at ha
  have hb : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) p := by
    have : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) (p ^ 1) := by
      rw [← (frobTwist h G).ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x ((relFrob h G).app 2 ((verschiebung h G).app 2 b)) = 0 := hy hb
  rw [relFrob_app_verschiebung_app] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup
