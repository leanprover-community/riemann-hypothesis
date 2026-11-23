module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
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

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem frobProj_frobTwist_app {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (x : (frobTwist h G).A n) :
    ((frobProj h G).frobTwist h h).app n x = (frobProj h (frobTwist h G)).app n x := by
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add (f := _), hx, hy]
  | h1 r a =>
    rw [SemiBialgHom.smul_map, SemiBialgHom.smul_map, SemiHom.frobTwist_app_frobProj]

private theorem frobProj_app_verschiebung {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (a : G.A n) :
    (frobProj h (frobTwist h G)).app n ((verschiebung h G).app n a) =
      (verschiebung h (frobTwist h G)).app n ((frobProj h G).app n a) := by
  refine Test.mulP_injective (frobTwist h (frobTwist h G)) n ?_
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [← PDivGroup.res_app, ← SemiHom.res_app, ← SemiHom.res_app, ← PDivGroup.res_app,
    mulP_res, mulP_res, ← map_mulBy, ← SemiBialgHom.map_mulBy ((frobProj h G).app (n + 1)),
    ← relFrob_app_verschiebung_app h G, frobProj_app_relFrob_app,
    ← relFrob_app_frobProj h (G := frobTwist h G) (n + 1),
    ← prime_smul_id_app, ← verschiebung_comp_relFrob]
  rfl

theorem pow_char_eq_zero_of_verschiebung (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R ((frobTwist h G).A n))
    (hχ : ∀ a : G.A n, χ ((verschiebung h G).app n a) = 0) : χ ^ p = 0 := by
  refine CartierDual.ext_apply fun y => ?_
  induction y using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]
  | h1 r a =>
    rw [map_smul, ← frobTwistDual_verschiebung h (G := frobTwist h G) n χ,
      ← frobProj_app_verschiebung h G,
      frobTwistDual_frobProj, hχ, zero_pow (Fact.out : p.Prime).ne_zero, smul_zero]
    rfl

end GlobalTheory.PDivGroup
