module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.RingFacts

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

theorem monic_Q (a : S → O) : (∏ s, (X - Polynomial.C (a s)) : O[X]).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)

theorem lin_eq (a : S → O) (s : S) :
    lin a s = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X]) (X - Polynomial.C (a s)) := by
  simp [lin, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem cofac_eq (a : S → O) (τ : S) :
    cofac a τ = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X])
      (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => lin_eq a s

theorem ev_mk (a : S → O) (τ : S) (f : O[X]) :
    ev a τ (AdjoinRoot.mk _ f) = f.eval (a τ) := by
  simp [ev]

theorem exists_lin_mul_of_ev_eq_zero (a : S → O) (τ : S) (r : RS a) (hr : ev a τ r = 0) :
    ∃ r', r = lin a τ * r' := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [ev_mk] at hr
  obtain ⟨h, hh⟩ := (Polynomial.dvd_iff_isRoot).2 hr
  exact ⟨AdjoinRoot.mk _ h, by rw [hh, map_mul, lin_eq]⟩

theorem eq_algebraMap_add_lin_mul (a : S → O) (τ : S) (r : RS a) :
    ∃ g, r = algebraMap O (RS a) (ev a τ r) + lin a τ * g := by
  obtain ⟨g, hg⟩ := exists_lin_mul_of_ev_eq_zero a τ (r - algebraMap O (RS a) (ev a τ r))
    (by rw [map_sub, AlgHom.commutes]; simp)
  exact ⟨g, by rw [← hg]; ring⟩

theorem lin_mul_cofac (a : S → O) (τ : S) : lin a τ * cofac a τ = 0 := by
  rw [cofac, Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Finset.prod_congr rfl
    (fun s _ => lin_eq a s), ← map_prod]
  exact AdjoinRoot.mk_self

theorem ev_cofac (a : S → O) (τ : S) :
    ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => ev_lin a τ s

theorem eq_smul_cofac_of_lin_mul_eq_zero [IsDomain O] (a : S → O) (τ : S) (r : RS a)
    (hr : lin a τ * r = 0) : ∃ c : O, r = algebraMap O (RS a) c * cofac a τ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [lin_eq, ← map_mul, AdjoinRoot.mk_eq_zero] at hr
  obtain ⟨g, hg⟩ := hr
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), mul_assoc] at hg
  have hf : f = (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) * g :=
    mul_left_cancel₀ (X_sub_C_ne_zero (a τ)) hg
  obtain ⟨h, hh⟩ := eq_algebraMap_add_lin_mul a τ (AdjoinRoot.mk _ g)
  refine ⟨ev a τ (AdjoinRoot.mk _ g), ?_⟩
  have hc := lin_mul_cofac a τ
  calc AdjoinRoot.mk _ f = cofac a τ * AdjoinRoot.mk _ g := by rw [hf, map_mul, cofac_eq]
    _ = cofac a τ * (algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) + lin a τ * h) := by
        rw [← hh]
    _ = algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) * cofac a τ
        + (lin a τ * cofac a τ) * h := by ring
    _ = _ := by rw [hc]; simp

theorem ring_facts : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S]
    (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧
    lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧
    (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧
    (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧
    (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  intro O _ _ S _ _ a τ
  let pb := AdjoinRoot.powerBasis' (monic_Q a)
  exact ⟨Module.Free.of_basis pb.basis, pb.finite, lin_mul_cofac a τ, ev_cofac a τ,
    exists_lin_mul_of_ev_eq_zero a τ, eq_algebraMap_add_lin_mul a τ (cofac a τ),
    eq_smul_cofac_of_lin_mul_eq_zero a τ⟩

end GlobalTheory.RingFacts
