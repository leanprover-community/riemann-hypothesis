module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eq_one_of_smul [IsGalois ℚ E] {v : Pl F} (hv : SplitsFully E v) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (g : Gal(E/ℚ)) (h : g • P = P) : g = 1 := by
  haveI : P.LiesOver (v.asIdeal.under ℤ) := ⟨by rw [P.over_def v.asIdeal, Ideal.under_under]⟩
  have h1 := MulAction.index_stabilizer Gal(E/ℚ) P
  rw [Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 E) Gal(E/ℚ) (v.asIdeal.under ℤ) P, hv,
    ← IsGalois.card_aut_eq_finrank] at h1
  have h2 := (MulAction.stabilizer Gal(E/ℚ) P).card_mul_index
  rw [h1] at h2
  have h3 : Nat.card (MulAction.stabilizer Gal(E/ℚ) P) = 1 :=
    (mul_left_eq_self₀.1 h2).resolve_right Nat.card_pos.ne'
  exact (Subgroup.mem_bot).1 (Subgroup.card_eq_one.1 h3 ▸ (MulAction.mem_stabilizer_iff.2 h))

def conjQ (h : IsCMExt F E σ) : Gal(E/ℚ) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (σ : E →+* E)
    (Function.Involutive.bijective (f := σ) (cm_conj_conj h))) fun x => by simp

theorem conjQ_apply (h : IsCMExt F E σ) (x : E) : conjQ h x = σ x := rfl

end PositivityTheory.KCo
