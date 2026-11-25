module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

noncomputable section

namespace UpperTheory.Lit.Car

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def IneAb {w : PlE H} (y : A.LP w) : Prop :=
  ∀ σ ∈ ⁅Ine (F := H.E) (N.plOm.1 w), Ine (F := H.E) (N.plOm.1 w)⁆, A.inePol y σ = (X - 1) ^ A.lpDim y

structure RelA {w : PlE H} (x y : A.LP w) : Prop where
  dim : A.lpDim x = A.lpDim y
  mono : A.mono0 y → A.mono0 x
  ine : IneAb N A y → ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol x σ = A.inePol y σ

structure Cusp {w : PlE H} (x y : A.LP w) : Prop where
  rel : RelA N A x y
  temp : Odd (A.lpDim y) → ∀ s : ℝ, A.tempered (A.lpTw y s) → A.tempered (A.lpTw x s)
  one : A.lpDim y = 1 → x = y

variable {N A}

theorem comm_le_ine (w : PlE H) :
    ⁅Ine (F := H.E) (N.plOm.1 w), Ine (F := H.E) (N.plOm.1 w)⁆ ≤ Ine (F := H.E) (N.plOm.1 w) :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem eq_pow_of_mul {p q : ℂ[X]} (hp : p.Monic) {n : ℕ} (h : p * q = (X - 1) ^ n) : p = (X - 1) ^ p.natDegree := by
  have hirr : Prime (X - C (1 : ℂ)) := prime_X_sub_C 1
  have hd : p ∣ (X - C (1 : ℂ)) ^ n := ⟨q, by simpa using h.symm⟩
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow hirr n).1 hd
  have e : p = (X - C (1 : ℂ)) ^ k := eq_of_monic_of_associated hp ((monic_X_sub_C 1).pow k) hk
  have : p.natDegree = k := by rw [e, natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [this, e]; simp

theorem inePol_char_unr (hLP : TieLP N A) {w : PlE H} (a c : A.LP w) (hc : A.lpDim c = 1) (hu : A.unr c) :
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.lpChar a c) σ = A.inePol a σ := fun σ hσ => by
  have e : A.inePol c σ = X - C 1 := by rw [((A.unr_iff_ine c).1 hu).2 σ hσ, hc]; simp
  rw [((hLP w a a c c 0 hc hc).2.2.2.2.2 σ hσ).2 1 e, scaleRoots_one]

variable (N A)

def GaloisRepresentationsWeak : Prop :=
  ∀ i, (∀ a, 1 ≤ a → ∀ π : A.CG a, A.csd π → A.ralg π →
      ∃ ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)),
        Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) ∧
        IsSSRep ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) →
          A.wdOf i ρ w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2) ∧ A.tempered (A.locG π w)) ∧
        (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧
          (∀ τ, InducesW N i τ w → A.jumpsW i ρ τ = A.jumpsInf i π τ) ∧
          Cusp N A (A.wdOf i ρ w) (A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2)))) ∧
    (∀ a (π : A.CG a), A.ralg π → ∃ w₀ : ℂ, ∀ τ : H.E →+* ℂ,
      A.infG π (τ.comp (H.conj : H.E ≃ₐ[ℚ] H.E).toRingEquiv.toRingHom) = (A.infG π τ).map (w₀ - ·)) ∧
    (∀ (χ : A.CG 1) (s : ℝ), (∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) →
      ∃ ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)), ContQ N i ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i ρ w = A.lpTw (A.locG χ w) s) ∧
        ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧ A.wdOf i ρ w = A.lpTw (A.locG χ w) s ∧
          ∀ τ, InducesW N i τ w → (A.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
            (A.infG χ ((A.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ))))

end UpperTheory.Lit.Car
