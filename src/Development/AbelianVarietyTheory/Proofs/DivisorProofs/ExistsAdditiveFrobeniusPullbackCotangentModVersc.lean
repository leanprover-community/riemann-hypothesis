module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveWithCotangentOfDualHeightOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCharEqZeroOfKillsVerschiebung
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    [HopfAlgebra R A] [HopfAlgebra R C] (f : C →ₐc[R] A) : (kerIdeal f).IsHopfIdeal R := by
  apply GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom <;> assumption

theorem isCocomm_of_surjective {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f : A →ₐc[R] B)
    (hf : Function.Surjective f) : IsCocomm R B := by
    refine ⟨LinearMap.ext fun b => ?_⟩
    obtain ⟨a, rfl⟩ := hf b
    have h1 := CoalgHomClass.map_comp_comul_apply f a
    have h2 := TensorProduct.map_comm (f : A →ₗ[R] B) (f : A →ₗ[R] B) (comul (R := R) a)
    have h3 := Coalgebra.comm_comul R a
    show TensorProduct.comm R B B (comul (f a)) = comul (f a)
    rw [← h1, ← h2, h3]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

theorem exists_cobOne_relFrob_eq_zero_dUnit_eq (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) (w : Cot K ((frobTwist h G).A 1)) :
    ∃ (β : (frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((relFrob h G).app 1 β) = 0 ∧
        dUnit (R := K) β = w + cotMap ((verschiebung h G).app 1) w' := by
    have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h
    let V := (verschiebung h G).app 1
    let F := (relFrob h G).app 1
    let J : Ideal ((frobTwist h G).A 1) := kerIdeal V
    have : J.IsHopfIdeal K := GlobalTheory.PDiv.isHopfIdeal_kerIdeal V
    let π : (frobTwist h G).A 1 →ₐc[K] (frobTwist h G).A 1 ⧸ J := Bialgebra.Quotient.mkBialgHom J
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    have hπker : RingHom.ker π = J := Ideal.Quotient.mkₐ_ker K J
    have : IsCocomm K ((frobTwist h G).A 1 ⧸ J) := GlobalTheory.PDiv.isCocomm_of_surjective π hπ
    have : Module.Finite K ((frobTwist h G).A 1 ⧸ J) :=
      Module.Finite.of_surjective (π : (frobTwist h G).A 1 →ₗ[K] _) hπ

    have hπV : ∀ a : G.A 1, π (V a) = algebraMap K _ (counit (R := K) a) :=
      (kerIdeal_le_ker_iff V (AlgHom.ofClass π)).mp hπker.ge

    have hdual : ∀ φ ∈ augIdeal K (CartierDual K ((frobTwist h G).A 1 ⧸ J)), φ ^ p = 0 := by
      intro φ hφ
      have hφ1 : φ 1 = 0 := by
        have : counit (R := K) φ = 0 := by simpa using hφ
        simpa using this
      have hχ : (CartierDual.map π φ) ^ p = 0 := by
        apply pow_char_eq_zero_of_verschiebung p K h G 1
        intro a
        rw [CartierDual.map_apply, hπV, Algebra.algebraMap_eq_smul_one]
        change φ.ofConv (counit (R := K) a • 1) = 0
        rw [map_smul]
        change counit (R := K) a • φ 1 = 0
        rw [hφ1, smul_zero]
      have hχ' : CartierDual.map π (φ ^ p) = 0 := by rw [map_pow]; exact hχ
      apply CartierDual.ext_apply
      intro x
      obtain ⟨a, rfl⟩ := hπ x
      have := congrArg (fun χ : CartierDual K ((frobTwist h G).A 1) => χ a) hχ'
      simp only [CartierDual.map_apply] at this
      simpa using this
    obtain ⟨b, hb0, hbw⟩ :=
      exists_primitive_dUnit_eq p K ((frobTwist h G).A 1 ⧸ J) hdual (cotMap π w)
    obtain ⟨β, rfl⟩ := hπ b

    have hker : RingHom.ker π ≤ RingHom.ker F := by
      rw [hπker]
      exact app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul p K (frobTwist h G) G
        (verschiebung h G) (relFrob h G) (relFrob_comp_verschiebung h G)
    have hFβ : F β = liftSurj π hπ F hker (π β) := (liftSurj_apply π hπ F hker β).symm

    obtain ⟨w', hw'⟩ := (exact_cotMap hπ V hπker (dUnit (R := K) β - w)).mp (by
      rw [map_sub, cotMap_d, hbw, sub_self])
    refine ⟨β, w', ?_, ?_⟩
    · rw [hFβ, ← pullTwo_cobOne, hb0, map_zero]
    · rw [hw']
      abel

end GlobalTheory.PDivGroup
