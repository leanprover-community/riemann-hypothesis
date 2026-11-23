module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinPointIdeal
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar joinCoord mcIdeal mcMap)

namespace JoinPointIdeal

noncomputable section

variable {K : Type} {ι : K → Type}

def joinIdx : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Unit ⊕ (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => .inr ⟨k, i⟩
    | ⟨.inr _, _⟩ => .inl ()
  invFun
    | .inr p => ⟨.inl p.1, p.2⟩
    | .inl _ => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨(k | ⟨⟩), i⟩
    · rfl
    · show (⟨.inr (), (0 : Fin 1)⟩ : Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) = ⟨.inr (), i⟩
      congr 1
      exact (Fin.fin_one_eq_zero i).symm
  right_inv := by
    rintro (⟨⟩ | p) <;> rfl

variable (R : Type) [CommRing R]

def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R ≃+*
    MvPolynomial Unit (MvPolynomial (Σ k, ι k) R) :=
  (renameEquiv R joinIdx).toRingEquiv.trans (sumRingEquiv R Unit (Σ k, ι k))

def tgtEquiv (Ω : Type) [CommRing Ω] : MvPolynomial (K ⊕ Unit) Ω ≃+* MvPolynomial Unit (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.sumComm K Unit)).toRingEquiv.trans (sumRingEquiv Ω Unit K)

variable (Ω : Type) [Field Ω] [Algebra R Ω]

theorem cone_comp (y : (Σ k, ι k) → Ω) :
    ((tgtEquiv (K := K) Ω : MvPolynomial (K ⊕ Unit) Ω →+* MvPolynomial Unit (MvPolynomial K Ω))).comp
        ((mcMap R (joinCoord y (ptCoord (Ω := Ω))) :
            MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →ₐ[R] MvPolynomial (K ⊕ Unit) Ω) :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial (K ⊕ Unit) Ω) =
      (MvPolynomial.map ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* _)).comp
        (srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, MvPolynomial.algebraMap_eq]
  · rintro ⟨(k | ⟨⟩), i⟩
    · simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, joinCoord, joinIdx]
    · simp [tgtEquiv, srcEquiv, mcMap, pointConeMap, joinCoord, joinIdx, ptCoord]

theorem rename_liftVar_eq :
    ((rename (liftVar (ι := ι) ptIdx) : MRing ι R →ₐ[R] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) :
        MRing ι R →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) =
      ((srcEquiv (ι := ι) R).symm : MvPolynomial Unit (MRing ι R) →+* _).comp
        (C : MRing ι R →+* MvPolynomial Unit (MRing ι R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [srcEquiv]
  · intro p
    simp [srcEquiv, liftVar, joinIdx]

end

end JoinPointIdeal

theorem JoinPointIdeal.proof : JoinPointIdeal.Statement := by
  intro R _ Ω _ _ K _ ι _ y
  set φ : MRing ι R →+* MvPolynomial K Ω :=
    ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* MvPolynomial K Ω) with hφ
  have h1 : mcIdeal R (joinCoord y (ptCoord (Ω := Ω))) =
      Ideal.comap (JoinPointIdeal.srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R))
        (RingHom.ker (MvPolynomial.map (σ := Unit) φ)) := by
    ext f
    have hc := RingHom.congr_fun (JoinPointIdeal.cone_comp R Ω y) f
    simp only [RingHom.comp_apply] at hc
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hc]
    simp only [RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]
    exact RingHom.mem_ker
  rw [h1, pointIdeal, show RingHom.ker (pointConeMap R y) = RingHom.ker φ from rfl, ← Ideal.map_coe, JoinPointIdeal.rename_liftVar_eq, ← Ideal.map_map, Ideal.map_coe, Ideal.map_symm, ← MvPolynomial.ker_map]
  rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
