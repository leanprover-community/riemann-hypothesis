module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.splitsField_of :
    SplitsField := by
  intro R S K _ _ _ _ _ _ hE
  haveI : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  haveI : IsArtinianRing (K ⊗[R] S) := isArtinian_of_tower K inferInstance
  let q : (S →ₐ[R] K) ≃ PrimeSpectrum (K ⊗[R] S) :=
    (AlgHom.liftEquiv R K S K).trans (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K (K ⊗[R] S))
  refine ⟨Finite.of_equiv _ q.symm, ?_⟩
  let e : K ⊗[R] S ≃ₐ[K] (S →ₐ[R] K) → K :=
    (Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S)).trans
      (AlgEquiv.piCongrLeft' K (fun _ => K) q.symm)
  suffices h : splitMap (fun z : S →ₐ[R] K => z) = e.toAlgHom by
    rw [Splits, h]
    exact e.bijective
  apply Algebra.TensorProduct.ext_ring
  ext s ψ
  let f : K ⊗[R] S →ₐ[K] K := AlgHom.liftEquiv R K S K ψ
  have hker : (⊥ : PrimeSpectrum K).comap f = q ψ :=
    PrimeSpectrum.ext (RingHom.ker_eq_comap_bot _).symm
  show splitMap (fun z : S →ₐ[R] K => z) (1 ⊗ₜ s) ψ =
    Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S) (1 ⊗ₜ s) (q ψ)
  rw [splitMap_tmul, one_mul, ← hker, Algebra.FormallyEtale.equivPiOfIsSepClosed_comap,
    Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply]
  simp only [f, AlgHom.liftEquiv_tmul, one_smul]
