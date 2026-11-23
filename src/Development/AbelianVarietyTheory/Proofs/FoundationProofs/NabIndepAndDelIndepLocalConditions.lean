module

public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPDelStdOfIsBasisAtStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAtStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.TestLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem isBasisAt_inv_mul (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (B B' : GL (Fin n) K)
    (h : IsBasisAt w M B) (h' : IsBasisAt w M B') : IsBasisAt w (colLat 1) (B'⁻¹ * B) := by
  rw [← isBasisAt_gLat w B', ← colLat_mul, mul_one, mul_inv_cancel_left]
  exact h'.symm.trans h

theorem indep_of_stable (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (T : Submodule (𝓞 K) (Pol K ι n))
    (hT : ∀ g : ι → GL (Fin n) K, (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ T, actP lam g F ∈ T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K)
    (h : ∀ τ, IsBasisAt w (M τ) (B τ)) (h' : ∀ τ, IsBasisAt w (M τ) (B' τ)) (F : Pol K ι n) :
    actP lam B⁻¹ F ∈ T ↔ actP lam B'⁻¹ F ∈ T := by
  constructor
  · intro hF
    have := hT (B'⁻¹ * B) (fun τ => isBasisAt_inv_mul w (M τ) (B τ) (B' τ) (h τ) (h' τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this
  · intro hF
    have := hT (B⁻¹ * B') (fun τ => isBasisAt_inv_mul w (M τ) (B' τ) (B τ) (h' τ) (h τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this

theorem nabIndep_and_delIndep : NabIndep ∧ DelIndep :=
  ⟨fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt K ι n lam w) M B B' h h' F,
    fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (GlobalTheory.T.polyAction_mem_locP_delStd_of_isBasisAt K ι n lam w) M B B' h h' F⟩

end GlobalTheory.TestLat
