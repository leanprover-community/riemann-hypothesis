module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UGenApprox
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (B : UniversalOrdinaryDeterminantRing r) (N : ℕ) (x : B.B), ∃ y ∈ Algebra.adjoin O ({a | ∃ (i : ℕ) (g : F.G₀), 1 ≤ i ∧ i ≤ n ∧ a = B.u.D.lam i (MonoidAlgebra.single g 1)} ∪ {a | ∃ v i g, a = ((B.u.ψ v i g : B.Bˣ) : B.B)}), x - y ∈ maximalIdeal B.B ^ N := by
  intro l _ F O _ _ _ _ _ _ _ n r B N x
  refine u_gen O B.B _ ?_ N x
  intro R' _ _ _ f f' h
  obtain ⟨p, hp⟩ := pair_map r B.u f
  refine (B.univ R' p).unique hp ⟨?_, fun v i => ?_⟩
  · rw [← hp.1]
    refine d_gext _ _ fun g i h1 h2 => ?_
    have e : ∀ φ : B.B →+* R', (B.u.D.map φ).lam i (MonoidAlgebra.single g 1) =
        φ (B.u.D.lam i (MonoidAlgebra.single g 1)) := fun φ => by
      have := ((d_gmap B.u.D).2.2.1 φ (MonoidAlgebra.single g 1)).2 i
      rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
    rw [e, e]
    exact (h _ (Or.inl ⟨i, g, h1, h2, rfl⟩)).symm
  · rw [← hp.2 v i]
    ext g
    exact (h _ (Or.inr ⟨v, i, g, rfl⟩)).symm
