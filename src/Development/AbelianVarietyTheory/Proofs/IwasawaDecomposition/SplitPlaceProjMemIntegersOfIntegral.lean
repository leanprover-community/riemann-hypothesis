module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.splitPlace_proj_mem_integers_of_integral {L : Type} [Field L] [NumberField L] [IsCMField L]
    (s : _root_.ReciprocityTheory.Aut.SplitPlace L) {y : _root_.ReciprocityTheory.Aut.AL L} (hy : y ∈ _root_.ReciprocityTheory.Aut.ALint L) :
    SplitPlace.proj s y ∈ s.v.adicCompletionIntegers (NumberField.maximalRealSubfield L) := by
  have key : _root_.ReciprocityTheory.Aut.ALint L ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.comap (SplitPlace.proj s) := by
    unfold _root_.ReciprocityTheory.Aut.ALint
    rw [Subring.closure_le]
    rintro x (⟨b, rfl⟩ | ⟨a, ha, rfl⟩)
    · simp only [Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        ValuationSubring.mem_toSubring]
      simp only [_root_.ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact _root_.ReciprocityTheory.Aut.SplitPlace.split_le_one s b
    · simp only [Subring.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        ValuationSubring.mem_toSubring]
      simp only [_root_.ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact ha s.v
  exact key hy


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.splitPlace_loc_congr_one :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (N : ℕ) (x : _root_.Formalism.AUTREP.GAf L n),
    _root_.Formalism.L2.NG.Cong L n N x →
    ∀ i j, Valued.v (((SplitPlace.loc s n x : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L))) := by
  intro L _ _ _ n s N x hx i j
  obtain ⟨y, hy, hxy⟩ := hx.2 i j
  have hentry : ((SplitPlace.loc s n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
      Matrix (Fin n) (Fin n) _) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j
      = (N : s.v.adicCompletion (maximalRealSubfield L)) * SplitPlace.proj s y := by
    have h1 : SplitPlace.proj s ((1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := by
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Matrix.one_apply_ne hij]
    rw [← h1, ← map_natCast (SplitPlace.proj s) N, ← map_mul, ← hxy, map_sub]
    rfl
  rw [hentry, map_mul]
  have hle : Valued.v (SplitPlace.proj s y) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
      (_root_.GlobalTheory.splitPlace_proj_mem_integers_of_integral s hy)
  exact mul_le_of_le_one_right' hle

end GlobalTheory
