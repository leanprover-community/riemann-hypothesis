module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Cohen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CompDim
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
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem dim_le_nil {R : Type} [CommRing R] :
    ringKrullDim R ≤ ringKrullDim (R ⧸ nilradical R) := by
  rw [ringKrullDim_quotient]
  have h : PrimeSpectrum.zeroLocus (nilradical R : Set R) = Set.univ := by
    ext p
    simp only [Set.mem_univ, iff_true, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact nilradical_le_prime p.asIdeal
  rw [h]
  exact le_of_eq (Order.krullDim_eq_of_orderIso OrderIso.Set.univ).symm

theorem UpperTheory.V.AlgebraTools.Conn.clComp :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
      [CommRing R] [IsLocalRing R] [Algebra O R] [IrreducibleSpace (PrimeSpectrum R)], UpperTheory.V.CA.IsCL O R → ∀ (a q : Ideal R) (h : ℕ),
      ReciprocityTheory.CA.AraLE a h → q ∈ a.minimalPrimes → ringKrullDim R ≤ ringKrullDim (R ⧸ q) + h := by
  intro O R _ _ _ _ _ _ _ _ hR a q h ha hq
  haveI := hR.noeth
  obtain ⟨s, hs, hrad⟩ := ha
  have hnil : (nilradical R).IsPrime := by
    have hirr : IsIrreducible (PrimeSpectrum.zeroLocus ((⊥ : Ideal R) : Set R)) := by
      rw [Submodule.bot_coe, PrimeSpectrum.zeroLocus_singleton_zero]
      exact IrreducibleSpace.isIrreducible_univ _
    exact (PrimeSpectrum.isIrreducible_zeroLocus_iff ⊥).mp hirr
  have hsup : (nilradical R ⊔ Ideal.span (s : Set R)).radical = a.radical := by
    rw [Ideal.radical_sup, nilradical, Ideal.radical_idem, ← Ideal.radical_sup, Submodule.zero_eq_bot,
      bot_sup_eq, hrad]
  have hq' : q ∈ (nilradical R ⊔ Ideal.span (s : Set R)).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hsup, Ideal.radical_minimalPrimes]
    exact hq
  calc ringKrullDim R ≤ ringKrullDim (R ⧸ nilradical R) := dim_le_nil
    _ ≤ ringKrullDim (R ⧸ q) + s.card := compDim (cohen hR) _ q s hnil hq'
    _ ≤ ringKrullDim (R ⧸ q) + h := by
      gcongr
