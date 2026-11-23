module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DecInf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ClosedInf
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.index_cyclotomicKer_sup_decompositionGroup_ne_zero :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → ((cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A).index ≠ 0 := by
  intro Ω _ _ _ l _ p A hp hA
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hg : ∃ g ∈ Dec (F := ℚ) A, ¬ IsOfFinOrder (cycZ ℚ Ω l g) := by
    by_cases hlp : l = p
    · subst hlp
      obtain ⟨g, hg, hf⟩ := UpperTheory.V.Base.decInf ℚ Ω l ⊤ isOpen_univ A hA
      exact ⟨g, hg.2, hf⟩
    · obtain ⟨-, -, γ, hγ, -, hc⟩ := UpperTheory.V.Chr.decCyc Ω p A hp hA
      refine ⟨γ, hγ, fun hf => ?_⟩
      obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
      have h3 := congrArg (Units.val : ℤ_[l]ˣ → ℤ_[l]) e
      rw [Units.val_pow_eq_pow_val, hc l hlp, Units.val_one] at h3
      have h4 : p ^ n = 1 := by exact_mod_cast h3
      exact (Nat.one_lt_pow hn.ne' hp.one_lt).ne' h4
  obtain ⟨g, hg, hf⟩ := hg
  have hcl : IsClosed (((Dec (F := ℚ) A).map (cycZ ℚ Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
    ((isClosed_Dec (F := ℚ) A).isCompact.image (continuous_cycZ ℚ Ω l)).isClosed
  have h0 := UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder l _ hcl ⟨_, ⟨g, hg, rfl⟩, hf⟩
  have e : (cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A = ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).comap (cycZ ℚ Ω l) := by
    rw [Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  exact fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)
