module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IdxAdic
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.decIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p c : ℕ) (A₀ : ValuationSubring Ω), p.Prime → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → A₀.valuation (p : Ω) < 1 →
      ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≠ 0 ∧ ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≤ c := by
  intro Ω _ _ _ p c A₀ hp hc hA
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, hgζ⟩ := decFrob Ω p A₀ hA
  have hodd : Nat.Coprime 2 p := by
    rw [Nat.coprime_two_left, Nat.odd_iff]; omega
  have hu : ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2]) = p := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 ^ n)
    have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val :=
      cyclotomicCharacter.spec 2 (n := n) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) ζ hζ.pow_eq_one
    have h2 := hgζ (2 ^ n) (Nat.Coprime.pow_left n hodd) ζ hζ.pow_eq_one
    rw [h2] at h1
    have h3 : p ≡ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val [MOD 2 ^ n] := by
      have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (by positivity)
      rwa [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
    rw [map_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 h3, ZMod.natCast_zmod_val]
  have hcl : IsClosed ((decImage ℚ 2 A₀ : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
    ((isClosed_Dec (F := ℚ) A₀).isCompact.image (continuous_cycZ ℚ Ω 2)).isClosed
  obtain ⟨h0, hle⟩ := idxAdic (decImage ℚ 2 A₀) (cycZ ℚ Ω 2 g) p c hcl ⟨g, hg, rfl⟩ hu hc
  have e : (cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀ = (decImage ℚ 2 A₀).comap (cycZ ℚ Ω 2) := by
    rw [decImage, Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : (decImage ℚ 2 A₀).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  refine ⟨fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hrel0).trans ?_
  rwa [Subgroup.relIndex_top_right]
