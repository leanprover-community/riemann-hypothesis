module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.LemmaX
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioOneKilled
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledA
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioEqOneOfCyclic
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkEndx
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledB
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_assemble

open PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem ratio_eq_one_of_coprime_cyclic' (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (hS : S.Finite)
    (hSℓ : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hℓ : ∀ m : M, ℓ • m = 0) (htriv : ∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)), M.ρ g = 1)
    (hK : ∀ (K' : FiniteSubfield) [Fact (K ≤ K')]
      (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) → IsCyclic ((gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) →
      Nat.Coprime ((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))).index ℓ →
      ∀ ιr' : ∀ w : {w : InfinitePlace K'.1 // w.IsReal}, ℚ̄ →ₐ[K'.1] AlgebraicClosure w.1.Completion,
      gsEulerRatio (placesOver S)
        (resTo S K' hK' M) ιr' = 1) :
    gsEulerRatio S M ιr = 1 :=
  W_killed_c.ratio_eq_one_of_cyclic ℓ K S hS hSℓ ιr L hL hN M hℓ htriv
    (fun L' _ hL' hle hcyc => W_killed_b.ratio_coind_cyclic ℓ K S hS hSℓ ιr L hL hN M hℓ htriv hK L' hL' hle hcyc)

theorem ratioOneKilled_of_lemmaX (ℓ : ℕ) [Fact ℓ.Prime] (hX : GlobalEulerCharCoprime) :
    RatioOneKilled ℓ (fun _ => True) := by
  intro K S hS hSℓ _ ιr M _ _ hℓ
  obtain ⟨L, hKL, hsplit⟩ := W_split.exists_split ℓ K S hS hSℓ M
  letI := hKL
  obtain ⟨hL, hN, hζ, hc, htriv⟩ := hsplit
  exact ratio_eq_one_of_coprime_cyclic' ℓ K S hS hSℓ ιr L hL hN M hℓ htriv
    (W_endx.ending_lemmaX hX ℓ K S hS hSℓ ιr L hL hN M hℓ htriv hζ hc)

end PositivityTheory.Lit1.GEN.W_assemble
