module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutLiesOver
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutProjection

theorem relDim_anti {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} {I J : Ideal (MRing ι F)}
    (hIJ : I ≤ J) : FieldNumbers.relDim J ≤ FieldNumbers.relDim I := by
  have hmono : Monotone (fun x : WithBot ℕ∞ =>
      WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) x) :=
    WithBot.monotone_map_iff.2 (WithTop.monotone_map_iff.2 (fun a b h =>
      Int.sub_le_sub_right (by exact_mod_cast h) _))
  exact hmono (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJ) (Ideal.Quotient.factor_surjective hIJ))

theorem specialIdeal_le_contractPrime {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K K' : Type*} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type*}
    {I : Ideal (MRing (fun k => ι' (j k)) O)} {W : Ideal (MRing ι' O)}
    (h : I ≤ W.comap (rename (FieldNumbers.blockIncl j ι'))) :
    specialIdeal I ≤ FieldNumbers.contractPrime j (specialIdeal W) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  simp only [Ideal.mem_comap, FieldNumbers.contractPrime, specialIdeal]
  rw [← map_rename]
  exact Ideal.mem_map_of_mem _ (h hf)

end SegreFlagCutProjection

open SegreFlagCutProjection in
theorem SegreFlagCutProjection.proof (hLies : SegreFlagCutLiesOver.Statement)
    (hDim : SegreFlagProjSpecialDim.Statement) : SegreFlagCutProjection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  obtain ⟨hl1, hl2⟩ := hLies O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  obtain ⟨hd1, hd2⟩ := hDim O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  refine ⟨fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_,
    fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_⟩
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl1 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd1
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl2 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
