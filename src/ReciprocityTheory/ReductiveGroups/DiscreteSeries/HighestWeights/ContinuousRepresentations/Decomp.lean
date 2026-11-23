module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem finrank_eq_sum_of_orth {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {m : ℕ} (A : Fin m → Submodule ℂ V)
    (horth : ∀ i i', i ≠ i' → ∀ y ∈ A i, ∀ z ∈ A i', ⟪y, z⟫_ℂ = 0) (htop : (⨆ i, A i) = ⊤) :
    Module.finrank ℂ V = ∑ i, Module.finrank ℂ (A i) := by
  classical
  have hOF : OrthogonalFamily ℂ (fun i => A i) fun i => (A i).subtypeₗᵢ :=
    fun i j hij v w => horth i j hij _ v.2 _ w.2
  have hind : iSupIndep A := by
    first
      | exact hOF.independent
      | exact hOF.iSupIndep
  have hint : DirectSum.IsInternal A := by
    first
      | exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top A).mpr ⟨hind, htop⟩
      | exact (DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top A).mpr ⟨hind, htop⟩
  rw [Module.finrank_eq_card_basis (hint.collectedBasis fun i => Module.finBasis ℂ (A i)),
    Fintype.card_sigma]
  simp

theorem compRed_of (hR : KRepRelStatement) (hS : KRepStableStatement) (hP : KRepPieceStatement) :
    CompRedStatement := by
  intro n ε R
  obtain ⟨hrel, hunit⟩ := hR n ε R
  obtain ⟨m, x, μ, hx, horth, htop⟩ :=
    Formalism.REAL.kDecomp R.V n ε R.units ⊤ inferInstance hrel hunit (fun a b _ v _ => Submodule.mem_top)
  refine ⟨m, x, μ, fun i => ⟨(hx i).2.1, (hx i).2.2⟩, horth, htop, ?_, ?_, ?_⟩
  · exact finrank_eq_sum_of_orth _ horth htop
  · intro i k v hv
    exact (hS n ε R _).mpr (Formalism.REAL.isCompactInvariant_compactSpan (x i)) k v hv
  · intro i
    obtain ⟨T, φ, h1, h2, h3⟩ := hP n ε R (μ i) (x i) (hx i).2.1 (hx i).2.2
    exact ⟨T, φ, φ.toLinearEquiv.finrank_eq, h1, h2, h3⟩

end ReciprocityTheory.ChartRestriction.DS.HW
