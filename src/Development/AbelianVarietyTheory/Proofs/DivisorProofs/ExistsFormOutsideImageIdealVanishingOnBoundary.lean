module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormsQuotientBirationalSystemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BoundaryForm

theorem exists_local_fun {Y : Scheme.{0}} [IrreducibleSpace Y] (Z : TopologicalSpace.Closeds Y) (hZ : Z ≠ ⊤) (y : Y) :
    ∃ (W : Y.Opens) (a : Γ(Y, W)), y ∈ W ∧ a ≠ 0 ∧ ∀ z ∈ Y.basicOpen a, z ∉ Z := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hne : ((Z : Set Y)ᶜ).Nonempty := Set.nonempty_compl.2 fun h => hZ (SetLike.coe_injective h)
  obtain ⟨z, hzW, hzZ⟩ := nonempty_preirreducible_inter W.isOpen Z.isClosed.isOpen_compl ⟨y, hy⟩ hne
  obtain ⟨a, ha, hz⟩ := IsAffineOpen.exists_basicOpen_le hW (V := Z.compl) ⟨z, hzZ⟩ hzW
  refine ⟨W, a, hy, ?_, fun w hw => ha hw⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hz
  exact hz

theorem exists_form_vanishing : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∃ (d : ℕ) (g : MvPolynomial (Fin T.N) F), g.IsHomogeneous d ∧ g ∉ T.imageIdeal ∧
      ∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0 := by
  intro F _ _ T hG hB
  have hV := hG.alg.variety
  have := HeightExists.isIntegral hV
  have := isNoetherian_of_isProjOver hV.proj
  have hp := HeightExists.isPrime_imageIdeal hV
  choose W a hy ha hz using exists_local_fun T.bd hG.bd_ne
  choose d P Q hP _ _ hPn hval using fun y => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F T.toLinSys hV hG.alg.bpf hB (W y) (a y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set T.Y)) (fun y => (W y).isOpen)
    fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩
  refine ⟨∑ y ∈ s, d y, ∏ y ∈ s, P y, IsHomogeneous.prod s P d fun y _ => hP y, fun h => ?_, fun K _ _ x hx => ?_⟩
  · obtain ⟨y, -, h⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hPn y (ha y) h
  · obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ (ptOf x.1)))
    rw [map_prod]
    refine Finset.prod_eq_zero hys ?_
    have h0 : valR x.1 (W y) (a y) = 0 := by
      by_contra h
      exact hz y _ ((valR_ne_zero_iff x.1 hxy _).1 h) hx
    rw [← hval y K x hxy, h0, zero_mul]

end GlobalTheory.BoundaryForm
