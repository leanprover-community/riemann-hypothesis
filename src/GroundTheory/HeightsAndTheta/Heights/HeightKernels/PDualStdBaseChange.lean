module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStdBaseChange
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.SingleMemDualLatticeStandard
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial

namespace StandardDualBaseChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem isMultiHomog_linForm (A : ∀ _ : Unit, Fin i → T → ℤ) (q : Σ _ : Unit, Fin i) :
    IsMultiHomog (linForm (ι := dualBlocks T) (ι₂ := PBlk i) A q) fun _ => 1 := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  cases k
  simp [Finsupp.single_apply]


omit [DecidableEq T] in
theorem exists_linForm_not_mem (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hP : IsArithVar (dualIdeal b) i)
    (hBP : IsBasePtFree (K₂ := Unit) (ι₂ := PBlk i) (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) :
    ∀ k₂ : Unit, ∃ j, linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨k₂, j⟩ ∉ dualIdeal b := by
  intro k₂
  by_contra hall
  simp only [not_exists, not_not] at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  obtain ⟨t, ht⟩ := hrel ()
  obtain ⟨N, hN⟩ := hBP k₂ fun _ => t
  have hle : Ideal.span (Set.range fun j : Fin i =>
      linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨k₂, j⟩) ≤ dualIdeal b :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle, Fintype.prod_unique] at hN
  exact ht (hprime.mem_of_pow_mem N hN)

end StandardDualBaseChange


open StandardDualBaseChange in
theorem DualStdBaseChange.proof (hCM : ChangeOfModelStatement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hBP : DualStdBasePtFree.Statement) (hIm : DualStdImageBot.Statement)
    (hDeg : DualStdGenDeg.Statement) (hMet : DualStdMetricPull.Statement) :
    DualStdBaseChange.Statement := by
  intro K _ _ i T _ _ b hb II hi hII
  have hP : IsArithVar (dualIdeal b) i :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i _ T b hi
  have hBPb := hBP K i T b
  have hGraph := (hGr Unit (dualBlocks T) Unit (PBlk i) (dualIdeal b) i
    (linForm (ι₂ := PBlk i) (dualStdCoordMat b)) (fun _ _ => 1) hP
    (isMultiHomog_linForm _) (exists_linForm_not_mem b hP hBPb)).1
  obtain ⟨G⟩ := hGF Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr inrV _ i
    isBlockMap_inr hGraph
  obtain ⟨J, hJ, -⟩ := hEU G.Φ _ (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) (Sum.inr : Unit → Unit ⊕ Unit))
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hbot : IsArithVar (imageZ (inrV (ι := dualBlocks T) (ι₂ := PBlk (n + 1)))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk (n + 1)) (dualStdCoordMat b)))) (n + 1) := by
    rw [hIm K (n + 1) T b]
    exact IndefiniteRowSideFullHecke.Inter.isArithVar_bot n
  have key := hCM II hII Unit (dualBlocks T) (PBlk (n + 1)) (dualIdeal b) (n + 1) (dualStdCoordMat b) G J
    (fun _ => fsMulti (PBlk (n + 1))) (fun _ => dualLine (HermLattice.standard K (n + 1)) b hb)
    hP hBPb hbot hJ (fun _ => FsLineSmooth.proof Unit (PBlk (n + 1)))
    (fun _ => (DualLineSemipositive.proof K (n + 1) _ T b hb).1) (fun _ => rfl)
    (fun _ z hz => hMet K (n + 1) T b hb z hz)
  rw [key, hDeg K (n + 1) T b G J hi hJ, hIm K (n + 1) T b]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights
