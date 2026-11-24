module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace SectionFn

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem differentiable_of_isFn (hL : L.IsLB) {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) :
    Differentiable ℂ θ := by
  intro z
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hn := (u.hol (L.U i) (s.f i)).1.mem_nhds hi
  have d : DifferentiableOn ℂ (fun w => valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹)
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U i} :=
    (u.hol (L.U i) (s.f i)).2.mul ((u.fr_hol i).inv fun w hw => u.fr_ne i w hw)
  refine (d.differentiableAt hn).congr_of_eventuallyEq (Filter.mem_of_superset hn fun w hw => ?_)
  have := u.fr_ne i w hw
  change θ w = valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹
  rw [h i w hw]
  field_simp

theorem isThetaFn_of_isFn (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsThetaFn Hm χ 1 θ := by
  refine ⟨differentiable_of_isFn u hL h, fun l z => ?_⟩
  have hper : u.ex (z + l) = u.ex z := by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h i z hi
  have h2 := h i (z + l) hi'
  rw [hper, h1, hAH.2.2.2 l i z hi] at h2
  refine mul_right_cancel₀ (u.fr_ne i _ hi') ?_
  rw [← h2, pow_one]
  unfold hermForm
  ring

theorem ne_zero_of_isFn [LocallyOfFiniteType A.hom] {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ)
    {p : A.left} (hp : p ∈ Out.nonzeroLocus s) : θ ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  have hle : A.left.basicOpen (s.f i) ≤ ⊥ := by
    refine ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun y hy hyb => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk y hy)
    have hzy : (u.ex z).left = y := by rw [hz]; rfl
    subst hzy
    have hne := (top_le_preimage_basicOpen_iff _ _ _).1 hyb
    have hU := top_le_preimage_of_valAt'_ne_zero _ hne
    exact absurd (by simpa using h i z hU) hne
  exact hle hi

end SectionFn

theorem isThetaFn_and_ne_zero_of_isFn :
    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ), u.IsAH Hm χ → u.IsFn x.th θ → u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 := by
  intro x u Hm χ θ hAH h
  refine ⟨SectionFn.isThetaFn_of_isFn u x.P.isLB hAH h, ?_⟩
  obtain ⟨p, -, hp⟩ := x.th_ne (default : PrimeSpectrum ℂ)
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  exact SectionFn.ne_zero_of_isFn u h hp

end GlobalTheory
