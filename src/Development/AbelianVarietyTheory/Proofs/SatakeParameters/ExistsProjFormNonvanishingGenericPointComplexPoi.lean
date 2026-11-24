module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Mathlib.Algebra.Module.Submodule.Union
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

theorem exists_form_forall_notMem (N n : ℕ) (T : Finset (PSpace ℂ N)) :
    ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n, ∀ x ∈ T, f ∉ x.asHomogeneousIdeal := by
  classical
  let V : T → Submodule ℂ (GlobalTheory.ProjSpace.grading ℂ N 1) := fun x =>
    ((x.1.asHomogeneousIdeal.toIdeal).restrictScalars ℂ).comap (GlobalTheory.ProjSpace.grading ℂ N 1).subtype
  have hV : ∀ x, V x ≠ ⊤ := by
    intro x h
    obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℂ N x.1
    have hX : (⟨MvPolynomial.X i, GlobalTheory.ProjSpace.X_mem ℂ N i⟩ : GlobalTheory.ProjSpace.grading ℂ N 1) ∈ V x :=
      h ▸ Submodule.mem_top
    exact (Proj.mem_basicOpen _ _ _).1 hi hX
  obtain ⟨ℓ, hℓ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top V hV
  have hpow : ℓ.1 ^ n ∈ GlobalTheory.ProjSpace.grading ℂ N n := by
    simpa using SetLike.pow_mem_graded n ℓ.2
  refine ⟨ℓ.1 ^ n, hpow, fun x hx hmem => hℓ ⟨x, hx⟩ ?_⟩
  exact x.isPrime.mem_of_pow_mem n hmem

theorem exists_form_genericPoint_cxPts : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (N : ℕ)
    (ι : X ⟶ PSpace ℂ N) (n : ℕ) (F : Finset (CxPts p (RingHom.id ℂ))), ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n,
      genericPoint X ∈ GlobalTheory.EtProj.fOpen ι f ∧ ∀ z ∈ F, z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f) := by
  intro X _ p N ι n F
  classical
  obtain ⟨f, hf, hT⟩ := exists_form_forall_notMem N n
    (insert (ι.base (genericPoint X)) (F.image fun z => ι.base (z.1 (IsLocalRing.closedPoint ℂ))))
  refine ⟨f, hf, hT _ (Finset.mem_insert_self _ _), fun z hz => ?_⟩
  exact CxPts.mem_ptsIn.2 (hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.EtProj
