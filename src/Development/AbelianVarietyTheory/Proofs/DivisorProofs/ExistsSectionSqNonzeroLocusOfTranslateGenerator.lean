module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
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
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.PullSecSq

theorem exists_sec_lbPow_two_nonzeroLocus : ∀ (Y X : Scheme.{0}) (f : Y ⟶ X) (M₀ : LB X), M₀.IsLB → ∀ (s₀ : M₀.Sec) (T₁ T₂ : Y ⟶ Y), (∃ t : LB.Gen (LB.LinComb (M₀.pull f) (K := Fin 3) ![T₁, T₂, 𝟙 Y] ![1, 1, -2]), t.IsGen) → ∃ s : (lbPow (M₀.pull f) 2).Sec, nonzeroLocus s = (T₁ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ ⊓ (T₂ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ := by
  intro Y X f M₀ hM s₀ T₁ T₂ ⟨t, ht⟩
  have hN : (M₀.pull f).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨t', ht', -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
    (φ' := Sum.elim (Sum.elim (fun _ : PUnit => T₁) (fun _ : PUnit => T₂)) (fun _ : PUnit => 𝟙 Y))
    (ε' := Sum.elim (Sum.elim (fun _ : PUnit => (1 : ℤ)) (fun _ : PUnit => (1 : ℤ)))
      (fun k => - (fun _ : PUnit => ((2 : ℕ) : ℤ)) k)) (by
      intro U _ h
      simp only [Fin.prod_univ_three, Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      simp) t ht
  have H := AdjointOfPairing.lbIso_of_gen (φ := fun _ : PUnit => 𝟙 Y) (ε := fun _ => ((2 : ℕ) : ℤ)) t' ht'
  obtain ⟨s, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso (GlobalTheory.isLB_lbPow hN 2) (LB.isLB_linComb hN _ _) H
    (DVR.mulSec (M₀.pull f) (fun _ : PUnit => T₁) (fun _ => 1) (fun _ : PUnit => T₂) (fun _ => 1)
      (GlobalTheory.secPull (GlobalTheory.secPull s₀ f) T₁) (GlobalTheory.secPull (GlobalTheory.secPull s₀ f) T₂))
  refine ⟨s, hs.trans ?_⟩
  simp only [GlobalTheory.nonzeroLocus_mulSec, GlobalTheory.nonzeroLocus_secPull]
  rfl

end GlobalTheory.PullSecSq
