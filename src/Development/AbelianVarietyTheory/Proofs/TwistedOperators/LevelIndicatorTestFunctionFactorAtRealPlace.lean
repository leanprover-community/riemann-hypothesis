module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem coef_factor : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ) (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (q : NI V C), q ∈ GlobalTheory.FibreAtTau.offP θ V C τ → ∀ x y : GA D V, ∃ R : ℂ, ∀ p ∈ GlobalTheory.FibreAtTau.atP θ V C τ, coef θ M K v a (x * ((p * q : NI V C) : GA D V) * y) = ⟪v τ, M.rep τ (cmp θ τ x * cmp θ τ (p : GA D V) * cmp θ τ y) (a τ)⟫_ℂ * R := by
  intro D θ _ V S M K v a τ r C q hq x y
  classical
  rw [mem_offP] at hq
  have hcmp : ∀ τ' (g h : GA D V), cmp θ τ' (g * h) = cmp θ τ' g * cmp θ τ' h := fun τ' g h =>
    (GlobalTheory.RowReal.infMatHom V (θ τ')).map_mul g h
  refine ⟨if Lev.finE V (x * (q : GA D V) * y) ∈ K then
      ∏ τ' ∈ Finset.univ.erase τ, ⟪v τ', M.rep τ' (cmp θ τ' (x * (q : GA D V) * y)) (a τ')⟫_ℂ else 0, ?_⟩
  intro p hp
  rw [mem_atP] at hp
  have hfin : Lev.finE V (p : GA D V) = 1 := by
    have h1 : (p : GA D V) ∈ (⊥ : Subgroup (GL (Fin V.rank) (Lev.EAf D))).comap (Lev.finE V) := by
      rw [GlobalTheory.Mass.Levels.comap_finE]
      exact Subgroup.mem_sup_right hp.1
    simpa using h1
  have hF : Lev.finE V (x * ((p * q : NI V C) : GA D V) * y) = Lev.finE V (x * (q : GA D V) * y) := by
    simp only [Subgroup.coe_mul, map_mul, hfin, one_mul]
  simp only [coef, coefR, hF]
  split_ifs with h
  · have e1 : cmp θ τ (x * ((p * q : NI V C) : GA D V) * y) = cmp θ τ x * cmp θ τ (p : GA D V) * cmp θ τ y := by
      rw [Subgroup.coe_mul, hcmp, hcmp, hcmp, hq, mul_one]
    have e2 : ∀ τ' ∈ Finset.univ.erase τ,
        ⟪v τ', M.rep τ' (cmp θ τ' (x * ((p * q : NI V C) : GA D V) * y)) (a τ')⟫_ℂ =
          ⟪v τ', M.rep τ' (cmp θ τ' (x * (q : GA D V) * y)) (a τ')⟫_ℂ := by
      intro τ' hτ'
      have hp' := hp.2 τ' (Finset.ne_of_mem_erase hτ')
      rw [Subgroup.coe_mul, hcmp, hcmp, hcmp, hcmp, hcmp, hp', one_mul]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), e1, Finset.prod_congr rfl e2]
  · simp

end GlobalTheory.FibreAtTau
