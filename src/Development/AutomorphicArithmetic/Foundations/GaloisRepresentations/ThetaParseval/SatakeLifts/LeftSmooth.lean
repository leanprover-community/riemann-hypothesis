module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.leftSmooth :
    UpperTheory.Gal.TP.Loc.LeftSmooth := by
  intro k _ _ _ _ n d Φ
  obtain ⟨hlc, hcs⟩ := Φ.2
  have key : ∀ f : GL (Fin n) k → Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k,
      Continuous (fun p : GL (Fin n) k × Matrix (Fin n) (Fin d) k => f p.1 p.2) → (∀ X, f 1 X = X) →
      ∀ᶠ g in nhds (1 : GL (Fin n) k), ∀ X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ),
        (Φ : Matrix (Fin n) (Fin d) k → ℂ) (f g X) = (Φ : Matrix (Fin n) (Fin d) k → ℂ) X := by
    intro f hf h1
    apply hcs.isCompact.eventually_forall_of_forall_eventually
    intro X₀ _
    have e1 := (hlc.comp_continuous hf).eventually_eq (1, X₀)
    have e2 := (hlc.comp_continuous
      (continuous_snd : Continuous (Prod.snd : GL (Fin n) k × Matrix (Fin n) (Fin d) k → _))).eventually_eq (1, X₀)
    filter_upwards [e1, e2] with p hp1 hp2
    simp only [Function.comp] at hp1 hp2
    rw [hp1, hp2, h1]
  have hU1 := key (fun g X => (g : Matrix (Fin n) (Fin n) k) * X)
    ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd) (fun X => by simp)
  have hU2 := key (fun g X => ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X)
    ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul continuous_snd) (fun X => by simp)
  filter_upwards [hU1, hU2] with g hg1 hg2
  intro X
  by_cases hX : X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  · exact hg1 X hX
  by_cases hgX : (g : Matrix (Fin n) (Fin n) k) * X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  · have := hg2 _ hgX
    rw [← Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hgX]
