module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pEtTr :
    EtTr := by
  intro l _ B hl n i Z Y p q s _ _ W r c hc J _ σ hσ hsp x
  obtain ⟨hsc, hiso⟩ := hsp
  have hT := UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2
  let e := Fintype.equivFin J
  have hiso' : IsIso (Sigma.desc fun k : Fin (Fintype.card J) =>
      pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) := by
    have hEq : (Sigma.desc fun k : Fin (Fintype.card J) =>
        pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) =
        (Sigma.reindex e.symm (fun _ : J => W)).hom ≫
          Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]) := by
      refine Sigma.hom_ext _ _ (fun k => ?_)
      rw [Sigma.ι_desc]
      have h4 := Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := fun _ : J => W) (b := k)
        (h := Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]))
      rw [Sigma.ι_desc] at h4
      exact h4.symm
    rw [hEq]
    infer_instance
  have hlZ : IsUnit ((l : Γ(Z, ⊤))) := by
    simpa using hl.map (Scheme.Hom.appTop p).hom
  have h1 := hT l n i s hlZ W c (Fintype.card J) (fun k => σ (e.symm k)) (fun k => hsc _) hiso'
  have h2 : ∀ y : HQ l (sch.obj Y) n i, pullHQ l (sch.map c) n i
      (TranscendenceTraces.trHQ l s (TranscendenceTraces.Wt.const Y 1) n i y) = ∑ j, pullHQ l (sch.map (σ j)) n i y := by
    intro y
    have h3 := LinearMap.congr_fun h1 y
    rw [LinearMap.comp_apply, LinearMap.sum_apply] at h3
    rw [h3]
    exact Equiv.sum_comp e.symm (fun j => pullHQ l (sch.map (σ j)) n i y)
  exact h2 x
