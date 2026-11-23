module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CombTheta

theorem comb_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (g : WO S T → ℂ), IsThetaFunO ψ S T g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ z ∈ R, c z • heisO ψ S T (t z) g) ∧ ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ R, c z • heisO ψ S T (t z) g) φ = ∑ z ∈ R, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  classical
  intro D ψ θ S T hψ hθ g hg ι R c t ht
  have ft := GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ g hg
  have hth : ∀ z ∈ R, IsThetaFunO ψ S T (heisO ψ S T (t z) g) := fun z hz => (ft.2 (t z) (ht z hz)).1
  have key : ∀ s ⊆ R, IsThetaFunO ψ S T (∑ z ∈ s, c z • heisO ψ S T (t z) g) ∧
      ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
        (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ),
        pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ s, c z • heisO ψ S T (t z) g) φ =
          ∑ z ∈ s, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ⟨GlobalTheory.OrientedHeis.theta_zero, fun sS BS sT BT φ =>
        GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
    | insert i s hi ih =>
      intro hs
      have hiR : i ∈ R := hs (Finset.mem_insert_self i s)
      have ih' := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
      simp only [Finset.sum_insert hi]
      refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hth i hiR)) ih'.1, fun sS BS sT BT φ => ?_⟩
      rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (c i) (hth i hiR) ih'.1 φ, ih'.2,
        (ft.2 (t i) (ht i hiR)).2 sS BS sT BT φ]
  exact ⟨(key R subset_rfl).1, fun sS BS sT BT φ => (key R subset_rfl).2 sS BS sT BT φ⟩

end GlobalTheory.CombTheta

end
