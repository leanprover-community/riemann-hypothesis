module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimage
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem _root_.GlobalTheory.T.exists_nhds_transportedAction_finitePoint_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ) (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ p0 : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) := by
  first | exact @GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | exact GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | (intros; apply GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage <;> assumption)
