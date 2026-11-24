module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.HermitianForms.TiedStep
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceComponentRingHomIntegral
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.exists_splitPlace_component_ringHom_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∃ φ : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k,
      (∀ a : AE D, φ (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a) ∧
      (∀ c : D.host.E, φ (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c)) ∧
      (∀ c : D.host.E, φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F)
          (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c)) = p.pr (incA D (sigD D c))) ∧
      ∀ z, z ∈ Formalism.UG.tensInt (F := D.host.F) (p.v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
          (p.v.adicCompletionIntegers D.host.F).toSubring ↔
        φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.SplitPhi.exists_ringHom_int | exact GlobalTheory.FinPl.SplitPhi.exists_ringHom_int | (intros; apply GlobalTheory.FinPl.SplitPhi.exists_ringHom_int <;> assumption)
