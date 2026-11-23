module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Jab.WsInteg

variable {D : D7}

def hermE (D : D7) (r : ℕ) (b : hermA D r) : HermR (AF D.host.F) D.sp.cm.sig r :=
  ⟨b.1, fun i j => by
    have h := congrFun (congrFun b.2 i) j
    simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] at h
    exact h⟩

theorem integrable_of_addEquiv {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V']
    (g : V → V') (k : V' → V) (h1 : Function.LeftInverse k g) (h2 : Function.RightInverse k g)
    (hadd : ∀ x y, g (x + y) = g x + g y) (hc : Continuous g) (hc' : Continuous k)
    (μ : Measure V) (hμ : μ.IsAddHaarMeasure) (ν : Measure V') (hν : ν.IsAddHaarMeasure)
    (f : V' → ℂ) (hf : Integrable (fun b => f (g b)) μ) : Integrable f ν := by
  let e : V ≃+ V' := { toFun := g, invFun := k, left_inv := h1, right_inv := h2, map_add' := hadd }
  let h : V ≃ₜ V' := { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hc hc'
  have hi : Integrable f (μ.map e) := (integrable_map_equiv h.toMeasurableEquiv f).2 hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (μ.map e)]
  exact hi.smul_measure_nnreal




theorem integrable_of_hermE {r : ℕ} (lam : Measure (hermA D r)) (hlam : lam.IsAddHaarMeasure)
    (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)) (hdb : db.IsAddHaarMeasure)
    (f : HermR (AF D.host.F) D.sp.cm.sig r → ℂ) (hf : Integrable (fun b => f (hermE D r b)) lam) :
    Integrable f db := by
  haveI : IsTopologicalAddGroup (Mx D r r) := inferInstanceAs (IsTopologicalAddGroup (Fin r → Fin r → AE D))
  haveI i3 : SecondCountableTopology (Mx D r r) := inferInstanceAs (SecondCountableTopology (Fin r → Fin r → AE D))
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  haveI : SecondCountableTopology (HermR (AF D.host.F) D.sp.cm.sig r) :=
    @Topology.IsInducing.secondCountableTopology _ _ _ _ _ i3 Topology.IsInducing.subtypeVal
  exact integrable_of_addEquiv (hermE D r) (fun S => ⟨S.1, Matrix.ext fun a c => S.2 a c⟩) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (continuous_subtype_val.subtype_mk _) (continuous_subtype_val.subtype_mk _)
    lam hlam db hdb f hf

end PositivityTheory.PfWsf.Jab.WsInteg
