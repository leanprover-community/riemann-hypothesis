module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTargetStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTieEntire
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantFormsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberFormsStableOfReferenceTuple
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical

namespace GlobalTheory.KFiClose

theorem kFi_of_tie : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  intro D L hT Gi Gl K Y cX ex t hC hF
  have second : ∀ u μ, DV.Used D μ → ∀ i < D.R.m, ∀ φ ∈ (ex.tw.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (ex.tw.fm u μ).Fi (i + 1) := by
    intro u μ hμ
    obtain ⟨G, hFA, hSP⟩ := hF u μ hμ
    exact GlobalTheory.T.kernelOperator_maps_stabiliserEquivariant_forms D u (D.chTw u μ) _ _ (ex.tw.fm u μ) (t.O u μ) G hFA (t.unf u μ)
      (fun i hi c c' => GlobalTheory.KerTieEntire.kerTie_entire D L hT Gi Gl K Y cX ex t u μ i hi c c')
      (GlobalTheory.T.classSum_term_law_stabiliser_target D L hT Gi Gl K Y cX ex t hC u μ G hSP)
  have h0 : DV.Used D D.what₂.mu0 := by
    unfold DV.Used
    exact Or.inl rfl
  exact ⟨fun u i hi => GlobalTheory.KFiMu0.memberForms_stable_of_reference_tuple D ex.tw u i hi (second u _ h0 i hi), second⟩

end GlobalTheory.KFiClose
