module

public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelBasisDeterminantAbsAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NrmIdNonneg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderTypeStatement
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

namespace GlobalTheory.KerJ

theorem unUnit_of_mtType : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ u μ, MtType u (t.O u μ).mt) → t.ent.UnUnit := by
  intro D L hT Gi Gl K Y cX ex t hm u μ w hw i hi c c'
  have h3 := GlobalTheory.T.rhoThreeOf_of_determinantCharacterFiniteOrderType D u (D.chTw u μ) _ (hm u μ)
  have hb := CharVal.brRho_holds D _ _ h3
  rw [t.kf_un u μ w hw i hi c c']
  exact (t.kf u μ w hw).norm_un ((t.kf u μ w hw).unUnit_of t.idl t.idl_ok hb (GlobalTheory.T.kernelBasis_determinant_abs_at_place _ _ _ _ _ _ _ _ _)) hi c c'

end GlobalTheory.KerJ
