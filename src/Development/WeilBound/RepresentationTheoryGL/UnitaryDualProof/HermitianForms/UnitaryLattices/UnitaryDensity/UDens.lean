module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.BlockContinuity.ContinuousBlkAt
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.ColumnAlgebra.PiColElAdd
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.MirabolicVectors.ContinuousMulVec
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.Stab
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.TwistedKernels.TwKerColElStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Dens

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

theorem uDens (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : UDens k := by
  intro ψ hψ hψ1 m N hN V _ _ π hπ s B hB A₀ hA₀
  have hL : Lv ψ hN π s B := ⟨hψ, hψ1, hπ, hB.1, hB.2.1, hB.2.2⟩
  obtain ⟨B', hD, -⟩ := Ex.dens_exists_of hL (fun ξ A hA v w => alg.avg_selfadj hL ξ hA v w)
    (fun K hK _ hA₀ => stab.stab' hL K hK hA₀) hA₀
  exact ⟨B', hD, props.dens_psd hL hA₀ hD, props.dens_kills hL hA₀ hD, mir.dens_mir hL hA₀ hD,
    fun v hv => props.dens_rad hL hA₀ hD v hv⟩

end PositivityTheory.RgUd.Form.U.Dens
