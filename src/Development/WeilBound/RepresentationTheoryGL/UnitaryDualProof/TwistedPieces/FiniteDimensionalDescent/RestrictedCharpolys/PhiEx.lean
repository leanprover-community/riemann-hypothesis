module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PullPieces
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PrimIdemZ
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
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.ContinuousEF
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PowCardEqZero

@[expose] public section

namespace PositivityTheory.RgUd.TP.Desc.Restr.Pphi1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC PositivityTheory.RgUd.TP.Desc.Restr.PphiE

theorem phiEx (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    FinDim k → PhiEx k := by
  intro hF p c _ _ n Z hZ hn
  obtain ⟨d, -, ⟨B⟩⟩ := fb_exists hF p c
  exact ⟨n * d, Z' B Z, φ B, e B,
    { inj := φ_inj B
      emb := φ_emb B
      econt := continuous_eF B
      econt' := continuous_eI B
      intertw := fun x v => key B x v
      carrier := coe_Z' B Z
      cen := cen B Z
      gz := gz B Z
      scal := φ_scal B
      cr := cr B Z hZ
      mu := mu_Z' B Z
      roots := roots B Z
      nil := nil B Z hn }⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Pphi1
