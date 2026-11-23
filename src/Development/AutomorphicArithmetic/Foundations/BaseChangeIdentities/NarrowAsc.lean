module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.CuspDiscrete
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.UsedAsc
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
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

open PositivityTheory.Rg.Rs in
theorem UpperTheory.BaseChangeIdentities.ascComp : UpperTheory.BaseChangeIdentities.AscComp := by
  intro E _ _ _ N hN
  refine ⟨fun a π ha hn => ?_, fun V hV a d π hn e =>
    Re.Asc.hasSpehComp ascSeed_holds2.2 PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL hN hV hn e⟩
  subst ha
  exact ⟨π.V, PositivityTheory.RSHS.L1.cuspDiscrete E _ hN π (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn) hn,
    PDich.ascEmb_one (Setoid.refl π)⟩
