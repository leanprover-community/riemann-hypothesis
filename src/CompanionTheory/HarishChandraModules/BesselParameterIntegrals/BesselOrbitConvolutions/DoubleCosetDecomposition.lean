module

public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P
open Formalism.QuantumDeterminants

namespace G

theorem double_coset_decomposition : CompanionTheory.D.Upq.BesselFunctionalConstruction.DecDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS x hx y hy
  obtain ⟨hHC, hσ, hgap, hOK, hw0, -⟩ := hS
  have hσ' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ := hσ
  obtain ⟨P, hP, hw⟩ := hw0
  obtain ⟨C, hC⟩ := hIn.1 k r hOK.1 ε lam h H σ hHC hσ hgap hOK.2.1 P hP w0 w0 hw.2 hw.2
  have hD : Formalism.MainNotions.InverseNormDecayBounds.DiagonalMatrixCoefficientPowerDecay σ w0 (Formalism.FourierDecayAlt.ThreeDimData.aOf r h) := ⟨C, fun g hg => hC g hg⟩
  have hh : 0 ≤ h := le_trans (by positivity) hOK.2.1
  have ha : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := div_nonneg hh (by positivity)
  exact Formalism.MainNotions.InverseNormDecayBounds.decDD hσ' ha hD x hx y hy

end G

end Formalism.FourierDecayAlt.P

end
