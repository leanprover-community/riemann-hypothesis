module

public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BeBessel
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BeConv
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingFromL2
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.DoubleCosetDecomposition
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.KFinFormOf
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.NormId
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.OOConv
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.QuadAOf
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.QuadBOf
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.VanishingOfL2Equivariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.DoubleCosetDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.IntegrableGNRpowOfLintegralLtTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFixM
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt.P

theorem decDD : DecDD := G.double_coset_decomposition
theorem beConv : BeConv := G.bessel_integral_convergence_of_growth growth_spherical_bound
theorem beBessel : BeBessel := PI.WBL.S5.G.beBessel_of growth_spherical_bound
theorem normIdSm : NormIdSm :=
  PI.WBL.NIS.G.normIdSm_of growth_spherical_bound growth_group_bound PI.WBL.NIS.measSideP
theorem kFinForm : KFinForm := kFinForm_of beConv beBessel
theorem zeroCase : ZeroCase := UnipotentHaarMeasurability.G.zeroCase_of beConv normIdSm schur_hermitian
theorem zeroCaseDD : ZeroCaseDD := UnipotentHaarMeasurability.G.zeroCaseDD_of beConv normIdSm schur_hermitian
theorem ooConv : OOConv :=
  S3dx4.G.ooConv_of schur_hermitian normIdSm norm_inverse_bound growth_group_bound decDD beConv
theorem quadConv : QuadConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe'
  exact ⟨fun γ hγ => S3dx4.G.quadA_of schur_hermitian normIdSm norm_inverse_bound growth_group_bound
      decDD beConv hIn D hS1 hS2 hbe hbe' hγ,
    S3dx4.G.quadB_of norm_inverse_bound growth_spherical_bound growth_group_bound decDD hIn D hS1 hbe⟩
theorem bessel_nonvanishing_L2 : BesselNonvanishingL2 :=
  MatrixMultiplicationContinuity.G.bessel_nonvanishing_from_L2 schur_hermitian norm_inverse_bound growth_spherical_bound
    growth_group_bound decDD beConv

end CompanionTheory.D.Upq.BesselFunctionalConstruction
