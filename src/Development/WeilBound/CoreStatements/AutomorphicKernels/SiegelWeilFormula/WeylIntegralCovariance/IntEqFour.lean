module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.RpSmulLeft
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylTheta.TWeylOf
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntegralCovGen
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.TW.Twp

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open PositivityTheory.SiegelWeilFormula.TBij.Adp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem int_eq_four (d : SD σ) (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) (ε : ℤˣ) (f : Mx F E d.m d.n → ℂ)
    (Y : Matrix (Fin d.m) (Fin d.n) E) :
    ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z)) * f Z ∂ν =
      GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
        (fun q => algebraMap F (AF F) (Lm d ε (rc d Y) q)) := by
  rw [integral_cov d ν hν, GroundTheory.Automorphic.GJMatrix.adelicFourierPi]
  congr 1
  funext c
  rw [pair_eq d ε Y (d.cmb c), crd_cmb, GlobalTheory.AdelicSvN.Weyl.isStd_eq d.ok.good.std, mul_comm]

theorem poisson : Poisson := by
  intro F E _ _ _ _ _ σ d ν hν ε f hf
  have hg : (fun c => f (d.cmb c)) ∈ schA F (Ix d) := Submodule.mem_comap.1 hf
  have hθ := GlobalTheory.TowU.FourWeyl.theta_four hg
  refine (tsum_congr fun X => int_eq_four d ν hν ε f X).trans ?_
  refine ((rc d).toEquiv.tsum_eq (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
      (fun q => algebraMap F (AF F) (Lm d ε a q)))).trans ?_
  refine ((LinearEquiv.ofInjectiveEndo (Lm d ε) (Lm_inj d ε)).toEquiv.tsum_eq
      (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c)) (fun q => algebraMap F (AF F) (a q)))).trans ?_
  refine hθ.trans ?_
  show ∑' ξ : Ix d → F, f (d.cmb fun q => algebraMap F (AF F) (ξ q)) = _
  have e : ∀ X : Matrix (Fin d.m) (Fin d.n) E, f (incM F X) = f (d.cmb fun q => algebraMap F (AF F) (rc d X q)) := by
    intro X
    congr 1
    rw [← cmb_crd d (incM F X)]
    congr 1
    funext q
    rw [crd_incM]
    rfl
  simp_rw [e]
  exact ((rc d).toEquiv.tsum_eq (fun a => f (d.cmb fun q => algebraMap F (AF F) (a q)))).symm

end PositivityTheory.SiegelWeilFormula.TW.Twp

end
