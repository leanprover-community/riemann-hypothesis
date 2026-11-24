module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwpAlg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwSt
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwpMeas
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



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.Twp
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem int_eq_four_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) (ε : ℤˣ) (f : Mx F E d.m d.n → ℂ)
    (Y : Matrix (Fin d.m) (Fin d.n) E) :
    ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z)) * f Z ∂ν =
      GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
        (fun q => algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d Y) q)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.integral_cov_k d ν hν, GroundTheory.Automorphic.GJMatrix.adelicFourierPi]
  congr 1
  funext c
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.pair_eq_k d ε Y (d.cmb c), _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb, GlobalTheory.AdelicSvN.Weyl.isStd_eq d.ok.good.std, mul_comm]
theorem poisson_k : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k := by
  intro F E _ _ _ _ _ σ d ν hν ε f hf
  have hg : (fun c => f (d.cmb c)) ∈ schA F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := Submodule.mem_comap.1 hf
  have hθ := GlobalTheory.TowU.FourWeyl.theta_four hg
  refine (tsum_congr fun X => _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.int_eq_four_k d ν hν ε f X).trans ?_
  refine ((_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).toEquiv.tsum_eq (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
      (fun q => algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε a q)))).trans ?_
  refine ((LinearEquiv.ofInjectiveEndo (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_inj_k d ε)).toEquiv.tsum_eq
      (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c)) (fun q => algebraMap F (AF F) (a q)))).trans ?_
  refine hθ.trans ?_
  show ∑' ξ : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → F, f (d.cmb fun q => algebraMap F (AF F) (ξ q)) = _
  have e : ∀ X : Matrix (Fin d.m) (Fin d.n) E, f (incM F X) = f (d.cmb fun q => algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d X q)) := by
    intro X
    congr 1
    rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (incM F X)]
    congr 1
    funext q
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM]
    rfl
  simp_rw [e]
  exact ((_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).toEquiv.tsum_eq (fun a => f (d.cmb fun q => algebraMap F (AF F) (a q)))).symm
end PositivityTheory.SiegelWeilFormula.TW.Twp
end
end
