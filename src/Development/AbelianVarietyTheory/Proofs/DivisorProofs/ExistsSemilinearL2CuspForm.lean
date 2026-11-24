module

public import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdZeroOfPetAt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

noncomputable section
namespace GlobalTheory.CovTop.PetRep
open MeasureTheory

section Gen

open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

end Gen



theorem adelMeas_one_of_good {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelMeas Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hL := GlobalTheory.DictLocTest.locClause_of_unif_places hd (fun k hk => ((h.levelK k).1 hk).1)
    (GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)
  exact adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ)
    (GlobalTheory.PetDef.adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd
      (GlobalTheory.PetDef.muUnit_one Y h σ hσ) hL continuous_const)

end GlobalTheory.CovTop.PetRep
