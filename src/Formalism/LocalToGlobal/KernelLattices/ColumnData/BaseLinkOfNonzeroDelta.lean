module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ProvisionExtensionLink
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ThIndep
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopIso

@[expose] public section

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem discrNe (D : Car) : DiscrNe D := by
  intro cc hcc
  obtain ⟨L, hL0⟩ := Formalism.L2.Ker.Cd.periodExists D cc 1 hcc one_ne_zero
  have hL : ∀ w : ℂ, w ∈ lamOf D cc 1 ↔ w ∈ L.lattice := fun w => by rw [← hL0]; rfl
  have h4 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 2 (by norm_num)
  have h6 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L hL 3 (by norm_num)
  have := Formalism.L2.Th1.F.discNeZero L
  unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
  rw [h4, h6]
  simpa [PeriodPair.g₂, PeriodPair.g₃] using this

def LinkDeltaNe : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0

def LinkQInt : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.QIntAll

theorem delta_nonzero_link : LinkDeltaNe := by
  intro D cc hcc δ hδ e
  apply discrNe D cc hcc.1
  rw [← (show δ ^ 12 = discr (lamOf D cc 1) from hδ), e]
  norm_num

theorem rational_integrality_link : LinkQInt := by
  intro D cc hcc δ hδ B N N' L L' hA x hx
  obtain ⟨a, b, hab, e⟩ := hermitian_form_integral_values D cc hcc δ hδ (delta_nonzero_link D cc hcc δ hδ) N N' L L' hA x hx x hx
  have hs := IO.sqrt_d_pos D
  have hreal : (Hf D (tor0 D cc δ) x x).im = 0 := by
    have h1 := IO.Hf_herm (tor0 D cc δ) x x
    have h2 := congrArg Complex.im h1
    rw [Complex.conj_im] at h2
    linarith
  have hb : b = 0 := by
    rw [e] at hreal
    simp at hreal
    exact hreal
  subst hb
  obtain ⟨j, hj⟩ := hab
  refine ⟨j, ?_⟩
  show Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = (j : ℝ)
  rw [e]
  have ha : (a : ℝ) = 2 * j := by
    have : a = 2 * j := by linarith
    exact_mod_cast this
  simp only [Int.cast_zero, zero_mul, add_zero, Complex.ofReal_re]
  rw [ha]
  field_simp

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
