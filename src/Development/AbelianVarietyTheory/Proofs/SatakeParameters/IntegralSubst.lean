module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

namespace GlobalTheory.CurveToStdLog

open MvPowerSeries

variable {l : ℕ} [Fact l.Prime] {κ κ' : Type}

theorem mvsubst_subst {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a) {b : MvPowerSeries κ ℂ_[l]}
    (hb : constantCoeff b = 0) (f : PowerSeries ℂ_[l]) :
    MvPowerSeries.subst a (f.subst b : MvPowerSeries κ ℂ_[l]) = f.subst (MvPowerSeries.subst a b) := by
  rw [PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hb).const ha]
  rfl

theorem subst_expMv [Finite κ] {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : ∀ i, constantCoeff (a i) = 0)
    {f : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) : subst a (expMv f) = expMv (subst a f) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, mvsubst_subst hs hf,
    GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]

theorem expMv_add {f g : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    expMv (f + g) = expMv f * expMv g := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg,
    GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg

theorem expMv_zero : expMv (0 : MvPowerSeries κ ℂ_[l]) = 1 := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero

theorem expMv_sum {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries κ ℂ_[l]}
    (hf : ∀ i, constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expMv_zero
  | insert i s hi ih =>

    rw [Finset.sum_insert hi, Finset.prod_insert hi, expMv_add (hf i) (by simp [map_sum, hf]), ih]

theorem cc_ph (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1) :
    PowerSeries.constantCoeff g.ph = 0 := by
  have h := (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).1
  show constantCoeff (-logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0
  rw [map_neg, h, neg_zero]

theorem cc_phAt (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) : constantCoeff (g.phAt y) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hy _ (cc_ph g hE)

theorem inv_ePhi1 (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) :
    (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = expMv (g.phAt y) := by
  have hs : HasSubst (fun _ : Unit => y) := hasSubst_of_constantCoeff_zero fun _ => hy
  have h := congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).2
  rw [subst_mul hs, subst_expMv (f := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) (cc_ph g hE), ← coe_substAlgHom hs (R := ℂ_[l]), map_one,
    coe_substAlgHom] at h
  have h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0 := by
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]; exact one_ne_zero
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one h1]
  exact h

end GlobalTheory.CurveToStdLog
