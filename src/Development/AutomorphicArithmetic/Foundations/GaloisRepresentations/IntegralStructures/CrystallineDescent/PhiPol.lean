module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOfPowerTraces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.phiPol_holds :
    PhiPol := by
  intro F Ω _ _ _ _ _ A w h x y σ hs
  have split : ∀ z : WD h, ((z.charPol σ).roots.map fun a => X - C a).prod = z.charPol σ := by
    intro z
    induction z using WD.ind with
    | hP n a =>
      rw [WD.charPol_mk]
      exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (LinearMap.charpoly_monic _)
        (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have hc : Multiset.card (x.charPol σ).roots = Multiset.card (y.charPol σ).roots := by
    have h0 := hs 0
    simp only [GlobalTheory.CongPhi.phiSum, pow_zero, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one] at h0
    exact_mod_cast h0
  rw [← split x, ← split y]
  exact GlobalTheory.CharpolyNewton.prod_eq_of_psum_eq _ _ hc hs
