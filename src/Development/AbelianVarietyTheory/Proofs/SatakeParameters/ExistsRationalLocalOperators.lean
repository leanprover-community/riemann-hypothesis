module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Formalism.ConjugateSelfDual.Statement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastEqZeroOfDvdCard
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.FrobOps
open Polynomial

theorem not_dvd_normV {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) (w : HeightOneSpectrum (𝓞 E))
    (h : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  first
  | exact @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | (apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem ..)

theorem norm_le_one {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (m : ℤ) (q e : ℕ) (hq : ¬ l ∣ q) :
    ‖ι.symm ((m : ℂ) / (q : ℂ) ^ e)‖ ≤ 1 := by
  rw [map_div₀, map_pow, map_intCast, map_natCast, norm_div, norm_pow]
  have h1 : ‖((q : ℕ) : Qbar l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hq
  rw [h1, one_pow, div_one]
  exact IsUltrametricDist.norm_intCast_le_one _ m

theorem trace_pow_of_charpoly {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) (B : Multiset ℂ)
    (h : M.charpoly = (B.map fun b => X - C b).prod) (n : ℕ) : (M ^ n).trace = (B.map (· ^ n)).sum := by
  rw [Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, h, Polynomial.roots_multiset_prod_X_sub_C]

theorem iota_trc {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : Γ →* GL (Fin a) (Qbar l))
    (s : Γ) (n : ℕ) :
    ι (trc r (s ^ n)) = ((((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom) ^ n).trace := by

  rw [← Matrix.map_pow, trc, map_pow, Units.val_pow_eq_pow_val, Matrix.trace, Matrix.trace, map_sum]
  rfl

end GlobalTheory.FrobOps
