module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ZeroDimSystem

def comb {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) : (Fin m → k) →ₛₗ[algebraMap k Γ(X, ⊤)] M.Sec :=
  ⟨⟨fun c => ∑ i, algebraMap k Γ(X, ⊤) (c i) • t i, fun a b => by
      simp [add_smul, Finset.sum_add_distrib]⟩, fun c a => by
      simp [mul_smul, Finset.smul_sum]⟩

theorem comb_apply {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) (c : Fin m → k) :
    comb t c = ∑ i, algebraMap k Γ(X, ⊤) (c i) • t i := rfl

def vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) (x : X) : Submodule k (Fin m → k) where
  carrier := {c | x ∉ nonzeroLocus (comb t c)}
  add_mem' := fun {a b} ha hb hx => by
    rw [map_add (f := _)] at hx
    exact (nonzeroLocus_add_le _ _ hx).elim ha hb
  zero_mem' := fun hx => by
    rw [map_zero] at hx
    exact nonzeroLocus_secZero.le hx
  smul_mem' := fun c a ha hx => by
    rw [(comb t).map_smulₛₗ] at hx
    exact ha ((nonzeroLocus_secScale _ _).le hx).2

theorem mem_vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X}
    {m : ℕ} (t : Fin m → M.Sec) (x : X) (c : Fin m → k) :
    c ∈ vanishAt t x ↔ x ∉ nonzeroLocus (comb t c) := Iff.rfl

theorem single_notMem_vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    {M : LB X} {m : ℕ} (t : Fin m → M.Sec) {x : X} {i : Fin m} (hx : x ∈ nonzeroLocus (t i)) :
    (Pi.single i 1 : Fin m → k) ∉ vanishAt t x := by
  classical
  rw [mem_vanishAt, not_not, comb_apply,
    Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, map_one,
    one_smul]
  exact hx

section Main

variable {k : Type} [Field k] [Infinite k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
  [AlgebraicGeometry.IsNoetherian X] {M : LB X} (hM : M.IsLB) {m : ℕ} (t : Fin m → M.Sec)
  (ht : ⨆ i, nonzeroLocus (t i) = ⊤)
  (hf : ∀ r, algebraMap k Γ(X, ⊤) r = (strHom k X).appTop ((Scheme.ΓSpecIso (.of k)).inv r))
  (hp : IsProjOver (strHom k (X := X)))
include hM ht hf hp

end Main

end GlobalTheory.ZeroDimSystem

namespace GlobalTheory

end GlobalTheory
